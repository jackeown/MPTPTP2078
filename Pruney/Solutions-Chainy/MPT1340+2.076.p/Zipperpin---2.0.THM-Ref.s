%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rrV7VwXSC8

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:20 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  336 (8503 expanded)
%              Number of leaves         :   39 (2447 expanded)
%              Depth                    :   35
%              Number of atoms          : 3259 (181327 expanded)
%              Number of equality atoms :  159 (5137 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('0',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X5 ) )
        = X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t64_tops_2,conjecture,(
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
               => ( r2_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( k2_tops_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ C ) ) ) ) ) )).

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
                 => ( r2_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( k2_tops_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_tops_2])).

thf('3',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('11',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('17',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('18',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['15','20'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('22',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( v1_partfun1 @ X12 @ X13 )
      | ~ ( v1_funct_2 @ X12 @ X13 @ X14 )
      | ~ ( v1_funct_1 @ X12 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('23',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('26',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('31',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24','31'])).

thf('33',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('34',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('35',plain,(
    ! [X25: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','37'])).

thf('39',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['32','42'])).

thf('44',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['10','43'])).

thf('45',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('47',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_partfun1 @ X16 @ X15 )
      | ( ( k1_relat_1 @ X16 )
        = X15 )
      | ~ ( v4_relat_1 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('53',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('59',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('60',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','53','60'])).

thf('62',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['32','42'])).

thf('63',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_partfun1 @ X16 @ X15 )
      | ( ( k1_relat_1 @ X16 )
        = X15 )
      | ~ ( v4_relat_1 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('64',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('68',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','68'])).

thf('70',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','68'])).

thf('71',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('72',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['9','61','69','70','71'])).

thf('73',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('75',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','53','60'])).

thf('81',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

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

thf('82',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X26 @ X28 )
       != X26 )
      | ~ ( v2_funct_1 @ X28 )
      | ( ( k2_tops_2 @ X27 @ X26 @ X28 )
        = ( k2_funct_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('83',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('86',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('87',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['85','90'])).

thf('92',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('95',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','53','60'])).

thf('97',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('100',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('101',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['99','104'])).

thf('106',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('109',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('110',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','53','60'])).

thf('112',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['83','84','97','98','112'])).

thf('114',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['72','114'])).

thf('116',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('117',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('118',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','53','60'])).

thf('119',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf(t31_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf('120',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X21 )
       != X22 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('121',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('124',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','53','60'])).

thf('125',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('127',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('128',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','53','60'])).

thf('130',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['121','122','125','130','131'])).

thf('133',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['116','132'])).

thf('134',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('135',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['133','134','135'])).

thf('137',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X26 @ X28 )
       != X26 )
      | ~ ( v2_funct_1 @ X28 )
      | ( ( k2_tops_2 @ X27 @ X26 @ X28 )
        = ( k2_funct_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('139',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('141',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('142',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X21 )
       != X22 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('143',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('146',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('147',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['143','144','145','146','147'])).

thf('149',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['140','148'])).

thf('150',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('151',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['149','150','151'])).

thf('153',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('155',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('156',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X21 )
       != X22 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X21 ) @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('157',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('160',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('161',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['157','158','159','160','161'])).

thf('163',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['154','162'])).

thf('164',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('165',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['163','164','165'])).

thf('167',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['139','153','167'])).

thf('169',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('170',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('171',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['168','171'])).

thf('173',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('174',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','53','60'])).

thf('175',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('176',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('177',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t63_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v2_funct_1 @ C ) )
               => ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) )).

thf('178',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( l1_struct_0 @ X29 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X29 ) @ X31 )
       != ( k2_struct_0 @ X29 ) )
      | ~ ( v2_funct_1 @ X31 )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X29 ) @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X29 ) ) ) )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X29 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t63_tops_2])).

thf('179',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) @ X2 ) )
      | ~ ( v2_funct_1 @ X2 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) @ X2 )
       != ( k2_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_struct_0 @ X1 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) @ X2 )
       != ( k2_struct_0 @ X1 ) )
      | ~ ( v2_funct_1 @ X2 )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) @ X2 ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ X1 ) @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ X2 ) )
      | ~ ( v2_funct_1 @ X2 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ X2 )
       != ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['176','180'])).

thf('182',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relset_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ X2 )
       != ( k2_struct_0 @ X0 ) )
      | ~ ( v2_funct_1 @ X2 )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ X2 ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ X1 ) @ ( k2_struct_0 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['181'])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ X0 ) @ ( k2_relat_1 @ sk_C ) ) ) )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 )
       != ( k2_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['175','182'])).

thf('184',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('186',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ X0 ) @ ( k2_relat_1 @ sk_C ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 )
       != ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['183','184','185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X0 )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X0 ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['174','186'])).

thf('188',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','68'])).

thf('189',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','68'])).

thf('190',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','68'])).

thf('191',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ X0 )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ X0 ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['187','188','189','190','191'])).

thf('193',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['173','192'])).

thf('194',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('196',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('197',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('198',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X26 @ X28 )
       != X26 )
      | ~ ( v2_funct_1 @ X28 )
      | ( ( k2_tops_2 @ X27 @ X26 @ X28 )
        = ( k2_funct_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('199',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('202',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('204',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['199','200','201','202','203'])).

thf('205',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['196','204'])).

thf('206',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('207',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['205','206','207'])).

thf('209',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['208'])).

thf('210',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('212',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['193','194','195','209','210','211'])).

thf('213',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['212'])).

thf('214',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['172','213'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('215',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('216',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('217',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X5 ) )
        = X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('218',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['212'])).

thf('219',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X5 ) )
        = X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('220',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('221',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X5 ) )
        = X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('222',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('223',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k1_relat_1 @ X16 )
       != X15 )
      | ( v1_partfun1 @ X16 @ X15 )
      | ~ ( v4_relat_1 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('224',plain,(
    ! [X16: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v4_relat_1 @ X16 @ ( k1_relat_1 @ X16 ) )
      | ( v1_partfun1 @ X16 @ ( k1_relat_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['223'])).

thf('225',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['222','224'])).

thf('226',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['221','225'])).

thf('227',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['220','226'])).

thf('228',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['227'])).

thf('229',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['219','228'])).

thf('230',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['229'])).

thf('231',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['218','230'])).

thf('232',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('233',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('236',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','53','60'])).

thf('237',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['235','236'])).

thf('238',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('239',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X21 )
       != X22 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('240',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['238','239'])).

thf('241',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('243',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('244',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['240','241','242','243','244'])).

thf('246',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['245'])).

thf('247',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('248',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['246','247'])).

thf('249',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('250',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['248','249'])).

thf('251',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['152'])).

thf('252',plain,(
    v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['231','232','233','234','237','250','251'])).

thf('253',plain,
    ( ( v1_partfun1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['217','252'])).

thf('254',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('255',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,(
    v1_partfun1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['253','254','255','256'])).

thf('258',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['216','257'])).

thf('259',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['248','249'])).

thf('260',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['152'])).

thf('261',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['212'])).

thf('262',plain,(
    v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['258','259','260','261'])).

thf('263',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_partfun1 @ X16 @ X15 )
      | ( ( k1_relat_1 @ X16 )
        = X15 )
      | ~ ( v4_relat_1 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('264',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['262','263'])).

thf('265',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('266',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['264','265'])).

thf('267',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['215','266'])).

thf('268',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['235','236'])).

thf('269',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('270',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('271',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('272',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['267','268','269','270','271'])).

thf('273',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['214','272'])).

thf('274',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['273'])).

thf('275',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['115','274'])).

thf('276',plain,
    ( ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','275'])).

thf('277',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('278',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_funct_2 @ A @ B @ C @ C ) ) )).

thf('279',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_funct_2 @ X17 @ X18 @ X19 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( v1_funct_2 @ X19 @ X17 @ X18 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_2 @ X20 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('280',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['278','279'])).

thf('281',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('282',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('283',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['280','281','282'])).

thf('284',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','68'])).

thf('285',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','68'])).

thf('286',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','68'])).

thf('287',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['283','284','285','286'])).

thf('288',plain,
    ( ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['277','287'])).

thf('289',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('290',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('291',plain,(
    r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['288','289','290'])).

thf('292',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('293',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('294',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('295',plain,(
    $false ),
    inference(demod,[status(thm)],['276','291','292','293','294'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rrV7VwXSC8
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:15:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.51/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.51/0.69  % Solved by: fo/fo7.sh
% 0.51/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.69  % done 422 iterations in 0.230s
% 0.51/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.51/0.69  % SZS output start Refutation
% 0.51/0.69  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.51/0.69  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.51/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.51/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.51/0.69  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.51/0.69  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.51/0.69  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.51/0.69  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.51/0.69  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.51/0.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.51/0.69  thf(sk_C_type, type, sk_C: $i).
% 0.51/0.69  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.51/0.69  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.51/0.69  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.51/0.69  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.51/0.69  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.51/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.51/0.69  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.51/0.69  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.51/0.69  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.51/0.69  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.51/0.69  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.51/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.69  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.51/0.69  thf(t65_funct_1, axiom,
% 0.51/0.69    (![A:$i]:
% 0.51/0.69     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.51/0.69       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.51/0.69  thf('0', plain,
% 0.51/0.69      (![X5 : $i]:
% 0.51/0.69         (~ (v2_funct_1 @ X5)
% 0.51/0.69          | ((k2_funct_1 @ (k2_funct_1 @ X5)) = (X5))
% 0.51/0.69          | ~ (v1_funct_1 @ X5)
% 0.51/0.69          | ~ (v1_relat_1 @ X5))),
% 0.51/0.69      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.51/0.69  thf(d3_struct_0, axiom,
% 0.51/0.69    (![A:$i]:
% 0.51/0.69     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.51/0.69  thf('1', plain,
% 0.51/0.69      (![X24 : $i]:
% 0.51/0.69         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.51/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.51/0.69  thf('2', plain,
% 0.51/0.69      (![X24 : $i]:
% 0.51/0.69         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.51/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.51/0.69  thf(t64_tops_2, conjecture,
% 0.51/0.69    (![A:$i]:
% 0.51/0.69     ( ( l1_struct_0 @ A ) =>
% 0.51/0.69       ( ![B:$i]:
% 0.51/0.69         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.51/0.69           ( ![C:$i]:
% 0.51/0.69             ( ( ( v1_funct_1 @ C ) & 
% 0.51/0.69                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.51/0.69                 ( m1_subset_1 @
% 0.51/0.69                   C @ 
% 0.51/0.69                   ( k1_zfmisc_1 @
% 0.51/0.69                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.51/0.69               ( ( ( ( k2_relset_1 @
% 0.51/0.69                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.51/0.69                     ( k2_struct_0 @ B ) ) & 
% 0.51/0.69                   ( v2_funct_1 @ C ) ) =>
% 0.51/0.69                 ( r2_funct_2 @
% 0.51/0.69                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.51/0.69                   ( k2_tops_2 @
% 0.51/0.69                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.51/0.69                     ( k2_tops_2 @
% 0.51/0.69                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.51/0.69                   C ) ) ) ) ) ) ))).
% 0.51/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.69    (~( ![A:$i]:
% 0.51/0.69        ( ( l1_struct_0 @ A ) =>
% 0.51/0.69          ( ![B:$i]:
% 0.51/0.69            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.51/0.69              ( ![C:$i]:
% 0.51/0.69                ( ( ( v1_funct_1 @ C ) & 
% 0.51/0.69                    ( v1_funct_2 @
% 0.51/0.69                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.51/0.69                    ( m1_subset_1 @
% 0.51/0.69                      C @ 
% 0.51/0.69                      ( k1_zfmisc_1 @
% 0.51/0.69                        ( k2_zfmisc_1 @
% 0.51/0.69                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.51/0.69                  ( ( ( ( k2_relset_1 @
% 0.51/0.69                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.51/0.69                        ( k2_struct_0 @ B ) ) & 
% 0.51/0.69                      ( v2_funct_1 @ C ) ) =>
% 0.51/0.69                    ( r2_funct_2 @
% 0.51/0.69                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.51/0.69                      ( k2_tops_2 @
% 0.51/0.69                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.51/0.69                        ( k2_tops_2 @
% 0.51/0.69                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.51/0.69                      C ) ) ) ) ) ) ) )),
% 0.51/0.69    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.51/0.69  thf('3', plain,
% 0.51/0.69      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.51/0.69          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.51/0.69           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.51/0.69          sk_C)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('4', plain,
% 0.51/0.69      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.51/0.69           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.51/0.69            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.51/0.69           sk_C)
% 0.51/0.69        | ~ (l1_struct_0 @ sk_A))),
% 0.51/0.69      inference('sup-', [status(thm)], ['2', '3'])).
% 0.51/0.69  thf('5', plain, ((l1_struct_0 @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('6', plain,
% 0.51/0.69      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.51/0.69          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.51/0.69           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.51/0.69          sk_C)),
% 0.51/0.69      inference('demod', [status(thm)], ['4', '5'])).
% 0.51/0.69  thf('7', plain,
% 0.51/0.69      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.51/0.69           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.51/0.69            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.51/0.69           sk_C)
% 0.51/0.69        | ~ (l1_struct_0 @ sk_B))),
% 0.51/0.69      inference('sup-', [status(thm)], ['1', '6'])).
% 0.51/0.69  thf('8', plain, ((l1_struct_0 @ sk_B)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('9', plain,
% 0.51/0.69      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.51/0.69          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.51/0.69           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.51/0.69          sk_C)),
% 0.51/0.69      inference('demod', [status(thm)], ['7', '8'])).
% 0.51/0.69  thf('10', plain,
% 0.51/0.69      (![X24 : $i]:
% 0.51/0.69         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.51/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.51/0.69  thf('11', plain,
% 0.51/0.69      (![X24 : $i]:
% 0.51/0.69         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.51/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.51/0.69  thf('12', plain,
% 0.51/0.69      ((m1_subset_1 @ sk_C @ 
% 0.51/0.69        (k1_zfmisc_1 @ 
% 0.51/0.69         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('13', plain,
% 0.51/0.69      (((m1_subset_1 @ sk_C @ 
% 0.51/0.69         (k1_zfmisc_1 @ 
% 0.51/0.69          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.51/0.69        | ~ (l1_struct_0 @ sk_B))),
% 0.51/0.69      inference('sup+', [status(thm)], ['11', '12'])).
% 0.51/0.69  thf('14', plain, ((l1_struct_0 @ sk_B)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('15', plain,
% 0.51/0.69      ((m1_subset_1 @ sk_C @ 
% 0.51/0.69        (k1_zfmisc_1 @ 
% 0.51/0.69         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.51/0.69      inference('demod', [status(thm)], ['13', '14'])).
% 0.51/0.69  thf('16', plain,
% 0.51/0.69      ((m1_subset_1 @ sk_C @ 
% 0.51/0.69        (k1_zfmisc_1 @ 
% 0.51/0.69         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf(redefinition_k2_relset_1, axiom,
% 0.51/0.69    (![A:$i,B:$i,C:$i]:
% 0.51/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.69       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.51/0.69  thf('17', plain,
% 0.51/0.69      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.51/0.69         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 0.51/0.69          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.51/0.69      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.51/0.69  thf('18', plain,
% 0.51/0.69      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.51/0.69         = (k2_relat_1 @ sk_C))),
% 0.51/0.69      inference('sup-', [status(thm)], ['16', '17'])).
% 0.51/0.69  thf('19', plain,
% 0.51/0.69      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.51/0.69         = (k2_struct_0 @ sk_B))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('20', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.51/0.69      inference('sup+', [status(thm)], ['18', '19'])).
% 0.51/0.69  thf('21', plain,
% 0.51/0.69      ((m1_subset_1 @ sk_C @ 
% 0.51/0.69        (k1_zfmisc_1 @ 
% 0.51/0.69         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.51/0.69      inference('demod', [status(thm)], ['15', '20'])).
% 0.51/0.69  thf(cc5_funct_2, axiom,
% 0.51/0.69    (![A:$i,B:$i]:
% 0.51/0.69     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.51/0.69       ( ![C:$i]:
% 0.51/0.69         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.69           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.51/0.69             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.51/0.69  thf('22', plain,
% 0.51/0.69      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.51/0.69         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.51/0.69          | (v1_partfun1 @ X12 @ X13)
% 0.51/0.69          | ~ (v1_funct_2 @ X12 @ X13 @ X14)
% 0.51/0.69          | ~ (v1_funct_1 @ X12)
% 0.51/0.69          | (v1_xboole_0 @ X14))),
% 0.51/0.69      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.51/0.69  thf('23', plain,
% 0.51/0.69      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.51/0.69        | ~ (v1_funct_1 @ sk_C)
% 0.51/0.69        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.51/0.69        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['21', '22'])).
% 0.51/0.69  thf('24', plain, ((v1_funct_1 @ sk_C)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('25', plain,
% 0.51/0.69      (![X24 : $i]:
% 0.51/0.69         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.51/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.51/0.69  thf('26', plain,
% 0.51/0.69      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('27', plain,
% 0.51/0.69      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.51/0.69        | ~ (l1_struct_0 @ sk_B))),
% 0.51/0.69      inference('sup+', [status(thm)], ['25', '26'])).
% 0.51/0.69  thf('28', plain, ((l1_struct_0 @ sk_B)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('29', plain,
% 0.51/0.69      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.51/0.69      inference('demod', [status(thm)], ['27', '28'])).
% 0.51/0.69  thf('30', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.51/0.69      inference('sup+', [status(thm)], ['18', '19'])).
% 0.51/0.69  thf('31', plain,
% 0.51/0.69      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.51/0.69      inference('demod', [status(thm)], ['29', '30'])).
% 0.51/0.69  thf('32', plain,
% 0.51/0.69      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.51/0.69        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.51/0.69      inference('demod', [status(thm)], ['23', '24', '31'])).
% 0.51/0.69  thf('33', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.51/0.69      inference('sup+', [status(thm)], ['18', '19'])).
% 0.51/0.69  thf('34', plain,
% 0.51/0.69      (![X24 : $i]:
% 0.51/0.69         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.51/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.51/0.69  thf(fc2_struct_0, axiom,
% 0.51/0.69    (![A:$i]:
% 0.51/0.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.51/0.69       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.51/0.69  thf('35', plain,
% 0.51/0.69      (![X25 : $i]:
% 0.51/0.69         (~ (v1_xboole_0 @ (u1_struct_0 @ X25))
% 0.51/0.69          | ~ (l1_struct_0 @ X25)
% 0.51/0.69          | (v2_struct_0 @ X25))),
% 0.51/0.69      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.51/0.69  thf('36', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.51/0.69          | ~ (l1_struct_0 @ X0)
% 0.51/0.69          | (v2_struct_0 @ X0)
% 0.51/0.69          | ~ (l1_struct_0 @ X0))),
% 0.51/0.69      inference('sup-', [status(thm)], ['34', '35'])).
% 0.51/0.69  thf('37', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         ((v2_struct_0 @ X0)
% 0.51/0.69          | ~ (l1_struct_0 @ X0)
% 0.51/0.69          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.51/0.69      inference('simplify', [status(thm)], ['36'])).
% 0.51/0.69  thf('38', plain,
% 0.51/0.69      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.51/0.69        | ~ (l1_struct_0 @ sk_B)
% 0.51/0.69        | (v2_struct_0 @ sk_B))),
% 0.51/0.69      inference('sup-', [status(thm)], ['33', '37'])).
% 0.51/0.69  thf('39', plain, ((l1_struct_0 @ sk_B)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('40', plain,
% 0.51/0.69      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.51/0.69      inference('demod', [status(thm)], ['38', '39'])).
% 0.51/0.69  thf('41', plain, (~ (v2_struct_0 @ sk_B)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('42', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.51/0.69      inference('clc', [status(thm)], ['40', '41'])).
% 0.51/0.69  thf('43', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.51/0.69      inference('clc', [status(thm)], ['32', '42'])).
% 0.51/0.69  thf('44', plain,
% 0.51/0.69      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.51/0.69      inference('sup+', [status(thm)], ['10', '43'])).
% 0.51/0.69  thf('45', plain, ((l1_struct_0 @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('46', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.51/0.69      inference('demod', [status(thm)], ['44', '45'])).
% 0.51/0.69  thf(d4_partfun1, axiom,
% 0.51/0.69    (![A:$i,B:$i]:
% 0.51/0.69     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.51/0.69       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.51/0.69  thf('47', plain,
% 0.51/0.69      (![X15 : $i, X16 : $i]:
% 0.51/0.69         (~ (v1_partfun1 @ X16 @ X15)
% 0.51/0.69          | ((k1_relat_1 @ X16) = (X15))
% 0.51/0.69          | ~ (v4_relat_1 @ X16 @ X15)
% 0.51/0.69          | ~ (v1_relat_1 @ X16))),
% 0.51/0.69      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.51/0.69  thf('48', plain,
% 0.51/0.69      ((~ (v1_relat_1 @ sk_C)
% 0.51/0.69        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.51/0.69        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['46', '47'])).
% 0.51/0.69  thf('49', plain,
% 0.51/0.69      ((m1_subset_1 @ sk_C @ 
% 0.51/0.69        (k1_zfmisc_1 @ 
% 0.51/0.69         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf(cc2_relat_1, axiom,
% 0.51/0.69    (![A:$i]:
% 0.51/0.69     ( ( v1_relat_1 @ A ) =>
% 0.51/0.69       ( ![B:$i]:
% 0.51/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.51/0.69  thf('50', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.51/0.69          | (v1_relat_1 @ X0)
% 0.51/0.69          | ~ (v1_relat_1 @ X1))),
% 0.51/0.69      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.51/0.69  thf('51', plain,
% 0.51/0.69      ((~ (v1_relat_1 @ 
% 0.51/0.69           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.51/0.69        | (v1_relat_1 @ sk_C))),
% 0.51/0.69      inference('sup-', [status(thm)], ['49', '50'])).
% 0.51/0.69  thf(fc6_relat_1, axiom,
% 0.51/0.69    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.51/0.69  thf('52', plain,
% 0.51/0.69      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.51/0.69      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.51/0.69  thf('53', plain, ((v1_relat_1 @ sk_C)),
% 0.51/0.69      inference('demod', [status(thm)], ['51', '52'])).
% 0.51/0.69  thf('54', plain,
% 0.51/0.69      (![X24 : $i]:
% 0.51/0.69         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.51/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.51/0.69  thf('55', plain,
% 0.51/0.69      ((m1_subset_1 @ sk_C @ 
% 0.51/0.69        (k1_zfmisc_1 @ 
% 0.51/0.69         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('56', plain,
% 0.51/0.69      (((m1_subset_1 @ sk_C @ 
% 0.51/0.69         (k1_zfmisc_1 @ 
% 0.51/0.69          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.51/0.69        | ~ (l1_struct_0 @ sk_A))),
% 0.51/0.69      inference('sup+', [status(thm)], ['54', '55'])).
% 0.51/0.69  thf('57', plain, ((l1_struct_0 @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('58', plain,
% 0.51/0.69      ((m1_subset_1 @ sk_C @ 
% 0.51/0.69        (k1_zfmisc_1 @ 
% 0.51/0.69         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.51/0.69      inference('demod', [status(thm)], ['56', '57'])).
% 0.51/0.69  thf(cc2_relset_1, axiom,
% 0.51/0.69    (![A:$i,B:$i,C:$i]:
% 0.51/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.69       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.51/0.69  thf('59', plain,
% 0.51/0.69      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.51/0.69         ((v4_relat_1 @ X6 @ X7)
% 0.51/0.69          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.51/0.69      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.51/0.69  thf('60', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.51/0.69      inference('sup-', [status(thm)], ['58', '59'])).
% 0.51/0.69  thf('61', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.51/0.69      inference('demod', [status(thm)], ['48', '53', '60'])).
% 0.51/0.69  thf('62', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.51/0.69      inference('clc', [status(thm)], ['32', '42'])).
% 0.51/0.69  thf('63', plain,
% 0.51/0.69      (![X15 : $i, X16 : $i]:
% 0.51/0.69         (~ (v1_partfun1 @ X16 @ X15)
% 0.51/0.69          | ((k1_relat_1 @ X16) = (X15))
% 0.51/0.69          | ~ (v4_relat_1 @ X16 @ X15)
% 0.51/0.69          | ~ (v1_relat_1 @ X16))),
% 0.51/0.69      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.51/0.69  thf('64', plain,
% 0.51/0.69      ((~ (v1_relat_1 @ sk_C)
% 0.51/0.69        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.51/0.69        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['62', '63'])).
% 0.51/0.69  thf('65', plain, ((v1_relat_1 @ sk_C)),
% 0.51/0.69      inference('demod', [status(thm)], ['51', '52'])).
% 0.51/0.69  thf('66', plain,
% 0.51/0.69      ((m1_subset_1 @ sk_C @ 
% 0.51/0.69        (k1_zfmisc_1 @ 
% 0.51/0.69         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('67', plain,
% 0.51/0.69      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.51/0.69         ((v4_relat_1 @ X6 @ X7)
% 0.51/0.69          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.51/0.69      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.51/0.69  thf('68', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.51/0.69      inference('sup-', [status(thm)], ['66', '67'])).
% 0.51/0.69  thf('69', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.51/0.69      inference('demod', [status(thm)], ['64', '65', '68'])).
% 0.51/0.69  thf('70', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.51/0.69      inference('demod', [status(thm)], ['64', '65', '68'])).
% 0.51/0.69  thf('71', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.51/0.69      inference('sup+', [status(thm)], ['18', '19'])).
% 0.51/0.69  thf('72', plain,
% 0.51/0.69      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.51/0.69          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.51/0.69           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)) @ 
% 0.51/0.69          sk_C)),
% 0.51/0.69      inference('demod', [status(thm)], ['9', '61', '69', '70', '71'])).
% 0.51/0.69  thf('73', plain,
% 0.51/0.69      (![X24 : $i]:
% 0.51/0.69         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.51/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.51/0.69  thf('74', plain,
% 0.51/0.69      ((m1_subset_1 @ sk_C @ 
% 0.51/0.69        (k1_zfmisc_1 @ 
% 0.51/0.69         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.51/0.69      inference('demod', [status(thm)], ['56', '57'])).
% 0.51/0.69  thf('75', plain,
% 0.51/0.69      (((m1_subset_1 @ sk_C @ 
% 0.51/0.69         (k1_zfmisc_1 @ 
% 0.51/0.69          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.51/0.69        | ~ (l1_struct_0 @ sk_B))),
% 0.51/0.69      inference('sup+', [status(thm)], ['73', '74'])).
% 0.51/0.69  thf('76', plain, ((l1_struct_0 @ sk_B)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('77', plain,
% 0.51/0.69      ((m1_subset_1 @ sk_C @ 
% 0.51/0.69        (k1_zfmisc_1 @ 
% 0.51/0.69         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.51/0.69      inference('demod', [status(thm)], ['75', '76'])).
% 0.51/0.69  thf('78', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.51/0.69      inference('sup+', [status(thm)], ['18', '19'])).
% 0.51/0.69  thf('79', plain,
% 0.51/0.69      ((m1_subset_1 @ sk_C @ 
% 0.51/0.69        (k1_zfmisc_1 @ 
% 0.51/0.69         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.51/0.69      inference('demod', [status(thm)], ['77', '78'])).
% 0.51/0.69  thf('80', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.51/0.69      inference('demod', [status(thm)], ['48', '53', '60'])).
% 0.51/0.69  thf('81', plain,
% 0.51/0.69      ((m1_subset_1 @ sk_C @ 
% 0.51/0.69        (k1_zfmisc_1 @ 
% 0.51/0.69         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.51/0.69      inference('demod', [status(thm)], ['79', '80'])).
% 0.51/0.69  thf(d4_tops_2, axiom,
% 0.51/0.69    (![A:$i,B:$i,C:$i]:
% 0.51/0.69     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.51/0.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.51/0.69       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.51/0.69         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.51/0.69  thf('82', plain,
% 0.51/0.69      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.51/0.69         (((k2_relset_1 @ X27 @ X26 @ X28) != (X26))
% 0.51/0.69          | ~ (v2_funct_1 @ X28)
% 0.51/0.69          | ((k2_tops_2 @ X27 @ X26 @ X28) = (k2_funct_1 @ X28))
% 0.51/0.69          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 0.51/0.69          | ~ (v1_funct_2 @ X28 @ X27 @ X26)
% 0.51/0.69          | ~ (v1_funct_1 @ X28))),
% 0.51/0.69      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.51/0.69  thf('83', plain,
% 0.51/0.69      ((~ (v1_funct_1 @ sk_C)
% 0.51/0.69        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.51/0.69        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.51/0.69            = (k2_funct_1 @ sk_C))
% 0.51/0.69        | ~ (v2_funct_1 @ sk_C)
% 0.51/0.69        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.51/0.69            != (k2_relat_1 @ sk_C)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['81', '82'])).
% 0.51/0.69  thf('84', plain, ((v1_funct_1 @ sk_C)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('85', plain,
% 0.51/0.69      (![X24 : $i]:
% 0.51/0.69         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.51/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.51/0.69  thf('86', plain,
% 0.51/0.69      (![X24 : $i]:
% 0.51/0.69         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.51/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.51/0.69  thf('87', plain,
% 0.51/0.69      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('88', plain,
% 0.51/0.69      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.51/0.69        | ~ (l1_struct_0 @ sk_A))),
% 0.51/0.69      inference('sup+', [status(thm)], ['86', '87'])).
% 0.51/0.69  thf('89', plain, ((l1_struct_0 @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('90', plain,
% 0.51/0.69      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.51/0.69      inference('demod', [status(thm)], ['88', '89'])).
% 0.51/0.69  thf('91', plain,
% 0.51/0.69      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.51/0.69        | ~ (l1_struct_0 @ sk_B))),
% 0.51/0.69      inference('sup+', [status(thm)], ['85', '90'])).
% 0.51/0.69  thf('92', plain, ((l1_struct_0 @ sk_B)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('93', plain,
% 0.51/0.69      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.51/0.69      inference('demod', [status(thm)], ['91', '92'])).
% 0.51/0.69  thf('94', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.51/0.69      inference('sup+', [status(thm)], ['18', '19'])).
% 0.51/0.69  thf('95', plain,
% 0.51/0.69      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.51/0.69      inference('demod', [status(thm)], ['93', '94'])).
% 0.51/0.69  thf('96', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.51/0.69      inference('demod', [status(thm)], ['48', '53', '60'])).
% 0.51/0.69  thf('97', plain,
% 0.51/0.69      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.51/0.69      inference('demod', [status(thm)], ['95', '96'])).
% 0.51/0.69  thf('98', plain, ((v2_funct_1 @ sk_C)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('99', plain,
% 0.51/0.69      (![X24 : $i]:
% 0.51/0.69         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.51/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.51/0.69  thf('100', plain,
% 0.51/0.69      (![X24 : $i]:
% 0.51/0.69         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.51/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.51/0.69  thf('101', plain,
% 0.51/0.69      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.51/0.69         = (k2_struct_0 @ sk_B))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('102', plain,
% 0.51/0.69      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.51/0.69          = (k2_struct_0 @ sk_B))
% 0.51/0.69        | ~ (l1_struct_0 @ sk_A))),
% 0.51/0.69      inference('sup+', [status(thm)], ['100', '101'])).
% 0.51/0.69  thf('103', plain, ((l1_struct_0 @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('104', plain,
% 0.51/0.69      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.51/0.69         = (k2_struct_0 @ sk_B))),
% 0.51/0.69      inference('demod', [status(thm)], ['102', '103'])).
% 0.51/0.69  thf('105', plain,
% 0.51/0.69      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.51/0.69          = (k2_struct_0 @ sk_B))
% 0.51/0.69        | ~ (l1_struct_0 @ sk_B))),
% 0.51/0.69      inference('sup+', [status(thm)], ['99', '104'])).
% 0.51/0.69  thf('106', plain, ((l1_struct_0 @ sk_B)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('107', plain,
% 0.51/0.69      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.51/0.69         = (k2_struct_0 @ sk_B))),
% 0.51/0.69      inference('demod', [status(thm)], ['105', '106'])).
% 0.51/0.69  thf('108', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.51/0.69      inference('sup+', [status(thm)], ['18', '19'])).
% 0.51/0.69  thf('109', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.51/0.69      inference('sup+', [status(thm)], ['18', '19'])).
% 0.51/0.69  thf('110', plain,
% 0.51/0.69      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.51/0.69         = (k2_relat_1 @ sk_C))),
% 0.51/0.69      inference('demod', [status(thm)], ['107', '108', '109'])).
% 0.51/0.69  thf('111', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.51/0.69      inference('demod', [status(thm)], ['48', '53', '60'])).
% 0.51/0.69  thf('112', plain,
% 0.51/0.69      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.51/0.69         = (k2_relat_1 @ sk_C))),
% 0.51/0.69      inference('demod', [status(thm)], ['110', '111'])).
% 0.51/0.69  thf('113', plain,
% 0.51/0.69      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.51/0.69          = (k2_funct_1 @ sk_C))
% 0.51/0.69        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.51/0.69      inference('demod', [status(thm)], ['83', '84', '97', '98', '112'])).
% 0.51/0.69  thf('114', plain,
% 0.51/0.69      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.51/0.69         = (k2_funct_1 @ sk_C))),
% 0.51/0.69      inference('simplify', [status(thm)], ['113'])).
% 0.51/0.69  thf('115', plain,
% 0.51/0.69      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.51/0.69          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.51/0.69           (k2_funct_1 @ sk_C)) @ 
% 0.51/0.69          sk_C)),
% 0.51/0.69      inference('demod', [status(thm)], ['72', '114'])).
% 0.51/0.69  thf('116', plain,
% 0.51/0.69      (![X24 : $i]:
% 0.51/0.69         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.51/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.51/0.69  thf('117', plain,
% 0.51/0.69      ((m1_subset_1 @ sk_C @ 
% 0.51/0.69        (k1_zfmisc_1 @ 
% 0.51/0.69         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.51/0.69      inference('demod', [status(thm)], ['56', '57'])).
% 0.51/0.69  thf('118', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.51/0.69      inference('demod', [status(thm)], ['48', '53', '60'])).
% 0.51/0.69  thf('119', plain,
% 0.51/0.69      ((m1_subset_1 @ sk_C @ 
% 0.51/0.69        (k1_zfmisc_1 @ 
% 0.51/0.69         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.51/0.69      inference('demod', [status(thm)], ['117', '118'])).
% 0.51/0.69  thf(t31_funct_2, axiom,
% 0.51/0.69    (![A:$i,B:$i,C:$i]:
% 0.51/0.69     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.51/0.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.51/0.69       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.51/0.69         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.51/0.69           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.51/0.69           ( m1_subset_1 @
% 0.51/0.69             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.51/0.69  thf('120', plain,
% 0.51/0.69      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.51/0.69         (~ (v2_funct_1 @ X21)
% 0.51/0.69          | ((k2_relset_1 @ X23 @ X22 @ X21) != (X22))
% 0.51/0.69          | (m1_subset_1 @ (k2_funct_1 @ X21) @ 
% 0.51/0.69             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.51/0.69          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.51/0.69          | ~ (v1_funct_2 @ X21 @ X23 @ X22)
% 0.51/0.69          | ~ (v1_funct_1 @ X21))),
% 0.51/0.69      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.51/0.69  thf('121', plain,
% 0.51/0.69      ((~ (v1_funct_1 @ sk_C)
% 0.51/0.69        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.51/0.69        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.51/0.69           (k1_zfmisc_1 @ 
% 0.51/0.69            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 0.51/0.69        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.51/0.69            != (u1_struct_0 @ sk_B))
% 0.51/0.69        | ~ (v2_funct_1 @ sk_C))),
% 0.51/0.69      inference('sup-', [status(thm)], ['119', '120'])).
% 0.51/0.69  thf('122', plain, ((v1_funct_1 @ sk_C)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('123', plain,
% 0.51/0.69      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.51/0.69      inference('demod', [status(thm)], ['88', '89'])).
% 0.51/0.69  thf('124', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.51/0.69      inference('demod', [status(thm)], ['48', '53', '60'])).
% 0.51/0.69  thf('125', plain,
% 0.51/0.69      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.51/0.69      inference('demod', [status(thm)], ['123', '124'])).
% 0.51/0.69  thf('126', plain,
% 0.51/0.69      ((m1_subset_1 @ sk_C @ 
% 0.51/0.69        (k1_zfmisc_1 @ 
% 0.51/0.69         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.51/0.69      inference('demod', [status(thm)], ['56', '57'])).
% 0.51/0.69  thf('127', plain,
% 0.51/0.69      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.51/0.69         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 0.51/0.69          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.51/0.69      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.51/0.69  thf('128', plain,
% 0.51/0.69      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.51/0.69         = (k2_relat_1 @ sk_C))),
% 0.51/0.69      inference('sup-', [status(thm)], ['126', '127'])).
% 0.51/0.69  thf('129', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.51/0.69      inference('demod', [status(thm)], ['48', '53', '60'])).
% 0.51/0.69  thf('130', plain,
% 0.51/0.69      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.51/0.69         = (k2_relat_1 @ sk_C))),
% 0.51/0.69      inference('demod', [status(thm)], ['128', '129'])).
% 0.51/0.69  thf('131', plain, ((v2_funct_1 @ sk_C)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('132', plain,
% 0.51/0.69      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.51/0.69         (k1_zfmisc_1 @ 
% 0.51/0.69          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 0.51/0.69        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.51/0.69      inference('demod', [status(thm)], ['121', '122', '125', '130', '131'])).
% 0.51/0.69  thf('133', plain,
% 0.51/0.69      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.51/0.69        | ~ (l1_struct_0 @ sk_B)
% 0.51/0.69        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.51/0.69           (k1_zfmisc_1 @ 
% 0.51/0.69            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 0.51/0.69      inference('sup-', [status(thm)], ['116', '132'])).
% 0.51/0.69  thf('134', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.51/0.69      inference('sup+', [status(thm)], ['18', '19'])).
% 0.51/0.69  thf('135', plain, ((l1_struct_0 @ sk_B)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('136', plain,
% 0.51/0.69      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.51/0.69        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.51/0.69           (k1_zfmisc_1 @ 
% 0.51/0.69            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 0.51/0.69      inference('demod', [status(thm)], ['133', '134', '135'])).
% 0.51/0.69  thf('137', plain,
% 0.51/0.69      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.51/0.69        (k1_zfmisc_1 @ 
% 0.51/0.69         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 0.51/0.69      inference('simplify', [status(thm)], ['136'])).
% 0.51/0.69  thf('138', plain,
% 0.51/0.69      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.51/0.69         (((k2_relset_1 @ X27 @ X26 @ X28) != (X26))
% 0.51/0.69          | ~ (v2_funct_1 @ X28)
% 0.51/0.69          | ((k2_tops_2 @ X27 @ X26 @ X28) = (k2_funct_1 @ X28))
% 0.51/0.69          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 0.51/0.69          | ~ (v1_funct_2 @ X28 @ X27 @ X26)
% 0.51/0.69          | ~ (v1_funct_1 @ X28))),
% 0.51/0.69      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.51/0.69  thf('139', plain,
% 0.51/0.69      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.51/0.69        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.51/0.69             (k1_relat_1 @ sk_C))
% 0.51/0.69        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.51/0.69            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.51/0.69        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.51/0.69        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.51/0.69            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['137', '138'])).
% 0.51/0.69  thf('140', plain,
% 0.51/0.69      (![X24 : $i]:
% 0.51/0.69         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.51/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.51/0.69  thf('141', plain,
% 0.51/0.69      ((m1_subset_1 @ sk_C @ 
% 0.51/0.69        (k1_zfmisc_1 @ 
% 0.51/0.69         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.51/0.69      inference('demod', [status(thm)], ['117', '118'])).
% 0.51/0.69  thf('142', plain,
% 0.51/0.69      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.51/0.69         (~ (v2_funct_1 @ X21)
% 0.51/0.69          | ((k2_relset_1 @ X23 @ X22 @ X21) != (X22))
% 0.51/0.69          | (v1_funct_1 @ (k2_funct_1 @ X21))
% 0.51/0.69          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.51/0.69          | ~ (v1_funct_2 @ X21 @ X23 @ X22)
% 0.51/0.69          | ~ (v1_funct_1 @ X21))),
% 0.51/0.69      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.51/0.69  thf('143', plain,
% 0.51/0.69      ((~ (v1_funct_1 @ sk_C)
% 0.51/0.69        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.51/0.69        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.51/0.69        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.51/0.69            != (u1_struct_0 @ sk_B))
% 0.51/0.69        | ~ (v2_funct_1 @ sk_C))),
% 0.51/0.69      inference('sup-', [status(thm)], ['141', '142'])).
% 0.51/0.69  thf('144', plain, ((v1_funct_1 @ sk_C)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('145', plain,
% 0.51/0.69      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.51/0.69      inference('demod', [status(thm)], ['123', '124'])).
% 0.51/0.69  thf('146', plain,
% 0.51/0.69      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.51/0.69         = (k2_relat_1 @ sk_C))),
% 0.51/0.69      inference('demod', [status(thm)], ['128', '129'])).
% 0.51/0.69  thf('147', plain, ((v2_funct_1 @ sk_C)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('148', plain,
% 0.51/0.69      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.51/0.69        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.51/0.69      inference('demod', [status(thm)], ['143', '144', '145', '146', '147'])).
% 0.51/0.69  thf('149', plain,
% 0.51/0.69      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.51/0.69        | ~ (l1_struct_0 @ sk_B)
% 0.51/0.69        | (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['140', '148'])).
% 0.51/0.69  thf('150', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.51/0.69      inference('sup+', [status(thm)], ['18', '19'])).
% 0.51/0.69  thf('151', plain, ((l1_struct_0 @ sk_B)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('152', plain,
% 0.51/0.69      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.51/0.69        | (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.51/0.69      inference('demod', [status(thm)], ['149', '150', '151'])).
% 0.51/0.69  thf('153', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.51/0.69      inference('simplify', [status(thm)], ['152'])).
% 0.51/0.69  thf('154', plain,
% 0.51/0.69      (![X24 : $i]:
% 0.51/0.69         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.51/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.51/0.69  thf('155', plain,
% 0.51/0.69      ((m1_subset_1 @ sk_C @ 
% 0.51/0.69        (k1_zfmisc_1 @ 
% 0.51/0.69         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.51/0.69      inference('demod', [status(thm)], ['117', '118'])).
% 0.51/0.69  thf('156', plain,
% 0.51/0.69      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.51/0.69         (~ (v2_funct_1 @ X21)
% 0.51/0.69          | ((k2_relset_1 @ X23 @ X22 @ X21) != (X22))
% 0.51/0.69          | (v1_funct_2 @ (k2_funct_1 @ X21) @ X22 @ X23)
% 0.51/0.69          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.51/0.69          | ~ (v1_funct_2 @ X21 @ X23 @ X22)
% 0.51/0.69          | ~ (v1_funct_1 @ X21))),
% 0.51/0.69      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.51/0.69  thf('157', plain,
% 0.51/0.69      ((~ (v1_funct_1 @ sk_C)
% 0.51/0.69        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.51/0.69        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.51/0.69           (k1_relat_1 @ sk_C))
% 0.51/0.69        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.51/0.69            != (u1_struct_0 @ sk_B))
% 0.51/0.69        | ~ (v2_funct_1 @ sk_C))),
% 0.51/0.69      inference('sup-', [status(thm)], ['155', '156'])).
% 0.51/0.69  thf('158', plain, ((v1_funct_1 @ sk_C)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('159', plain,
% 0.51/0.69      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.51/0.69      inference('demod', [status(thm)], ['123', '124'])).
% 0.51/0.69  thf('160', plain,
% 0.51/0.69      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.51/0.69         = (k2_relat_1 @ sk_C))),
% 0.51/0.69      inference('demod', [status(thm)], ['128', '129'])).
% 0.51/0.69  thf('161', plain, ((v2_funct_1 @ sk_C)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('162', plain,
% 0.51/0.69      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.51/0.69         (k1_relat_1 @ sk_C))
% 0.51/0.69        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.51/0.69      inference('demod', [status(thm)], ['157', '158', '159', '160', '161'])).
% 0.51/0.69  thf('163', plain,
% 0.51/0.69      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.51/0.69        | ~ (l1_struct_0 @ sk_B)
% 0.51/0.69        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.51/0.69           (k1_relat_1 @ sk_C)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['154', '162'])).
% 0.51/0.69  thf('164', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.51/0.69      inference('sup+', [status(thm)], ['18', '19'])).
% 0.51/0.69  thf('165', plain, ((l1_struct_0 @ sk_B)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('166', plain,
% 0.51/0.69      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.51/0.69        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.51/0.69           (k1_relat_1 @ sk_C)))),
% 0.51/0.69      inference('demod', [status(thm)], ['163', '164', '165'])).
% 0.51/0.69  thf('167', plain,
% 0.51/0.69      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.51/0.69        (k1_relat_1 @ sk_C))),
% 0.51/0.69      inference('simplify', [status(thm)], ['166'])).
% 0.51/0.69  thf('168', plain,
% 0.51/0.69      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.51/0.69          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.51/0.69        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.51/0.69        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.51/0.69            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.51/0.69      inference('demod', [status(thm)], ['139', '153', '167'])).
% 0.51/0.69  thf('169', plain,
% 0.51/0.69      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.51/0.69        (k1_zfmisc_1 @ 
% 0.51/0.69         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 0.51/0.69      inference('simplify', [status(thm)], ['136'])).
% 0.51/0.69  thf('170', plain,
% 0.51/0.69      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.51/0.69         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 0.51/0.69          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.51/0.69      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.51/0.69  thf('171', plain,
% 0.51/0.69      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.51/0.69         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['169', '170'])).
% 0.51/0.69  thf('172', plain,
% 0.51/0.69      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.51/0.69          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.51/0.69        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.51/0.69        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.51/0.69      inference('demod', [status(thm)], ['168', '171'])).
% 0.51/0.69  thf('173', plain,
% 0.51/0.69      ((m1_subset_1 @ sk_C @ 
% 0.51/0.69        (k1_zfmisc_1 @ 
% 0.51/0.69         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.51/0.69      inference('demod', [status(thm)], ['79', '80'])).
% 0.51/0.69  thf('174', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.51/0.69      inference('demod', [status(thm)], ['48', '53', '60'])).
% 0.51/0.69  thf('175', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.51/0.69      inference('sup+', [status(thm)], ['18', '19'])).
% 0.51/0.69  thf('176', plain,
% 0.51/0.69      (![X24 : $i]:
% 0.51/0.69         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.51/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.51/0.69  thf('177', plain,
% 0.51/0.69      (![X24 : $i]:
% 0.51/0.69         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.51/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.51/0.69  thf(t63_tops_2, axiom,
% 0.51/0.69    (![A:$i]:
% 0.51/0.69     ( ( l1_struct_0 @ A ) =>
% 0.51/0.69       ( ![B:$i]:
% 0.51/0.69         ( ( l1_struct_0 @ B ) =>
% 0.51/0.69           ( ![C:$i]:
% 0.51/0.69             ( ( ( v1_funct_1 @ C ) & 
% 0.51/0.69                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.51/0.69                 ( m1_subset_1 @
% 0.51/0.69                   C @ 
% 0.51/0.69                   ( k1_zfmisc_1 @
% 0.51/0.69                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.51/0.69               ( ( ( ( k2_relset_1 @
% 0.51/0.69                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.51/0.69                     ( k2_struct_0 @ B ) ) & 
% 0.51/0.69                   ( v2_funct_1 @ C ) ) =>
% 0.51/0.69                 ( v2_funct_1 @
% 0.51/0.69                   ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) ) ))).
% 0.51/0.69  thf('178', plain,
% 0.51/0.69      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.51/0.69         (~ (l1_struct_0 @ X29)
% 0.51/0.69          | ((k2_relset_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X29) @ X31)
% 0.51/0.69              != (k2_struct_0 @ X29))
% 0.51/0.69          | ~ (v2_funct_1 @ X31)
% 0.51/0.69          | (v2_funct_1 @ 
% 0.51/0.69             (k2_tops_2 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X29) @ X31))
% 0.51/0.69          | ~ (m1_subset_1 @ X31 @ 
% 0.51/0.69               (k1_zfmisc_1 @ 
% 0.51/0.69                (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X29))))
% 0.51/0.69          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X29))
% 0.51/0.69          | ~ (v1_funct_1 @ X31)
% 0.51/0.69          | ~ (l1_struct_0 @ X30))),
% 0.51/0.69      inference('cnf', [status(esa)], [t63_tops_2])).
% 0.51/0.69  thf('179', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.69         (~ (m1_subset_1 @ X2 @ 
% 0.51/0.69             (k1_zfmisc_1 @ 
% 0.51/0.69              (k2_zfmisc_1 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1))))
% 0.51/0.69          | ~ (l1_struct_0 @ X0)
% 0.51/0.69          | ~ (l1_struct_0 @ X0)
% 0.51/0.69          | ~ (v1_funct_1 @ X2)
% 0.51/0.69          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.51/0.69          | (v2_funct_1 @ 
% 0.51/0.69             (k2_tops_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1) @ X2))
% 0.51/0.69          | ~ (v2_funct_1 @ X2)
% 0.51/0.69          | ((k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1) @ X2)
% 0.51/0.69              != (k2_struct_0 @ X1))
% 0.51/0.69          | ~ (l1_struct_0 @ X1))),
% 0.51/0.69      inference('sup-', [status(thm)], ['177', '178'])).
% 0.51/0.69  thf('180', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.69         (~ (l1_struct_0 @ X1)
% 0.51/0.69          | ((k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1) @ X2)
% 0.51/0.69              != (k2_struct_0 @ X1))
% 0.51/0.69          | ~ (v2_funct_1 @ X2)
% 0.51/0.69          | (v2_funct_1 @ 
% 0.51/0.69             (k2_tops_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1) @ X2))
% 0.51/0.69          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.51/0.69          | ~ (v1_funct_1 @ X2)
% 0.51/0.69          | ~ (l1_struct_0 @ X0)
% 0.51/0.69          | ~ (m1_subset_1 @ X2 @ 
% 0.51/0.69               (k1_zfmisc_1 @ 
% 0.51/0.69                (k2_zfmisc_1 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1)))))),
% 0.51/0.69      inference('simplify', [status(thm)], ['179'])).
% 0.51/0.69  thf('181', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.69         (~ (m1_subset_1 @ X2 @ 
% 0.51/0.69             (k1_zfmisc_1 @ 
% 0.51/0.69              (k2_zfmisc_1 @ (k2_struct_0 @ X1) @ (k2_struct_0 @ X0))))
% 0.51/0.69          | ~ (l1_struct_0 @ X0)
% 0.51/0.69          | ~ (l1_struct_0 @ X1)
% 0.51/0.69          | ~ (v1_funct_1 @ X2)
% 0.51/0.69          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 0.51/0.69          | (v2_funct_1 @ 
% 0.51/0.69             (k2_tops_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ X2))
% 0.51/0.69          | ~ (v2_funct_1 @ X2)
% 0.51/0.69          | ((k2_relset_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ X2)
% 0.51/0.69              != (k2_struct_0 @ X0))
% 0.51/0.69          | ~ (l1_struct_0 @ X0))),
% 0.51/0.69      inference('sup-', [status(thm)], ['176', '180'])).
% 0.51/0.69  thf('182', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.69         (((k2_relset_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ X2)
% 0.51/0.69            != (k2_struct_0 @ X0))
% 0.51/0.69          | ~ (v2_funct_1 @ X2)
% 0.51/0.69          | (v2_funct_1 @ 
% 0.51/0.69             (k2_tops_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ X2))
% 0.51/0.69          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 0.51/0.69          | ~ (v1_funct_1 @ X2)
% 0.51/0.69          | ~ (l1_struct_0 @ X1)
% 0.51/0.69          | ~ (l1_struct_0 @ X0)
% 0.51/0.69          | ~ (m1_subset_1 @ X2 @ 
% 0.51/0.69               (k1_zfmisc_1 @ 
% 0.51/0.69                (k2_zfmisc_1 @ (k2_struct_0 @ X1) @ (k2_struct_0 @ X0)))))),
% 0.51/0.69      inference('simplify', [status(thm)], ['181'])).
% 0.51/0.69  thf('183', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         (~ (m1_subset_1 @ X1 @ 
% 0.51/0.69             (k1_zfmisc_1 @ 
% 0.51/0.69              (k2_zfmisc_1 @ (k2_struct_0 @ X0) @ (k2_relat_1 @ sk_C))))
% 0.51/0.69          | ~ (l1_struct_0 @ sk_B)
% 0.51/0.69          | ~ (l1_struct_0 @ X0)
% 0.51/0.69          | ~ (v1_funct_1 @ X1)
% 0.51/0.69          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.51/0.69          | (v2_funct_1 @ 
% 0.51/0.69             (k2_tops_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1))
% 0.51/0.69          | ~ (v2_funct_1 @ X1)
% 0.51/0.69          | ((k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1)
% 0.51/0.69              != (k2_struct_0 @ sk_B)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['175', '182'])).
% 0.51/0.69  thf('184', plain, ((l1_struct_0 @ sk_B)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('185', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.51/0.69      inference('sup+', [status(thm)], ['18', '19'])).
% 0.51/0.69  thf('186', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         (~ (m1_subset_1 @ X1 @ 
% 0.51/0.69             (k1_zfmisc_1 @ 
% 0.51/0.69              (k2_zfmisc_1 @ (k2_struct_0 @ X0) @ (k2_relat_1 @ sk_C))))
% 0.51/0.69          | ~ (l1_struct_0 @ X0)
% 0.51/0.69          | ~ (v1_funct_1 @ X1)
% 0.51/0.69          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.51/0.69          | (v2_funct_1 @ 
% 0.51/0.69             (k2_tops_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1))
% 0.51/0.69          | ~ (v2_funct_1 @ X1)
% 0.51/0.69          | ((k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1)
% 0.51/0.69              != (k2_relat_1 @ sk_C)))),
% 0.51/0.69      inference('demod', [status(thm)], ['183', '184', '185'])).
% 0.51/0.69  thf('187', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         (~ (m1_subset_1 @ X0 @ 
% 0.51/0.69             (k1_zfmisc_1 @ 
% 0.51/0.69              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))
% 0.51/0.69          | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ X0)
% 0.51/0.69              != (k2_relat_1 @ sk_C))
% 0.51/0.69          | ~ (v2_funct_1 @ X0)
% 0.51/0.69          | (v2_funct_1 @ 
% 0.51/0.69             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ X0))
% 0.51/0.69          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.51/0.69          | ~ (v1_funct_1 @ X0)
% 0.51/0.69          | ~ (l1_struct_0 @ sk_A))),
% 0.51/0.69      inference('sup-', [status(thm)], ['174', '186'])).
% 0.51/0.69  thf('188', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.51/0.69      inference('demod', [status(thm)], ['64', '65', '68'])).
% 0.51/0.69  thf('189', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.51/0.69      inference('demod', [status(thm)], ['64', '65', '68'])).
% 0.51/0.69  thf('190', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.51/0.69      inference('demod', [status(thm)], ['64', '65', '68'])).
% 0.51/0.69  thf('191', plain, ((l1_struct_0 @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('192', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         (~ (m1_subset_1 @ X0 @ 
% 0.51/0.69             (k1_zfmisc_1 @ 
% 0.51/0.69              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))
% 0.51/0.69          | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ X0)
% 0.51/0.69              != (k2_relat_1 @ sk_C))
% 0.51/0.69          | ~ (v2_funct_1 @ X0)
% 0.51/0.69          | (v2_funct_1 @ 
% 0.51/0.69             (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ X0))
% 0.51/0.69          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.51/0.69          | ~ (v1_funct_1 @ X0))),
% 0.51/0.69      inference('demod', [status(thm)], ['187', '188', '189', '190', '191'])).
% 0.51/0.69  thf('193', plain,
% 0.51/0.69      ((~ (v1_funct_1 @ sk_C)
% 0.51/0.69        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.51/0.69        | (v2_funct_1 @ 
% 0.51/0.69           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.51/0.69        | ~ (v2_funct_1 @ sk_C)
% 0.51/0.69        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.51/0.69            != (k2_relat_1 @ sk_C)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['173', '192'])).
% 0.51/0.69  thf('194', plain, ((v1_funct_1 @ sk_C)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('195', plain,
% 0.51/0.69      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.51/0.69      inference('demod', [status(thm)], ['123', '124'])).
% 0.51/0.69  thf('196', plain,
% 0.51/0.69      (![X24 : $i]:
% 0.51/0.69         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.51/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.51/0.69  thf('197', plain,
% 0.51/0.69      ((m1_subset_1 @ sk_C @ 
% 0.51/0.69        (k1_zfmisc_1 @ 
% 0.51/0.69         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.51/0.69      inference('demod', [status(thm)], ['117', '118'])).
% 0.51/0.69  thf('198', plain,
% 0.51/0.69      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.51/0.69         (((k2_relset_1 @ X27 @ X26 @ X28) != (X26))
% 0.51/0.69          | ~ (v2_funct_1 @ X28)
% 0.51/0.69          | ((k2_tops_2 @ X27 @ X26 @ X28) = (k2_funct_1 @ X28))
% 0.51/0.69          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 0.51/0.69          | ~ (v1_funct_2 @ X28 @ X27 @ X26)
% 0.51/0.69          | ~ (v1_funct_1 @ X28))),
% 0.51/0.69      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.51/0.69  thf('199', plain,
% 0.51/0.69      ((~ (v1_funct_1 @ sk_C)
% 0.51/0.69        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.51/0.69        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.51/0.69            = (k2_funct_1 @ sk_C))
% 0.51/0.69        | ~ (v2_funct_1 @ sk_C)
% 0.51/0.69        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.51/0.69            != (u1_struct_0 @ sk_B)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['197', '198'])).
% 0.51/0.69  thf('200', plain, ((v1_funct_1 @ sk_C)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('201', plain,
% 0.51/0.69      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.51/0.69      inference('demod', [status(thm)], ['123', '124'])).
% 0.51/0.69  thf('202', plain, ((v2_funct_1 @ sk_C)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('203', plain,
% 0.51/0.69      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.51/0.69         = (k2_relat_1 @ sk_C))),
% 0.51/0.69      inference('demod', [status(thm)], ['128', '129'])).
% 0.51/0.69  thf('204', plain,
% 0.51/0.69      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.51/0.69          = (k2_funct_1 @ sk_C))
% 0.51/0.69        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.51/0.69      inference('demod', [status(thm)], ['199', '200', '201', '202', '203'])).
% 0.51/0.69  thf('205', plain,
% 0.51/0.69      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.51/0.69        | ~ (l1_struct_0 @ sk_B)
% 0.51/0.69        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.51/0.69            = (k2_funct_1 @ sk_C)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['196', '204'])).
% 0.51/0.69  thf('206', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.51/0.69      inference('sup+', [status(thm)], ['18', '19'])).
% 0.51/0.69  thf('207', plain, ((l1_struct_0 @ sk_B)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('208', plain,
% 0.51/0.69      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.51/0.69        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.51/0.69            = (k2_funct_1 @ sk_C)))),
% 0.51/0.69      inference('demod', [status(thm)], ['205', '206', '207'])).
% 0.51/0.69  thf('209', plain,
% 0.51/0.69      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.51/0.69         = (k2_funct_1 @ sk_C))),
% 0.51/0.69      inference('simplify', [status(thm)], ['208'])).
% 0.51/0.69  thf('210', plain, ((v2_funct_1 @ sk_C)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('211', plain,
% 0.51/0.69      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.51/0.69         = (k2_relat_1 @ sk_C))),
% 0.51/0.69      inference('demod', [status(thm)], ['128', '129'])).
% 0.51/0.69  thf('212', plain,
% 0.51/0.69      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.51/0.69        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.51/0.69      inference('demod', [status(thm)],
% 0.51/0.69                ['193', '194', '195', '209', '210', '211'])).
% 0.51/0.69  thf('213', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.51/0.69      inference('simplify', [status(thm)], ['212'])).
% 0.51/0.69  thf('214', plain,
% 0.51/0.69      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.51/0.69          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.51/0.69        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.51/0.69      inference('demod', [status(thm)], ['172', '213'])).
% 0.51/0.69  thf(t55_funct_1, axiom,
% 0.51/0.69    (![A:$i]:
% 0.51/0.69     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.51/0.69       ( ( v2_funct_1 @ A ) =>
% 0.51/0.69         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.51/0.69           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.51/0.69  thf('215', plain,
% 0.51/0.69      (![X4 : $i]:
% 0.51/0.69         (~ (v2_funct_1 @ X4)
% 0.51/0.69          | ((k1_relat_1 @ X4) = (k2_relat_1 @ (k2_funct_1 @ X4)))
% 0.51/0.69          | ~ (v1_funct_1 @ X4)
% 0.51/0.69          | ~ (v1_relat_1 @ X4))),
% 0.51/0.69      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.51/0.69  thf('216', plain,
% 0.51/0.69      (![X4 : $i]:
% 0.51/0.69         (~ (v2_funct_1 @ X4)
% 0.51/0.69          | ((k2_relat_1 @ X4) = (k1_relat_1 @ (k2_funct_1 @ X4)))
% 0.51/0.69          | ~ (v1_funct_1 @ X4)
% 0.51/0.69          | ~ (v1_relat_1 @ X4))),
% 0.51/0.69      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.51/0.69  thf('217', plain,
% 0.51/0.69      (![X5 : $i]:
% 0.51/0.69         (~ (v2_funct_1 @ X5)
% 0.51/0.69          | ((k2_funct_1 @ (k2_funct_1 @ X5)) = (X5))
% 0.51/0.69          | ~ (v1_funct_1 @ X5)
% 0.51/0.69          | ~ (v1_relat_1 @ X5))),
% 0.51/0.69      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.51/0.69  thf('218', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.51/0.69      inference('simplify', [status(thm)], ['212'])).
% 0.51/0.69  thf('219', plain,
% 0.51/0.69      (![X5 : $i]:
% 0.51/0.69         (~ (v2_funct_1 @ X5)
% 0.51/0.69          | ((k2_funct_1 @ (k2_funct_1 @ X5)) = (X5))
% 0.51/0.69          | ~ (v1_funct_1 @ X5)
% 0.51/0.69          | ~ (v1_relat_1 @ X5))),
% 0.51/0.69      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.51/0.69  thf('220', plain,
% 0.51/0.69      (![X4 : $i]:
% 0.51/0.69         (~ (v2_funct_1 @ X4)
% 0.51/0.69          | ((k1_relat_1 @ X4) = (k2_relat_1 @ (k2_funct_1 @ X4)))
% 0.51/0.69          | ~ (v1_funct_1 @ X4)
% 0.51/0.69          | ~ (v1_relat_1 @ X4))),
% 0.51/0.69      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.51/0.69  thf('221', plain,
% 0.51/0.69      (![X5 : $i]:
% 0.51/0.69         (~ (v2_funct_1 @ X5)
% 0.51/0.69          | ((k2_funct_1 @ (k2_funct_1 @ X5)) = (X5))
% 0.51/0.69          | ~ (v1_funct_1 @ X5)
% 0.51/0.69          | ~ (v1_relat_1 @ X5))),
% 0.51/0.69      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.51/0.69  thf('222', plain,
% 0.51/0.69      (![X4 : $i]:
% 0.51/0.69         (~ (v2_funct_1 @ X4)
% 0.51/0.69          | ((k2_relat_1 @ X4) = (k1_relat_1 @ (k2_funct_1 @ X4)))
% 0.51/0.69          | ~ (v1_funct_1 @ X4)
% 0.51/0.69          | ~ (v1_relat_1 @ X4))),
% 0.51/0.69      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.51/0.69  thf('223', plain,
% 0.51/0.69      (![X15 : $i, X16 : $i]:
% 0.51/0.69         (((k1_relat_1 @ X16) != (X15))
% 0.51/0.69          | (v1_partfun1 @ X16 @ X15)
% 0.51/0.69          | ~ (v4_relat_1 @ X16 @ X15)
% 0.51/0.69          | ~ (v1_relat_1 @ X16))),
% 0.51/0.69      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.51/0.69  thf('224', plain,
% 0.51/0.69      (![X16 : $i]:
% 0.51/0.69         (~ (v1_relat_1 @ X16)
% 0.51/0.69          | ~ (v4_relat_1 @ X16 @ (k1_relat_1 @ X16))
% 0.51/0.69          | (v1_partfun1 @ X16 @ (k1_relat_1 @ X16)))),
% 0.51/0.69      inference('simplify', [status(thm)], ['223'])).
% 0.51/0.69  thf('225', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.51/0.69          | ~ (v1_relat_1 @ X0)
% 0.51/0.69          | ~ (v1_funct_1 @ X0)
% 0.51/0.69          | ~ (v2_funct_1 @ X0)
% 0.51/0.69          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.51/0.69          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['222', '224'])).
% 0.51/0.69  thf('226', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         (~ (v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.51/0.69          | ~ (v1_relat_1 @ X0)
% 0.51/0.69          | ~ (v1_funct_1 @ X0)
% 0.51/0.69          | ~ (v2_funct_1 @ X0)
% 0.51/0.69          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.51/0.69          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.51/0.69             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.51/0.69          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.51/0.69          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.51/0.69          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['221', '225'])).
% 0.51/0.69  thf('227', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         (~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.51/0.69          | ~ (v1_relat_1 @ X0)
% 0.51/0.69          | ~ (v1_funct_1 @ X0)
% 0.51/0.69          | ~ (v2_funct_1 @ X0)
% 0.51/0.69          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.51/0.69          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.51/0.69          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.51/0.69          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.51/0.69             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.51/0.69          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.51/0.69          | ~ (v2_funct_1 @ X0)
% 0.51/0.69          | ~ (v1_funct_1 @ X0)
% 0.51/0.69          | ~ (v1_relat_1 @ X0))),
% 0.51/0.69      inference('sup-', [status(thm)], ['220', '226'])).
% 0.51/0.69  thf('228', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         (~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.51/0.69          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.51/0.69             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.51/0.69          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.51/0.69          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.51/0.69          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.51/0.69          | ~ (v2_funct_1 @ X0)
% 0.51/0.69          | ~ (v1_funct_1 @ X0)
% 0.51/0.69          | ~ (v1_relat_1 @ X0)
% 0.51/0.69          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.51/0.69      inference('simplify', [status(thm)], ['227'])).
% 0.51/0.69  thf('229', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         (~ (v1_relat_1 @ X0)
% 0.51/0.69          | ~ (v1_relat_1 @ X0)
% 0.51/0.69          | ~ (v1_funct_1 @ X0)
% 0.51/0.69          | ~ (v2_funct_1 @ X0)
% 0.51/0.69          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.51/0.69          | ~ (v1_relat_1 @ X0)
% 0.51/0.69          | ~ (v1_funct_1 @ X0)
% 0.51/0.69          | ~ (v2_funct_1 @ X0)
% 0.51/0.69          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.51/0.69          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.51/0.69          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.51/0.69          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.51/0.69             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.51/0.69      inference('sup-', [status(thm)], ['219', '228'])).
% 0.51/0.69  thf('230', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.51/0.69           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.51/0.69          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.51/0.69          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.51/0.69          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.51/0.69          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.51/0.69          | ~ (v2_funct_1 @ X0)
% 0.51/0.69          | ~ (v1_funct_1 @ X0)
% 0.51/0.69          | ~ (v1_relat_1 @ X0))),
% 0.51/0.69      inference('simplify', [status(thm)], ['229'])).
% 0.51/0.69  thf('231', plain,
% 0.51/0.69      ((~ (v1_relat_1 @ sk_C)
% 0.51/0.69        | ~ (v1_funct_1 @ sk_C)
% 0.51/0.69        | ~ (v2_funct_1 @ sk_C)
% 0.51/0.69        | ~ (v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.51/0.69        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.51/0.69        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.51/0.69        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.51/0.69           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.51/0.69      inference('sup-', [status(thm)], ['218', '230'])).
% 0.51/0.69  thf('232', plain, ((v1_relat_1 @ sk_C)),
% 0.51/0.69      inference('demod', [status(thm)], ['51', '52'])).
% 0.51/0.69  thf('233', plain, ((v1_funct_1 @ sk_C)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('234', plain, ((v2_funct_1 @ sk_C)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('235', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.51/0.69      inference('sup-', [status(thm)], ['58', '59'])).
% 0.51/0.69  thf('236', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.51/0.69      inference('demod', [status(thm)], ['48', '53', '60'])).
% 0.51/0.69  thf('237', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 0.51/0.69      inference('demod', [status(thm)], ['235', '236'])).
% 0.51/0.69  thf('238', plain,
% 0.51/0.69      ((m1_subset_1 @ sk_C @ 
% 0.51/0.69        (k1_zfmisc_1 @ 
% 0.51/0.69         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.51/0.69      inference('demod', [status(thm)], ['79', '80'])).
% 0.51/0.69  thf('239', plain,
% 0.51/0.69      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.51/0.69         (~ (v2_funct_1 @ X21)
% 0.51/0.69          | ((k2_relset_1 @ X23 @ X22 @ X21) != (X22))
% 0.51/0.69          | (m1_subset_1 @ (k2_funct_1 @ X21) @ 
% 0.51/0.69             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.51/0.69          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.51/0.69          | ~ (v1_funct_2 @ X21 @ X23 @ X22)
% 0.51/0.69          | ~ (v1_funct_1 @ X21))),
% 0.51/0.69      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.51/0.69  thf('240', plain,
% 0.51/0.69      ((~ (v1_funct_1 @ sk_C)
% 0.51/0.69        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.51/0.69        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.51/0.69           (k1_zfmisc_1 @ 
% 0.51/0.69            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.51/0.69        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.51/0.69            != (k2_relat_1 @ sk_C))
% 0.51/0.69        | ~ (v2_funct_1 @ sk_C))),
% 0.51/0.69      inference('sup-', [status(thm)], ['238', '239'])).
% 0.51/0.69  thf('241', plain, ((v1_funct_1 @ sk_C)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('242', plain,
% 0.51/0.69      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.51/0.69      inference('demod', [status(thm)], ['95', '96'])).
% 0.51/0.69  thf('243', plain,
% 0.51/0.69      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.51/0.69         = (k2_relat_1 @ sk_C))),
% 0.51/0.69      inference('demod', [status(thm)], ['110', '111'])).
% 0.51/0.69  thf('244', plain, ((v2_funct_1 @ sk_C)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('245', plain,
% 0.51/0.69      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.51/0.69         (k1_zfmisc_1 @ 
% 0.51/0.69          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.51/0.69        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.51/0.69      inference('demod', [status(thm)], ['240', '241', '242', '243', '244'])).
% 0.51/0.69  thf('246', plain,
% 0.51/0.69      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.51/0.69        (k1_zfmisc_1 @ 
% 0.51/0.69         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.51/0.69      inference('simplify', [status(thm)], ['245'])).
% 0.51/0.69  thf('247', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.51/0.69          | (v1_relat_1 @ X0)
% 0.51/0.69          | ~ (v1_relat_1 @ X1))),
% 0.51/0.69      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.51/0.69  thf('248', plain,
% 0.51/0.69      ((~ (v1_relat_1 @ 
% 0.51/0.69           (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C)))
% 0.51/0.69        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['246', '247'])).
% 0.51/0.69  thf('249', plain,
% 0.51/0.69      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.51/0.69      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.51/0.69  thf('250', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.51/0.69      inference('demod', [status(thm)], ['248', '249'])).
% 0.51/0.69  thf('251', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.51/0.69      inference('simplify', [status(thm)], ['152'])).
% 0.51/0.69  thf('252', plain,
% 0.51/0.69      ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.51/0.69        (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.51/0.69      inference('demod', [status(thm)],
% 0.51/0.69                ['231', '232', '233', '234', '237', '250', '251'])).
% 0.51/0.69  thf('253', plain,
% 0.51/0.69      (((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.51/0.69        | ~ (v1_relat_1 @ sk_C)
% 0.51/0.69        | ~ (v1_funct_1 @ sk_C)
% 0.51/0.69        | ~ (v2_funct_1 @ sk_C))),
% 0.51/0.69      inference('sup+', [status(thm)], ['217', '252'])).
% 0.51/0.69  thf('254', plain, ((v1_relat_1 @ sk_C)),
% 0.51/0.69      inference('demod', [status(thm)], ['51', '52'])).
% 0.51/0.69  thf('255', plain, ((v1_funct_1 @ sk_C)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('256', plain, ((v2_funct_1 @ sk_C)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('257', plain,
% 0.51/0.69      ((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.51/0.69      inference('demod', [status(thm)], ['253', '254', '255', '256'])).
% 0.51/0.69  thf('258', plain,
% 0.51/0.69      (((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.51/0.69        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.51/0.69        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.51/0.69        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.51/0.69      inference('sup+', [status(thm)], ['216', '257'])).
% 0.51/0.69  thf('259', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.51/0.69      inference('demod', [status(thm)], ['248', '249'])).
% 0.51/0.69  thf('260', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.51/0.69      inference('simplify', [status(thm)], ['152'])).
% 0.51/0.69  thf('261', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.51/0.69      inference('simplify', [status(thm)], ['212'])).
% 0.51/0.69  thf('262', plain,
% 0.51/0.69      ((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.51/0.69      inference('demod', [status(thm)], ['258', '259', '260', '261'])).
% 0.51/0.69  thf('263', plain,
% 0.51/0.69      (![X15 : $i, X16 : $i]:
% 0.51/0.69         (~ (v1_partfun1 @ X16 @ X15)
% 0.51/0.69          | ((k1_relat_1 @ X16) = (X15))
% 0.51/0.69          | ~ (v4_relat_1 @ X16 @ X15)
% 0.51/0.69          | ~ (v1_relat_1 @ X16))),
% 0.51/0.69      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.51/0.69  thf('264', plain,
% 0.51/0.69      ((~ (v1_relat_1 @ sk_C)
% 0.51/0.69        | ~ (v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.51/0.69        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.51/0.69      inference('sup-', [status(thm)], ['262', '263'])).
% 0.51/0.69  thf('265', plain, ((v1_relat_1 @ sk_C)),
% 0.51/0.69      inference('demod', [status(thm)], ['51', '52'])).
% 0.51/0.69  thf('266', plain,
% 0.51/0.69      ((~ (v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.51/0.69        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.51/0.69      inference('demod', [status(thm)], ['264', '265'])).
% 0.51/0.69  thf('267', plain,
% 0.51/0.69      ((~ (v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.51/0.69        | ~ (v1_relat_1 @ sk_C)
% 0.51/0.69        | ~ (v1_funct_1 @ sk_C)
% 0.51/0.69        | ~ (v2_funct_1 @ sk_C)
% 0.51/0.69        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.51/0.69      inference('sup-', [status(thm)], ['215', '266'])).
% 0.51/0.69  thf('268', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 0.51/0.69      inference('demod', [status(thm)], ['235', '236'])).
% 0.51/0.69  thf('269', plain, ((v1_relat_1 @ sk_C)),
% 0.51/0.69      inference('demod', [status(thm)], ['51', '52'])).
% 0.51/0.69  thf('270', plain, ((v1_funct_1 @ sk_C)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('271', plain, ((v2_funct_1 @ sk_C)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('272', plain,
% 0.51/0.69      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.51/0.69      inference('demod', [status(thm)], ['267', '268', '269', '270', '271'])).
% 0.51/0.69  thf('273', plain,
% 0.51/0.69      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.51/0.69          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.51/0.69        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))),
% 0.51/0.69      inference('demod', [status(thm)], ['214', '272'])).
% 0.51/0.69  thf('274', plain,
% 0.51/0.69      (((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.51/0.69         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.51/0.69      inference('simplify', [status(thm)], ['273'])).
% 0.51/0.69  thf('275', plain,
% 0.51/0.69      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.51/0.69          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 0.51/0.69      inference('demod', [status(thm)], ['115', '274'])).
% 0.51/0.69  thf('276', plain,
% 0.51/0.69      ((~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.51/0.69           sk_C)
% 0.51/0.69        | ~ (v1_relat_1 @ sk_C)
% 0.51/0.69        | ~ (v1_funct_1 @ sk_C)
% 0.51/0.69        | ~ (v2_funct_1 @ sk_C))),
% 0.51/0.69      inference('sup-', [status(thm)], ['0', '275'])).
% 0.51/0.69  thf('277', plain,
% 0.51/0.69      ((m1_subset_1 @ sk_C @ 
% 0.51/0.69        (k1_zfmisc_1 @ 
% 0.51/0.69         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.51/0.69      inference('demod', [status(thm)], ['117', '118'])).
% 0.51/0.69  thf('278', plain,
% 0.51/0.69      ((m1_subset_1 @ sk_C @ 
% 0.51/0.69        (k1_zfmisc_1 @ 
% 0.51/0.69         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf(reflexivity_r2_funct_2, axiom,
% 0.51/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.51/0.69     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.51/0.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.51/0.69         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.51/0.69         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.51/0.69       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.51/0.69  thf('279', plain,
% 0.51/0.69      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.51/0.69         ((r2_funct_2 @ X17 @ X18 @ X19 @ X19)
% 0.51/0.69          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.51/0.69          | ~ (v1_funct_2 @ X19 @ X17 @ X18)
% 0.51/0.69          | ~ (v1_funct_1 @ X19)
% 0.51/0.69          | ~ (v1_funct_1 @ X20)
% 0.51/0.69          | ~ (v1_funct_2 @ X20 @ X17 @ X18)
% 0.51/0.69          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.51/0.69      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.51/0.69  thf('280', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         (~ (m1_subset_1 @ X0 @ 
% 0.51/0.69             (k1_zfmisc_1 @ 
% 0.51/0.69              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.51/0.69          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.51/0.69          | ~ (v1_funct_1 @ X0)
% 0.51/0.69          | ~ (v1_funct_1 @ sk_C)
% 0.51/0.69          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.51/0.69          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.51/0.69             sk_C))),
% 0.51/0.69      inference('sup-', [status(thm)], ['278', '279'])).
% 0.51/0.69  thf('281', plain, ((v1_funct_1 @ sk_C)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('282', plain,
% 0.51/0.69      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('283', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         (~ (m1_subset_1 @ X0 @ 
% 0.51/0.69             (k1_zfmisc_1 @ 
% 0.51/0.69              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.51/0.69          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.51/0.69          | ~ (v1_funct_1 @ X0)
% 0.51/0.69          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.51/0.69             sk_C))),
% 0.51/0.69      inference('demod', [status(thm)], ['280', '281', '282'])).
% 0.51/0.69  thf('284', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.51/0.69      inference('demod', [status(thm)], ['64', '65', '68'])).
% 0.51/0.69  thf('285', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.51/0.69      inference('demod', [status(thm)], ['64', '65', '68'])).
% 0.51/0.69  thf('286', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.51/0.69      inference('demod', [status(thm)], ['64', '65', '68'])).
% 0.51/0.69  thf('287', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         (~ (m1_subset_1 @ X0 @ 
% 0.51/0.69             (k1_zfmisc_1 @ 
% 0.51/0.69              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.51/0.69          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.51/0.69          | ~ (v1_funct_1 @ X0)
% 0.51/0.69          | (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.51/0.69             sk_C))),
% 0.51/0.69      inference('demod', [status(thm)], ['283', '284', '285', '286'])).
% 0.51/0.69  thf('288', plain,
% 0.51/0.69      (((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 0.51/0.69        | ~ (v1_funct_1 @ sk_C)
% 0.51/0.69        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['277', '287'])).
% 0.51/0.69  thf('289', plain, ((v1_funct_1 @ sk_C)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('290', plain,
% 0.51/0.69      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.51/0.69      inference('demod', [status(thm)], ['123', '124'])).
% 0.51/0.69  thf('291', plain,
% 0.51/0.69      ((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.51/0.69      inference('demod', [status(thm)], ['288', '289', '290'])).
% 0.51/0.69  thf('292', plain, ((v1_relat_1 @ sk_C)),
% 0.51/0.69      inference('demod', [status(thm)], ['51', '52'])).
% 0.51/0.69  thf('293', plain, ((v1_funct_1 @ sk_C)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('294', plain, ((v2_funct_1 @ sk_C)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('295', plain, ($false),
% 0.51/0.69      inference('demod', [status(thm)], ['276', '291', '292', '293', '294'])).
% 0.51/0.69  
% 0.51/0.69  % SZS output end Refutation
% 0.51/0.69  
% 0.51/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
