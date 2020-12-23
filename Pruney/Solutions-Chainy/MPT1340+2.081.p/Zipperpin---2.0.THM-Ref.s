%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aSW4rCx1zs

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:21 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  324 (7408 expanded)
%              Number of leaves         :   39 (2153 expanded)
%              Depth                    :   35
%              Number of atoms          : 3101 (159637 expanded)
%              Number of equality atoms :  151 (4344 expanded)
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
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('15',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( v1_partfun1 @ X12 @ X13 )
      | ~ ( v1_funct_2 @ X12 @ X13 @ X14 )
      | ~ ( v1_funct_1 @ X12 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('19',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('25',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('26',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','28'])).

thf('30',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('31',plain,(
    ! [X25: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('32',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['29','36'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('38',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_partfun1 @ X16 @ X15 )
      | ( ( k1_relat_1 @ X16 )
        = X15 )
      | ~ ( v4_relat_1 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('43',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('44',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('46',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('47',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','44','47'])).

thf('49',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('50',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['29','36'])).

thf('51',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_partfun1 @ X16 @ X15 )
      | ( ( k1_relat_1 @ X16 )
        = X15 )
      | ~ ( v4_relat_1 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('55',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['42','43'])).

thf('57',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('63',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['55','56','63'])).

thf('65',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','44','47'])).

thf('66',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('67',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['9','48','64','65','66'])).

thf('68',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('70',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['55','56','63'])).

thf('76',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

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

thf('77',plain,(
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

thf('78',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('81',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('82',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['80','85'])).

thf('87',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('90',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['55','56','63'])).

thf('92',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('95',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('96',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['94','99'])).

thf('101',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('104',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('105',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['55','56','63'])).

thf('107',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['78','79','92','93','107'])).

thf('109',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['67','109'])).

thf('111',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('112',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('113',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['55','56','63'])).

thf('114',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['112','113'])).

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

thf('115',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X21 )
       != X22 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('116',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('119',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['55','56','63'])).

thf('120',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('122',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('123',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['55','56','63'])).

thf('125',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['116','117','120','125','126'])).

thf('128',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['111','127'])).

thf('129',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('130',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('132',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
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

thf('134',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('136',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('137',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X21 )
       != X22 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('138',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('141',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('142',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['138','139','140','141','142'])).

thf('144',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['135','143'])).

thf('145',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('146',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['144','145','146'])).

thf('148',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('150',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('151',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X21 )
       != X22 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X21 ) @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('152',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('155',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('156',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['152','153','154','155','156'])).

thf('158',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['149','157'])).

thf('159',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('160',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['158','159','160'])).

thf('162',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['134','148','162'])).

thf('164',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('165',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('166',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['163','166'])).

thf('168',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('169',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','44','47'])).

thf('170',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('171',plain,(
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

thf('172',plain,(
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

thf('173',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ X2 ) )
      | ~ ( v2_funct_1 @ X2 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ X2 )
       != ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relset_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ X2 )
       != ( k2_struct_0 @ X0 ) )
      | ~ ( v2_funct_1 @ X2 )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ X2 ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( k2_struct_0 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( k2_relat_1 @ sk_C ) ) ) )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 )
       != ( k2_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['170','174'])).

thf('176',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( k2_relat_1 @ sk_C ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 )
       != ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['175','176','177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X0 )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X0 ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['169','178'])).

thf('180',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','44','47'])).

thf('181',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','44','47'])).

thf('182',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','44','47'])).

thf('183',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ X0 )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ X0 ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['179','180','181','182','183'])).

thf('185',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['168','184'])).

thf('186',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('188',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('189',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('190',plain,(
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

thf('191',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('194',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('196',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['191','192','193','194','195'])).

thf('197',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['188','196'])).

thf('198',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('199',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['197','198','199'])).

thf('201',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['200'])).

thf('202',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('204',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['185','186','187','201','202','203'])).

thf('205',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['204'])).

thf('206',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['167','205'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('207',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('208',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('209',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X5 ) )
        = X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('210',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['204'])).

thf('211',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X5 ) )
        = X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('212',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('213',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X5 ) )
        = X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('214',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('215',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k1_relat_1 @ X16 )
       != X15 )
      | ( v1_partfun1 @ X16 @ X15 )
      | ~ ( v4_relat_1 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('216',plain,(
    ! [X16: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v4_relat_1 @ X16 @ ( k1_relat_1 @ X16 ) )
      | ( v1_partfun1 @ X16 @ ( k1_relat_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['215'])).

thf('217',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['214','216'])).

thf('218',plain,(
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
    inference('sup-',[status(thm)],['213','217'])).

thf('219',plain,(
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
    inference('sup-',[status(thm)],['212','218'])).

thf('220',plain,(
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
    inference(simplify,[status(thm)],['219'])).

thf('221',plain,(
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
    inference('sup-',[status(thm)],['211','220'])).

thf('222',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['221'])).

thf('223',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['210','222'])).

thf('224',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['42','43'])).

thf('225',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('228',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['55','56','63'])).

thf('229',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['227','228'])).

thf('230',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('231',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X21 )
       != X22 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('232',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['230','231'])).

thf('233',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('235',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('236',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['232','233','234','235','236'])).

thf('238',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['237'])).

thf('239',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('240',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['238','239'])).

thf('241',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('242',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['240','241'])).

thf('243',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['147'])).

thf('244',plain,(
    v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['223','224','225','226','229','242','243'])).

thf('245',plain,
    ( ( v1_partfun1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['209','244'])).

thf('246',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['42','43'])).

thf('247',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,(
    v1_partfun1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['245','246','247','248'])).

thf('250',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['208','249'])).

thf('251',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['240','241'])).

thf('252',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['147'])).

thf('253',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['204'])).

thf('254',plain,(
    v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['250','251','252','253'])).

thf('255',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_partfun1 @ X16 @ X15 )
      | ( ( k1_relat_1 @ X16 )
        = X15 )
      | ~ ( v4_relat_1 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('256',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['254','255'])).

thf('257',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['42','43'])).

thf('258',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['256','257'])).

thf('259',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['207','258'])).

thf('260',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['227','228'])).

thf('261',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['42','43'])).

thf('262',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['259','260','261','262','263'])).

thf('265',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['206','264'])).

thf('266',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['265'])).

thf('267',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['110','266'])).

thf('268',plain,
    ( ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','267'])).

thf('269',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('270',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf(reflexivity_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_funct_2 @ A @ B @ C @ C ) ) )).

thf('271',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_funct_2 @ X17 @ X18 @ X19 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( v1_funct_2 @ X19 @ X17 @ X18 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_2 @ X20 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('272',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['270','271'])).

thf('273',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('274',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('275',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['272','273','274'])).

thf('276',plain,
    ( ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['269','275'])).

thf('277',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('278',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('279',plain,(
    r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['276','277','278'])).

thf('280',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['42','43'])).

thf('281',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('282',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('283',plain,(
    $false ),
    inference(demod,[status(thm)],['268','279','280','281','282'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aSW4rCx1zs
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:42:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.46/0.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.70  % Solved by: fo/fo7.sh
% 0.46/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.70  % done 479 iterations in 0.231s
% 0.46/0.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.70  % SZS output start Refutation
% 0.46/0.70  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.46/0.70  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.46/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.70  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.70  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.46/0.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.70  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.70  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.46/0.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.70  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.46/0.70  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.46/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.70  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.70  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.70  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.46/0.70  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.46/0.70  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.46/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.70  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.46/0.70  thf(t65_funct_1, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.70       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.46/0.70  thf('0', plain,
% 0.46/0.70      (![X5 : $i]:
% 0.46/0.70         (~ (v2_funct_1 @ X5)
% 0.46/0.70          | ((k2_funct_1 @ (k2_funct_1 @ X5)) = (X5))
% 0.46/0.70          | ~ (v1_funct_1 @ X5)
% 0.46/0.70          | ~ (v1_relat_1 @ X5))),
% 0.46/0.70      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.46/0.70  thf(d3_struct_0, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.46/0.70  thf('1', plain,
% 0.46/0.70      (![X24 : $i]:
% 0.46/0.70         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.70  thf('2', plain,
% 0.46/0.70      (![X24 : $i]:
% 0.46/0.70         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.70  thf(t64_tops_2, conjecture,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( l1_struct_0 @ A ) =>
% 0.46/0.70       ( ![B:$i]:
% 0.46/0.70         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.46/0.70           ( ![C:$i]:
% 0.46/0.70             ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.70                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.70                 ( m1_subset_1 @
% 0.46/0.70                   C @ 
% 0.46/0.70                   ( k1_zfmisc_1 @
% 0.46/0.70                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.70               ( ( ( ( k2_relset_1 @
% 0.46/0.70                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.46/0.70                     ( k2_struct_0 @ B ) ) & 
% 0.46/0.70                   ( v2_funct_1 @ C ) ) =>
% 0.46/0.70                 ( r2_funct_2 @
% 0.46/0.70                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.46/0.70                   ( k2_tops_2 @
% 0.46/0.70                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.46/0.70                     ( k2_tops_2 @
% 0.46/0.70                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.46/0.70                   C ) ) ) ) ) ) ))).
% 0.46/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.70    (~( ![A:$i]:
% 0.46/0.70        ( ( l1_struct_0 @ A ) =>
% 0.46/0.70          ( ![B:$i]:
% 0.46/0.70            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.46/0.70              ( ![C:$i]:
% 0.46/0.70                ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.70                    ( v1_funct_2 @
% 0.46/0.70                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.70                    ( m1_subset_1 @
% 0.46/0.70                      C @ 
% 0.46/0.70                      ( k1_zfmisc_1 @
% 0.46/0.70                        ( k2_zfmisc_1 @
% 0.46/0.70                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.70                  ( ( ( ( k2_relset_1 @
% 0.46/0.70                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.46/0.70                        ( k2_struct_0 @ B ) ) & 
% 0.46/0.70                      ( v2_funct_1 @ C ) ) =>
% 0.46/0.70                    ( r2_funct_2 @
% 0.46/0.70                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.46/0.70                      ( k2_tops_2 @
% 0.46/0.70                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.46/0.70                        ( k2_tops_2 @
% 0.46/0.70                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.46/0.70                      C ) ) ) ) ) ) ) )),
% 0.46/0.70    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.46/0.70  thf('3', plain,
% 0.46/0.70      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.70          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.70           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.70          sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('4', plain,
% 0.46/0.70      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.70           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.70            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.70           sk_C)
% 0.46/0.70        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.70      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.70  thf('5', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('6', plain,
% 0.46/0.70      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.70          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.70           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.70          sk_C)),
% 0.46/0.70      inference('demod', [status(thm)], ['4', '5'])).
% 0.46/0.70  thf('7', plain,
% 0.46/0.70      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.70           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.70            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.70           sk_C)
% 0.46/0.70        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup-', [status(thm)], ['1', '6'])).
% 0.46/0.70  thf('8', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('9', plain,
% 0.46/0.70      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.70          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.70           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.70          sk_C)),
% 0.46/0.70      inference('demod', [status(thm)], ['7', '8'])).
% 0.46/0.70  thf('10', plain,
% 0.46/0.70      (![X24 : $i]:
% 0.46/0.70         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.70  thf('11', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('12', plain,
% 0.46/0.70      (((m1_subset_1 @ sk_C @ 
% 0.46/0.70         (k1_zfmisc_1 @ 
% 0.46/0.70          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.46/0.70        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['10', '11'])).
% 0.46/0.70  thf('13', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('14', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.70      inference('demod', [status(thm)], ['12', '13'])).
% 0.46/0.70  thf(cc5_funct_2, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.46/0.70       ( ![C:$i]:
% 0.46/0.70         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.70           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.46/0.70             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.46/0.70  thf('15', plain,
% 0.46/0.70      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.46/0.70          | (v1_partfun1 @ X12 @ X13)
% 0.46/0.70          | ~ (v1_funct_2 @ X12 @ X13 @ X14)
% 0.46/0.70          | ~ (v1_funct_1 @ X12)
% 0.46/0.70          | (v1_xboole_0 @ X14))),
% 0.46/0.70      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.46/0.70  thf('16', plain,
% 0.46/0.70      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.46/0.70        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.70        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.70        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.70  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('18', plain,
% 0.46/0.70      (![X24 : $i]:
% 0.46/0.70         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.70  thf('19', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('20', plain,
% 0.46/0.70      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.70        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['18', '19'])).
% 0.46/0.70  thf('21', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('22', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['20', '21'])).
% 0.46/0.70  thf('23', plain,
% 0.46/0.70      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.46/0.70        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.46/0.70      inference('demod', [status(thm)], ['16', '17', '22'])).
% 0.46/0.70  thf('24', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(redefinition_k2_relset_1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.70       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.46/0.70  thf('25', plain,
% 0.46/0.70      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.46/0.70         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 0.46/0.70          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.46/0.70      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.70  thf('26', plain,
% 0.46/0.70      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70         = (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('sup-', [status(thm)], ['24', '25'])).
% 0.46/0.70  thf('27', plain,
% 0.46/0.70      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70         = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('28', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['26', '27'])).
% 0.46/0.70  thf('29', plain,
% 0.46/0.70      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.46/0.70        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.46/0.70      inference('demod', [status(thm)], ['23', '28'])).
% 0.46/0.70  thf('30', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['26', '27'])).
% 0.46/0.70  thf(fc5_struct_0, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.70       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.46/0.70  thf('31', plain,
% 0.46/0.70      (![X25 : $i]:
% 0.46/0.70         (~ (v1_xboole_0 @ (k2_struct_0 @ X25))
% 0.46/0.70          | ~ (l1_struct_0 @ X25)
% 0.46/0.70          | (v2_struct_0 @ X25))),
% 0.46/0.70      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.46/0.70  thf('32', plain,
% 0.46/0.70      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.46/0.70        | (v2_struct_0 @ sk_B)
% 0.46/0.70        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup-', [status(thm)], ['30', '31'])).
% 0.46/0.70  thf('33', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('34', plain,
% 0.46/0.70      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['32', '33'])).
% 0.46/0.70  thf('35', plain, (~ (v2_struct_0 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('36', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('clc', [status(thm)], ['34', '35'])).
% 0.46/0.70  thf('37', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.46/0.70      inference('clc', [status(thm)], ['29', '36'])).
% 0.46/0.70  thf(d4_partfun1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.46/0.70       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.46/0.70  thf('38', plain,
% 0.46/0.70      (![X15 : $i, X16 : $i]:
% 0.46/0.70         (~ (v1_partfun1 @ X16 @ X15)
% 0.46/0.70          | ((k1_relat_1 @ X16) = (X15))
% 0.46/0.70          | ~ (v4_relat_1 @ X16 @ X15)
% 0.46/0.70          | ~ (v1_relat_1 @ X16))),
% 0.46/0.70      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.46/0.70  thf('39', plain,
% 0.46/0.70      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.70        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.46/0.70        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['37', '38'])).
% 0.46/0.70  thf('40', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(cc2_relat_1, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( v1_relat_1 @ A ) =>
% 0.46/0.70       ( ![B:$i]:
% 0.46/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.46/0.70  thf('41', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.46/0.70          | (v1_relat_1 @ X0)
% 0.46/0.70          | ~ (v1_relat_1 @ X1))),
% 0.46/0.70      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.46/0.70  thf('42', plain,
% 0.46/0.70      ((~ (v1_relat_1 @ 
% 0.46/0.70           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.46/0.70        | (v1_relat_1 @ sk_C))),
% 0.46/0.70      inference('sup-', [status(thm)], ['40', '41'])).
% 0.46/0.70  thf(fc6_relat_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.46/0.70  thf('43', plain,
% 0.46/0.70      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.46/0.70      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.46/0.70  thf('44', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.70      inference('demod', [status(thm)], ['42', '43'])).
% 0.46/0.70  thf('45', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(cc2_relset_1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.70       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.46/0.70  thf('46', plain,
% 0.46/0.70      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.70         ((v4_relat_1 @ X6 @ X7)
% 0.46/0.70          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.46/0.70      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.70  thf('47', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.46/0.70      inference('sup-', [status(thm)], ['45', '46'])).
% 0.46/0.70  thf('48', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['39', '44', '47'])).
% 0.46/0.70  thf('49', plain,
% 0.46/0.70      (![X24 : $i]:
% 0.46/0.70         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.70  thf('50', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.46/0.70      inference('clc', [status(thm)], ['29', '36'])).
% 0.46/0.70  thf('51', plain,
% 0.46/0.70      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.70      inference('sup+', [status(thm)], ['49', '50'])).
% 0.46/0.70  thf('52', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('53', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['51', '52'])).
% 0.46/0.70  thf('54', plain,
% 0.46/0.70      (![X15 : $i, X16 : $i]:
% 0.46/0.70         (~ (v1_partfun1 @ X16 @ X15)
% 0.46/0.70          | ((k1_relat_1 @ X16) = (X15))
% 0.46/0.70          | ~ (v4_relat_1 @ X16 @ X15)
% 0.46/0.70          | ~ (v1_relat_1 @ X16))),
% 0.46/0.70      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.46/0.70  thf('55', plain,
% 0.46/0.70      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.70        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.46/0.70        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['53', '54'])).
% 0.46/0.70  thf('56', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.70      inference('demod', [status(thm)], ['42', '43'])).
% 0.46/0.70  thf('57', plain,
% 0.46/0.70      (![X24 : $i]:
% 0.46/0.70         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.70  thf('58', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('59', plain,
% 0.46/0.70      (((m1_subset_1 @ sk_C @ 
% 0.46/0.70         (k1_zfmisc_1 @ 
% 0.46/0.70          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.46/0.70        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.70      inference('sup+', [status(thm)], ['57', '58'])).
% 0.46/0.70  thf('60', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('61', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('demod', [status(thm)], ['59', '60'])).
% 0.46/0.70  thf('62', plain,
% 0.46/0.70      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.70         ((v4_relat_1 @ X6 @ X7)
% 0.46/0.70          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.46/0.70      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.70  thf('63', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.46/0.70      inference('sup-', [status(thm)], ['61', '62'])).
% 0.46/0.70  thf('64', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['55', '56', '63'])).
% 0.46/0.70  thf('65', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['39', '44', '47'])).
% 0.46/0.70  thf('66', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['26', '27'])).
% 0.46/0.70  thf('67', plain,
% 0.46/0.70      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.70          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.70           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)) @ 
% 0.46/0.70          sk_C)),
% 0.46/0.70      inference('demod', [status(thm)], ['9', '48', '64', '65', '66'])).
% 0.46/0.70  thf('68', plain,
% 0.46/0.70      (![X24 : $i]:
% 0.46/0.70         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.70  thf('69', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('demod', [status(thm)], ['59', '60'])).
% 0.46/0.70  thf('70', plain,
% 0.46/0.70      (((m1_subset_1 @ sk_C @ 
% 0.46/0.70         (k1_zfmisc_1 @ 
% 0.46/0.70          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.46/0.70        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['68', '69'])).
% 0.46/0.70  thf('71', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('72', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.70      inference('demod', [status(thm)], ['70', '71'])).
% 0.46/0.70  thf('73', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['26', '27'])).
% 0.46/0.70  thf('74', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.46/0.70      inference('demod', [status(thm)], ['72', '73'])).
% 0.46/0.70  thf('75', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['55', '56', '63'])).
% 0.46/0.70  thf('76', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.46/0.70      inference('demod', [status(thm)], ['74', '75'])).
% 0.46/0.70  thf(d4_tops_2, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.70       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.46/0.70         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.46/0.70  thf('77', plain,
% 0.46/0.70      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.46/0.70         (((k2_relset_1 @ X27 @ X26 @ X28) != (X26))
% 0.46/0.70          | ~ (v2_funct_1 @ X28)
% 0.46/0.70          | ((k2_tops_2 @ X27 @ X26 @ X28) = (k2_funct_1 @ X28))
% 0.46/0.70          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 0.46/0.70          | ~ (v1_funct_2 @ X28 @ X27 @ X26)
% 0.46/0.70          | ~ (v1_funct_1 @ X28))),
% 0.46/0.70      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.46/0.70  thf('78', plain,
% 0.46/0.70      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.70        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.46/0.70        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.70            = (k2_funct_1 @ sk_C))
% 0.46/0.70        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.70        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.70            != (k2_relat_1 @ sk_C)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['76', '77'])).
% 0.46/0.70  thf('79', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('80', plain,
% 0.46/0.70      (![X24 : $i]:
% 0.46/0.70         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.70  thf('81', plain,
% 0.46/0.70      (![X24 : $i]:
% 0.46/0.70         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.70  thf('82', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('83', plain,
% 0.46/0.70      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.70        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.70      inference('sup+', [status(thm)], ['81', '82'])).
% 0.46/0.70  thf('84', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('85', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['83', '84'])).
% 0.46/0.70  thf('86', plain,
% 0.46/0.70      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.70        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['80', '85'])).
% 0.46/0.70  thf('87', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('88', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['86', '87'])).
% 0.46/0.70  thf('89', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['26', '27'])).
% 0.46/0.70  thf('90', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['88', '89'])).
% 0.46/0.70  thf('91', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['55', '56', '63'])).
% 0.46/0.70  thf('92', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['90', '91'])).
% 0.46/0.70  thf('93', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('94', plain,
% 0.46/0.70      (![X24 : $i]:
% 0.46/0.70         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.70  thf('95', plain,
% 0.46/0.70      (![X24 : $i]:
% 0.46/0.70         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.70  thf('96', plain,
% 0.46/0.70      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70         = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('97', plain,
% 0.46/0.70      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70          = (k2_struct_0 @ sk_B))
% 0.46/0.70        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.70      inference('sup+', [status(thm)], ['95', '96'])).
% 0.46/0.70  thf('98', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('99', plain,
% 0.46/0.70      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70         = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['97', '98'])).
% 0.46/0.70  thf('100', plain,
% 0.46/0.70      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70          = (k2_struct_0 @ sk_B))
% 0.46/0.70        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['94', '99'])).
% 0.46/0.70  thf('101', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('102', plain,
% 0.46/0.70      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70         = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['100', '101'])).
% 0.46/0.70  thf('103', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['26', '27'])).
% 0.46/0.70  thf('104', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['26', '27'])).
% 0.46/0.70  thf('105', plain,
% 0.46/0.70      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.70         = (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.46/0.70  thf('106', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['55', '56', '63'])).
% 0.46/0.70  thf('107', plain,
% 0.46/0.70      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.70         = (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['105', '106'])).
% 0.46/0.70  thf('108', plain,
% 0.46/0.70      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.70          = (k2_funct_1 @ sk_C))
% 0.46/0.70        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['78', '79', '92', '93', '107'])).
% 0.46/0.70  thf('109', plain,
% 0.46/0.70      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.70         = (k2_funct_1 @ sk_C))),
% 0.46/0.70      inference('simplify', [status(thm)], ['108'])).
% 0.46/0.70  thf('110', plain,
% 0.46/0.70      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.70          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.70           (k2_funct_1 @ sk_C)) @ 
% 0.46/0.70          sk_C)),
% 0.46/0.70      inference('demod', [status(thm)], ['67', '109'])).
% 0.46/0.70  thf('111', plain,
% 0.46/0.70      (![X24 : $i]:
% 0.46/0.70         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.70  thf('112', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('demod', [status(thm)], ['59', '60'])).
% 0.46/0.70  thf('113', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['55', '56', '63'])).
% 0.46/0.70  thf('114', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('demod', [status(thm)], ['112', '113'])).
% 0.46/0.70  thf(t31_funct_2, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.70       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.46/0.70         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.46/0.70           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.46/0.70           ( m1_subset_1 @
% 0.46/0.70             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.46/0.70  thf('115', plain,
% 0.46/0.70      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.70         (~ (v2_funct_1 @ X21)
% 0.46/0.70          | ((k2_relset_1 @ X23 @ X22 @ X21) != (X22))
% 0.46/0.70          | (m1_subset_1 @ (k2_funct_1 @ X21) @ 
% 0.46/0.70             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.46/0.70          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.46/0.70          | ~ (v1_funct_2 @ X21 @ X23 @ X22)
% 0.46/0.70          | ~ (v1_funct_1 @ X21))),
% 0.46/0.70      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.46/0.70  thf('116', plain,
% 0.46/0.70      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.70        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.46/0.70        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.70           (k1_zfmisc_1 @ 
% 0.46/0.70            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 0.46/0.70        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70            != (u1_struct_0 @ sk_B))
% 0.46/0.70        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.70      inference('sup-', [status(thm)], ['114', '115'])).
% 0.46/0.70  thf('117', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('118', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['83', '84'])).
% 0.46/0.70  thf('119', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['55', '56', '63'])).
% 0.46/0.70  thf('120', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['118', '119'])).
% 0.46/0.70  thf('121', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('demod', [status(thm)], ['59', '60'])).
% 0.46/0.70  thf('122', plain,
% 0.46/0.70      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.46/0.70         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 0.46/0.70          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.46/0.70      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.70  thf('123', plain,
% 0.46/0.70      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70         = (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('sup-', [status(thm)], ['121', '122'])).
% 0.46/0.70  thf('124', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['55', '56', '63'])).
% 0.46/0.70  thf('125', plain,
% 0.46/0.70      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70         = (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['123', '124'])).
% 0.46/0.70  thf('126', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('127', plain,
% 0.46/0.70      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.70         (k1_zfmisc_1 @ 
% 0.46/0.70          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 0.46/0.70        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.46/0.70      inference('demod', [status(thm)], ['116', '117', '120', '125', '126'])).
% 0.46/0.70  thf('128', plain,
% 0.46/0.70      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.46/0.70        | ~ (l1_struct_0 @ sk_B)
% 0.46/0.70        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.70           (k1_zfmisc_1 @ 
% 0.46/0.70            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['111', '127'])).
% 0.46/0.70  thf('129', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['26', '27'])).
% 0.46/0.70  thf('130', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('131', plain,
% 0.46/0.70      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.46/0.70        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.70           (k1_zfmisc_1 @ 
% 0.46/0.70            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 0.46/0.70      inference('demod', [status(thm)], ['128', '129', '130'])).
% 0.46/0.70  thf('132', plain,
% 0.46/0.70      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 0.46/0.70      inference('simplify', [status(thm)], ['131'])).
% 0.46/0.70  thf('133', plain,
% 0.46/0.70      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.46/0.70         (((k2_relset_1 @ X27 @ X26 @ X28) != (X26))
% 0.46/0.70          | ~ (v2_funct_1 @ X28)
% 0.46/0.70          | ((k2_tops_2 @ X27 @ X26 @ X28) = (k2_funct_1 @ X28))
% 0.46/0.70          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 0.46/0.70          | ~ (v1_funct_2 @ X28 @ X27 @ X26)
% 0.46/0.70          | ~ (v1_funct_1 @ X28))),
% 0.46/0.70      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.46/0.70  thf('134', plain,
% 0.46/0.70      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.70        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.70             (k1_relat_1 @ sk_C))
% 0.46/0.70        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.70            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.70        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.70        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.70            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['132', '133'])).
% 0.46/0.70  thf('135', plain,
% 0.46/0.70      (![X24 : $i]:
% 0.46/0.70         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.70  thf('136', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('demod', [status(thm)], ['112', '113'])).
% 0.46/0.70  thf('137', plain,
% 0.46/0.70      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.70         (~ (v2_funct_1 @ X21)
% 0.46/0.70          | ((k2_relset_1 @ X23 @ X22 @ X21) != (X22))
% 0.46/0.70          | (v1_funct_1 @ (k2_funct_1 @ X21))
% 0.46/0.70          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.46/0.70          | ~ (v1_funct_2 @ X21 @ X23 @ X22)
% 0.46/0.70          | ~ (v1_funct_1 @ X21))),
% 0.46/0.70      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.46/0.70  thf('138', plain,
% 0.46/0.70      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.70        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.46/0.70        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.70        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70            != (u1_struct_0 @ sk_B))
% 0.46/0.70        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.70      inference('sup-', [status(thm)], ['136', '137'])).
% 0.46/0.70  thf('139', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('140', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['118', '119'])).
% 0.46/0.70  thf('141', plain,
% 0.46/0.70      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70         = (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['123', '124'])).
% 0.46/0.70  thf('142', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('143', plain,
% 0.46/0.70      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.70        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.46/0.70      inference('demod', [status(thm)], ['138', '139', '140', '141', '142'])).
% 0.46/0.70  thf('144', plain,
% 0.46/0.70      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.46/0.70        | ~ (l1_struct_0 @ sk_B)
% 0.46/0.70        | (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['135', '143'])).
% 0.46/0.70  thf('145', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['26', '27'])).
% 0.46/0.70  thf('146', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('147', plain,
% 0.46/0.70      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.46/0.70        | (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['144', '145', '146'])).
% 0.46/0.70  thf('148', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.70      inference('simplify', [status(thm)], ['147'])).
% 0.46/0.70  thf('149', plain,
% 0.46/0.70      (![X24 : $i]:
% 0.46/0.70         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.70  thf('150', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('demod', [status(thm)], ['112', '113'])).
% 0.46/0.70  thf('151', plain,
% 0.46/0.70      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.70         (~ (v2_funct_1 @ X21)
% 0.46/0.70          | ((k2_relset_1 @ X23 @ X22 @ X21) != (X22))
% 0.46/0.70          | (v1_funct_2 @ (k2_funct_1 @ X21) @ X22 @ X23)
% 0.46/0.70          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.46/0.70          | ~ (v1_funct_2 @ X21 @ X23 @ X22)
% 0.46/0.70          | ~ (v1_funct_1 @ X21))),
% 0.46/0.70      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.46/0.70  thf('152', plain,
% 0.46/0.70      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.70        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.46/0.70        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.70           (k1_relat_1 @ sk_C))
% 0.46/0.70        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70            != (u1_struct_0 @ sk_B))
% 0.46/0.70        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.70      inference('sup-', [status(thm)], ['150', '151'])).
% 0.46/0.70  thf('153', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('154', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['118', '119'])).
% 0.46/0.70  thf('155', plain,
% 0.46/0.70      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70         = (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['123', '124'])).
% 0.46/0.70  thf('156', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('157', plain,
% 0.46/0.70      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.70         (k1_relat_1 @ sk_C))
% 0.46/0.70        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.46/0.70      inference('demod', [status(thm)], ['152', '153', '154', '155', '156'])).
% 0.46/0.70  thf('158', plain,
% 0.46/0.70      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.46/0.70        | ~ (l1_struct_0 @ sk_B)
% 0.46/0.70        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.70           (k1_relat_1 @ sk_C)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['149', '157'])).
% 0.46/0.70  thf('159', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['26', '27'])).
% 0.46/0.70  thf('160', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('161', plain,
% 0.46/0.70      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.46/0.70        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.70           (k1_relat_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['158', '159', '160'])).
% 0.46/0.70  thf('162', plain,
% 0.46/0.70      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.70        (k1_relat_1 @ sk_C))),
% 0.46/0.70      inference('simplify', [status(thm)], ['161'])).
% 0.46/0.70  thf('163', plain,
% 0.46/0.70      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.70          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.70        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.70        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.70            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['134', '148', '162'])).
% 0.46/0.70  thf('164', plain,
% 0.46/0.70      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 0.46/0.70      inference('simplify', [status(thm)], ['131'])).
% 0.46/0.70  thf('165', plain,
% 0.46/0.70      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.46/0.70         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 0.46/0.70          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.46/0.70      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.70  thf('166', plain,
% 0.46/0.70      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.70         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['164', '165'])).
% 0.46/0.70  thf('167', plain,
% 0.46/0.70      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.70          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.70        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.70        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['163', '166'])).
% 0.46/0.70  thf('168', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.46/0.70      inference('demod', [status(thm)], ['74', '75'])).
% 0.46/0.70  thf('169', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['39', '44', '47'])).
% 0.46/0.70  thf('170', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['26', '27'])).
% 0.46/0.70  thf('171', plain,
% 0.46/0.70      (![X24 : $i]:
% 0.46/0.70         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.70  thf(t63_tops_2, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( l1_struct_0 @ A ) =>
% 0.46/0.70       ( ![B:$i]:
% 0.46/0.70         ( ( l1_struct_0 @ B ) =>
% 0.46/0.70           ( ![C:$i]:
% 0.46/0.70             ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.70                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.70                 ( m1_subset_1 @
% 0.46/0.70                   C @ 
% 0.46/0.70                   ( k1_zfmisc_1 @
% 0.46/0.70                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.70               ( ( ( ( k2_relset_1 @
% 0.46/0.70                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.46/0.70                     ( k2_struct_0 @ B ) ) & 
% 0.46/0.70                   ( v2_funct_1 @ C ) ) =>
% 0.46/0.70                 ( v2_funct_1 @
% 0.46/0.70                   ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) ) ))).
% 0.46/0.70  thf('172', plain,
% 0.46/0.70      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.46/0.70         (~ (l1_struct_0 @ X29)
% 0.46/0.70          | ((k2_relset_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X29) @ X31)
% 0.46/0.70              != (k2_struct_0 @ X29))
% 0.46/0.70          | ~ (v2_funct_1 @ X31)
% 0.46/0.70          | (v2_funct_1 @ 
% 0.46/0.70             (k2_tops_2 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X29) @ X31))
% 0.46/0.70          | ~ (m1_subset_1 @ X31 @ 
% 0.46/0.70               (k1_zfmisc_1 @ 
% 0.46/0.70                (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X29))))
% 0.46/0.70          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X29))
% 0.46/0.70          | ~ (v1_funct_1 @ X31)
% 0.46/0.70          | ~ (l1_struct_0 @ X30))),
% 0.46/0.70      inference('cnf', [status(esa)], [t63_tops_2])).
% 0.46/0.70  thf('173', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X2 @ 
% 0.46/0.70             (k1_zfmisc_1 @ 
% 0.46/0.70              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (k2_struct_0 @ X0))))
% 0.46/0.70          | ~ (l1_struct_0 @ X0)
% 0.46/0.70          | ~ (l1_struct_0 @ X1)
% 0.46/0.70          | ~ (v1_funct_1 @ X2)
% 0.46/0.70          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 0.46/0.70          | (v2_funct_1 @ 
% 0.46/0.70             (k2_tops_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ X2))
% 0.46/0.70          | ~ (v2_funct_1 @ X2)
% 0.46/0.70          | ((k2_relset_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ X2)
% 0.46/0.70              != (k2_struct_0 @ X0))
% 0.46/0.70          | ~ (l1_struct_0 @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['171', '172'])).
% 0.46/0.70  thf('174', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.70         (((k2_relset_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ X2)
% 0.46/0.70            != (k2_struct_0 @ X0))
% 0.46/0.70          | ~ (v2_funct_1 @ X2)
% 0.46/0.70          | (v2_funct_1 @ 
% 0.46/0.70             (k2_tops_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ X2))
% 0.46/0.70          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 0.46/0.70          | ~ (v1_funct_1 @ X2)
% 0.46/0.70          | ~ (l1_struct_0 @ X1)
% 0.46/0.70          | ~ (l1_struct_0 @ X0)
% 0.46/0.70          | ~ (m1_subset_1 @ X2 @ 
% 0.46/0.70               (k1_zfmisc_1 @ 
% 0.46/0.70                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (k2_struct_0 @ X0)))))),
% 0.46/0.70      inference('simplify', [status(thm)], ['173'])).
% 0.46/0.70  thf('175', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X1 @ 
% 0.46/0.70             (k1_zfmisc_1 @ 
% 0.46/0.70              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (k2_relat_1 @ sk_C))))
% 0.46/0.70          | ~ (l1_struct_0 @ sk_B)
% 0.46/0.70          | ~ (l1_struct_0 @ X0)
% 0.46/0.70          | ~ (v1_funct_1 @ X1)
% 0.46/0.70          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.46/0.70          | (v2_funct_1 @ 
% 0.46/0.70             (k2_tops_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1))
% 0.46/0.70          | ~ (v2_funct_1 @ X1)
% 0.46/0.70          | ((k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1)
% 0.46/0.70              != (k2_struct_0 @ sk_B)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['170', '174'])).
% 0.46/0.70  thf('176', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('177', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['26', '27'])).
% 0.46/0.70  thf('178', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X1 @ 
% 0.46/0.70             (k1_zfmisc_1 @ 
% 0.46/0.70              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (k2_relat_1 @ sk_C))))
% 0.46/0.70          | ~ (l1_struct_0 @ X0)
% 0.46/0.70          | ~ (v1_funct_1 @ X1)
% 0.46/0.70          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.46/0.70          | (v2_funct_1 @ 
% 0.46/0.70             (k2_tops_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1))
% 0.46/0.70          | ~ (v2_funct_1 @ X1)
% 0.46/0.70          | ((k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1)
% 0.46/0.70              != (k2_relat_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['175', '176', '177'])).
% 0.46/0.70  thf('179', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X0 @ 
% 0.46/0.70             (k1_zfmisc_1 @ 
% 0.46/0.70              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))
% 0.46/0.70          | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ X0)
% 0.46/0.70              != (k2_relat_1 @ sk_C))
% 0.46/0.70          | ~ (v2_funct_1 @ X0)
% 0.46/0.70          | (v2_funct_1 @ 
% 0.46/0.70             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ X0))
% 0.46/0.70          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.70          | ~ (v1_funct_1 @ X0)
% 0.46/0.70          | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.70      inference('sup-', [status(thm)], ['169', '178'])).
% 0.46/0.70  thf('180', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['39', '44', '47'])).
% 0.46/0.70  thf('181', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['39', '44', '47'])).
% 0.46/0.70  thf('182', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['39', '44', '47'])).
% 0.46/0.70  thf('183', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('184', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X0 @ 
% 0.46/0.70             (k1_zfmisc_1 @ 
% 0.46/0.70              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))
% 0.46/0.70          | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ X0)
% 0.46/0.70              != (k2_relat_1 @ sk_C))
% 0.46/0.70          | ~ (v2_funct_1 @ X0)
% 0.46/0.70          | (v2_funct_1 @ 
% 0.46/0.70             (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ X0))
% 0.46/0.70          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.46/0.70          | ~ (v1_funct_1 @ X0))),
% 0.46/0.70      inference('demod', [status(thm)], ['179', '180', '181', '182', '183'])).
% 0.46/0.70  thf('185', plain,
% 0.46/0.70      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.70        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.46/0.70        | (v2_funct_1 @ 
% 0.46/0.70           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.46/0.70        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.70        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70            != (k2_relat_1 @ sk_C)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['168', '184'])).
% 0.46/0.70  thf('186', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('187', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['118', '119'])).
% 0.46/0.70  thf('188', plain,
% 0.46/0.70      (![X24 : $i]:
% 0.46/0.70         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.70  thf('189', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('demod', [status(thm)], ['112', '113'])).
% 0.46/0.70  thf('190', plain,
% 0.46/0.70      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.46/0.70         (((k2_relset_1 @ X27 @ X26 @ X28) != (X26))
% 0.46/0.70          | ~ (v2_funct_1 @ X28)
% 0.46/0.70          | ((k2_tops_2 @ X27 @ X26 @ X28) = (k2_funct_1 @ X28))
% 0.46/0.70          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 0.46/0.70          | ~ (v1_funct_2 @ X28 @ X27 @ X26)
% 0.46/0.70          | ~ (v1_funct_1 @ X28))),
% 0.46/0.70      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.46/0.70  thf('191', plain,
% 0.46/0.70      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.70        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.46/0.70        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70            = (k2_funct_1 @ sk_C))
% 0.46/0.70        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.70        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70            != (u1_struct_0 @ sk_B)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['189', '190'])).
% 0.46/0.70  thf('192', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('193', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['118', '119'])).
% 0.46/0.70  thf('194', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('195', plain,
% 0.46/0.70      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70         = (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['123', '124'])).
% 0.46/0.70  thf('196', plain,
% 0.46/0.70      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70          = (k2_funct_1 @ sk_C))
% 0.46/0.70        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.46/0.70      inference('demod', [status(thm)], ['191', '192', '193', '194', '195'])).
% 0.46/0.70  thf('197', plain,
% 0.46/0.70      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.46/0.70        | ~ (l1_struct_0 @ sk_B)
% 0.46/0.70        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70            = (k2_funct_1 @ sk_C)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['188', '196'])).
% 0.46/0.70  thf('198', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['26', '27'])).
% 0.46/0.70  thf('199', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('200', plain,
% 0.46/0.70      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.46/0.70        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70            = (k2_funct_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['197', '198', '199'])).
% 0.46/0.70  thf('201', plain,
% 0.46/0.70      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70         = (k2_funct_1 @ sk_C))),
% 0.46/0.70      inference('simplify', [status(thm)], ['200'])).
% 0.46/0.70  thf('202', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('203', plain,
% 0.46/0.70      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.70         = (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['123', '124'])).
% 0.46/0.70  thf('204', plain,
% 0.46/0.70      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.70        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)],
% 0.46/0.70                ['185', '186', '187', '201', '202', '203'])).
% 0.46/0.70  thf('205', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.70      inference('simplify', [status(thm)], ['204'])).
% 0.46/0.70  thf('206', plain,
% 0.46/0.70      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.70          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.70        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['167', '205'])).
% 0.46/0.70  thf(t55_funct_1, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.70       ( ( v2_funct_1 @ A ) =>
% 0.46/0.70         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.46/0.70           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.46/0.70  thf('207', plain,
% 0.46/0.70      (![X4 : $i]:
% 0.46/0.70         (~ (v2_funct_1 @ X4)
% 0.46/0.70          | ((k1_relat_1 @ X4) = (k2_relat_1 @ (k2_funct_1 @ X4)))
% 0.46/0.70          | ~ (v1_funct_1 @ X4)
% 0.46/0.70          | ~ (v1_relat_1 @ X4))),
% 0.46/0.70      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.70  thf('208', plain,
% 0.46/0.70      (![X4 : $i]:
% 0.46/0.70         (~ (v2_funct_1 @ X4)
% 0.46/0.70          | ((k2_relat_1 @ X4) = (k1_relat_1 @ (k2_funct_1 @ X4)))
% 0.46/0.70          | ~ (v1_funct_1 @ X4)
% 0.46/0.70          | ~ (v1_relat_1 @ X4))),
% 0.46/0.70      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.70  thf('209', plain,
% 0.46/0.70      (![X5 : $i]:
% 0.46/0.70         (~ (v2_funct_1 @ X5)
% 0.46/0.70          | ((k2_funct_1 @ (k2_funct_1 @ X5)) = (X5))
% 0.46/0.70          | ~ (v1_funct_1 @ X5)
% 0.46/0.70          | ~ (v1_relat_1 @ X5))),
% 0.46/0.70      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.46/0.70  thf('210', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.70      inference('simplify', [status(thm)], ['204'])).
% 0.46/0.70  thf('211', plain,
% 0.46/0.70      (![X5 : $i]:
% 0.46/0.70         (~ (v2_funct_1 @ X5)
% 0.46/0.70          | ((k2_funct_1 @ (k2_funct_1 @ X5)) = (X5))
% 0.46/0.70          | ~ (v1_funct_1 @ X5)
% 0.46/0.70          | ~ (v1_relat_1 @ X5))),
% 0.46/0.70      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.46/0.70  thf('212', plain,
% 0.46/0.70      (![X4 : $i]:
% 0.46/0.70         (~ (v2_funct_1 @ X4)
% 0.46/0.70          | ((k1_relat_1 @ X4) = (k2_relat_1 @ (k2_funct_1 @ X4)))
% 0.46/0.70          | ~ (v1_funct_1 @ X4)
% 0.46/0.70          | ~ (v1_relat_1 @ X4))),
% 0.46/0.70      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.70  thf('213', plain,
% 0.46/0.70      (![X5 : $i]:
% 0.46/0.70         (~ (v2_funct_1 @ X5)
% 0.46/0.70          | ((k2_funct_1 @ (k2_funct_1 @ X5)) = (X5))
% 0.46/0.70          | ~ (v1_funct_1 @ X5)
% 0.46/0.70          | ~ (v1_relat_1 @ X5))),
% 0.46/0.70      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.46/0.70  thf('214', plain,
% 0.46/0.70      (![X4 : $i]:
% 0.46/0.70         (~ (v2_funct_1 @ X4)
% 0.46/0.70          | ((k2_relat_1 @ X4) = (k1_relat_1 @ (k2_funct_1 @ X4)))
% 0.46/0.70          | ~ (v1_funct_1 @ X4)
% 0.46/0.70          | ~ (v1_relat_1 @ X4))),
% 0.46/0.70      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.70  thf('215', plain,
% 0.46/0.70      (![X15 : $i, X16 : $i]:
% 0.46/0.70         (((k1_relat_1 @ X16) != (X15))
% 0.46/0.70          | (v1_partfun1 @ X16 @ X15)
% 0.46/0.70          | ~ (v4_relat_1 @ X16 @ X15)
% 0.46/0.70          | ~ (v1_relat_1 @ X16))),
% 0.46/0.70      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.46/0.70  thf('216', plain,
% 0.46/0.70      (![X16 : $i]:
% 0.46/0.70         (~ (v1_relat_1 @ X16)
% 0.46/0.70          | ~ (v4_relat_1 @ X16 @ (k1_relat_1 @ X16))
% 0.46/0.70          | (v1_partfun1 @ X16 @ (k1_relat_1 @ X16)))),
% 0.46/0.70      inference('simplify', [status(thm)], ['215'])).
% 0.46/0.70  thf('217', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.46/0.70          | ~ (v1_relat_1 @ X0)
% 0.46/0.70          | ~ (v1_funct_1 @ X0)
% 0.46/0.70          | ~ (v2_funct_1 @ X0)
% 0.46/0.70          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.70          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['214', '216'])).
% 0.46/0.70  thf('218', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.70          | ~ (v1_relat_1 @ X0)
% 0.46/0.70          | ~ (v1_funct_1 @ X0)
% 0.46/0.70          | ~ (v2_funct_1 @ X0)
% 0.46/0.70          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.46/0.70          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.46/0.70             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.46/0.70          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.70          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.70          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['213', '217'])).
% 0.46/0.70  thf('219', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.46/0.70          | ~ (v1_relat_1 @ X0)
% 0.46/0.70          | ~ (v1_funct_1 @ X0)
% 0.46/0.70          | ~ (v2_funct_1 @ X0)
% 0.46/0.70          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.70          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.70          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.70          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.46/0.70             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.46/0.70          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.46/0.70          | ~ (v2_funct_1 @ X0)
% 0.46/0.70          | ~ (v1_funct_1 @ X0)
% 0.46/0.70          | ~ (v1_relat_1 @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['212', '218'])).
% 0.46/0.70  thf('220', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.46/0.70          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.46/0.70             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.46/0.70          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.70          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.70          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.70          | ~ (v2_funct_1 @ X0)
% 0.46/0.70          | ~ (v1_funct_1 @ X0)
% 0.46/0.70          | ~ (v1_relat_1 @ X0)
% 0.46/0.70          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.46/0.70      inference('simplify', [status(thm)], ['219'])).
% 0.46/0.70  thf('221', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (v1_relat_1 @ X0)
% 0.46/0.70          | ~ (v1_relat_1 @ X0)
% 0.46/0.70          | ~ (v1_funct_1 @ X0)
% 0.46/0.70          | ~ (v2_funct_1 @ X0)
% 0.46/0.70          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.46/0.70          | ~ (v1_relat_1 @ X0)
% 0.46/0.70          | ~ (v1_funct_1 @ X0)
% 0.46/0.70          | ~ (v2_funct_1 @ X0)
% 0.46/0.70          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.70          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.70          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.70          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.46/0.70             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['211', '220'])).
% 0.46/0.70  thf('222', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.46/0.70           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.46/0.70          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.70          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.70          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.70          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.46/0.70          | ~ (v2_funct_1 @ X0)
% 0.46/0.70          | ~ (v1_funct_1 @ X0)
% 0.46/0.70          | ~ (v1_relat_1 @ X0))),
% 0.46/0.70      inference('simplify', [status(thm)], ['221'])).
% 0.46/0.70  thf('223', plain,
% 0.46/0.70      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.70        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.70        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.70        | ~ (v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.46/0.70        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.70        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.70        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.46/0.70           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['210', '222'])).
% 0.46/0.70  thf('224', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.70      inference('demod', [status(thm)], ['42', '43'])).
% 0.46/0.70  thf('225', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('226', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('227', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.46/0.70      inference('sup-', [status(thm)], ['61', '62'])).
% 0.46/0.70  thf('228', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['55', '56', '63'])).
% 0.46/0.70  thf('229', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['227', '228'])).
% 0.46/0.70  thf('230', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.46/0.70      inference('demod', [status(thm)], ['74', '75'])).
% 0.46/0.70  thf('231', plain,
% 0.46/0.70      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.70         (~ (v2_funct_1 @ X21)
% 0.46/0.70          | ((k2_relset_1 @ X23 @ X22 @ X21) != (X22))
% 0.46/0.70          | (m1_subset_1 @ (k2_funct_1 @ X21) @ 
% 0.46/0.70             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.46/0.70          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.46/0.70          | ~ (v1_funct_2 @ X21 @ X23 @ X22)
% 0.46/0.70          | ~ (v1_funct_1 @ X21))),
% 0.46/0.70      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.46/0.70  thf('232', plain,
% 0.46/0.70      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.70        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.46/0.70        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.70           (k1_zfmisc_1 @ 
% 0.46/0.70            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.46/0.70        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.70            != (k2_relat_1 @ sk_C))
% 0.46/0.70        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.70      inference('sup-', [status(thm)], ['230', '231'])).
% 0.46/0.70  thf('233', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('234', plain,
% 0.46/0.70      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['90', '91'])).
% 0.46/0.70  thf('235', plain,
% 0.46/0.70      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.46/0.70         = (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['105', '106'])).
% 0.46/0.70  thf('236', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('237', plain,
% 0.46/0.70      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.70         (k1_zfmisc_1 @ 
% 0.46/0.70          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.46/0.70        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['232', '233', '234', '235', '236'])).
% 0.46/0.70  thf('238', plain,
% 0.46/0.70      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.46/0.70      inference('simplify', [status(thm)], ['237'])).
% 0.46/0.70  thf('239', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.46/0.70          | (v1_relat_1 @ X0)
% 0.46/0.70          | ~ (v1_relat_1 @ X1))),
% 0.46/0.70      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.46/0.70  thf('240', plain,
% 0.46/0.70      ((~ (v1_relat_1 @ 
% 0.46/0.70           (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C)))
% 0.46/0.70        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['238', '239'])).
% 0.46/0.70  thf('241', plain,
% 0.46/0.70      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.46/0.70      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.46/0.70  thf('242', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['240', '241'])).
% 0.46/0.71  thf('243', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.71      inference('simplify', [status(thm)], ['147'])).
% 0.46/0.71  thf('244', plain,
% 0.46/0.71      ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.46/0.71        (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.71      inference('demod', [status(thm)],
% 0.46/0.71                ['223', '224', '225', '226', '229', '242', '243'])).
% 0.46/0.71  thf('245', plain,
% 0.46/0.71      (((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.46/0.71        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.71        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.71        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.71      inference('sup+', [status(thm)], ['209', '244'])).
% 0.46/0.71  thf('246', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.71      inference('demod', [status(thm)], ['42', '43'])).
% 0.46/0.71  thf('247', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('248', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('249', plain,
% 0.46/0.71      ((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.71      inference('demod', [status(thm)], ['245', '246', '247', '248'])).
% 0.46/0.71  thf('250', plain,
% 0.46/0.71      (((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.71        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.71        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.71        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.71      inference('sup+', [status(thm)], ['208', '249'])).
% 0.46/0.71  thf('251', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.71      inference('demod', [status(thm)], ['240', '241'])).
% 0.46/0.71  thf('252', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.71      inference('simplify', [status(thm)], ['147'])).
% 0.46/0.71  thf('253', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.71      inference('simplify', [status(thm)], ['204'])).
% 0.46/0.71  thf('254', plain,
% 0.46/0.71      ((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.71      inference('demod', [status(thm)], ['250', '251', '252', '253'])).
% 0.46/0.71  thf('255', plain,
% 0.46/0.71      (![X15 : $i, X16 : $i]:
% 0.46/0.71         (~ (v1_partfun1 @ X16 @ X15)
% 0.46/0.71          | ((k1_relat_1 @ X16) = (X15))
% 0.46/0.71          | ~ (v4_relat_1 @ X16 @ X15)
% 0.46/0.71          | ~ (v1_relat_1 @ X16))),
% 0.46/0.71      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.46/0.71  thf('256', plain,
% 0.46/0.71      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.71        | ~ (v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.71        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.71      inference('sup-', [status(thm)], ['254', '255'])).
% 0.46/0.71  thf('257', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.71      inference('demod', [status(thm)], ['42', '43'])).
% 0.46/0.71  thf('258', plain,
% 0.46/0.71      ((~ (v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.71        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.71      inference('demod', [status(thm)], ['256', '257'])).
% 0.46/0.71  thf('259', plain,
% 0.46/0.71      ((~ (v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.46/0.71        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.71        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.71        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.71        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.71      inference('sup-', [status(thm)], ['207', '258'])).
% 0.46/0.71  thf('260', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 0.46/0.71      inference('demod', [status(thm)], ['227', '228'])).
% 0.46/0.71  thf('261', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.71      inference('demod', [status(thm)], ['42', '43'])).
% 0.46/0.71  thf('262', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('263', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('264', plain,
% 0.46/0.71      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.71      inference('demod', [status(thm)], ['259', '260', '261', '262', '263'])).
% 0.46/0.71  thf('265', plain,
% 0.46/0.71      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.71          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.71        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))),
% 0.46/0.71      inference('demod', [status(thm)], ['206', '264'])).
% 0.46/0.71  thf('266', plain,
% 0.46/0.71      (((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.46/0.71         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.71      inference('simplify', [status(thm)], ['265'])).
% 0.46/0.71  thf('267', plain,
% 0.46/0.71      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.71          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 0.46/0.71      inference('demod', [status(thm)], ['110', '266'])).
% 0.46/0.71  thf('268', plain,
% 0.46/0.71      ((~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.71           sk_C)
% 0.46/0.71        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.71        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.71        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.71      inference('sup-', [status(thm)], ['0', '267'])).
% 0.46/0.71  thf('269', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_C @ 
% 0.46/0.71        (k1_zfmisc_1 @ 
% 0.46/0.71         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.71      inference('demod', [status(thm)], ['112', '113'])).
% 0.46/0.71  thf('270', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_C @ 
% 0.46/0.71        (k1_zfmisc_1 @ 
% 0.46/0.71         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.71      inference('demod', [status(thm)], ['112', '113'])).
% 0.46/0.71  thf(reflexivity_r2_funct_2, axiom,
% 0.46/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.71     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.46/0.71         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.46/0.71         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.71       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.46/0.71  thf('271', plain,
% 0.46/0.71      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.71         ((r2_funct_2 @ X17 @ X18 @ X19 @ X19)
% 0.46/0.71          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.46/0.71          | ~ (v1_funct_2 @ X19 @ X17 @ X18)
% 0.46/0.71          | ~ (v1_funct_1 @ X19)
% 0.46/0.71          | ~ (v1_funct_1 @ X20)
% 0.46/0.71          | ~ (v1_funct_2 @ X20 @ X17 @ X18)
% 0.46/0.71          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.46/0.71      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.46/0.71  thf('272', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (~ (m1_subset_1 @ X0 @ 
% 0.46/0.71             (k1_zfmisc_1 @ 
% 0.46/0.71              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.46/0.71          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.46/0.71          | ~ (v1_funct_1 @ X0)
% 0.46/0.71          | ~ (v1_funct_1 @ sk_C)
% 0.46/0.71          | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.46/0.71          | (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.71             sk_C))),
% 0.46/0.71      inference('sup-', [status(thm)], ['270', '271'])).
% 0.46/0.71  thf('273', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('274', plain,
% 0.46/0.71      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.46/0.71      inference('demod', [status(thm)], ['118', '119'])).
% 0.46/0.71  thf('275', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (~ (m1_subset_1 @ X0 @ 
% 0.46/0.71             (k1_zfmisc_1 @ 
% 0.46/0.71              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.46/0.71          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.46/0.71          | ~ (v1_funct_1 @ X0)
% 0.46/0.71          | (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.71             sk_C))),
% 0.46/0.71      inference('demod', [status(thm)], ['272', '273', '274'])).
% 0.46/0.71  thf('276', plain,
% 0.46/0.71      (((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 0.46/0.71        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.71        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['269', '275'])).
% 0.46/0.71  thf('277', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('278', plain,
% 0.46/0.71      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.46/0.71      inference('demod', [status(thm)], ['118', '119'])).
% 0.46/0.71  thf('279', plain,
% 0.46/0.71      ((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.46/0.71      inference('demod', [status(thm)], ['276', '277', '278'])).
% 0.46/0.71  thf('280', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.71      inference('demod', [status(thm)], ['42', '43'])).
% 0.46/0.71  thf('281', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('282', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('283', plain, ($false),
% 0.46/0.71      inference('demod', [status(thm)], ['268', '279', '280', '281', '282'])).
% 0.46/0.71  
% 0.46/0.71  % SZS output end Refutation
% 0.46/0.71  
% 0.46/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
