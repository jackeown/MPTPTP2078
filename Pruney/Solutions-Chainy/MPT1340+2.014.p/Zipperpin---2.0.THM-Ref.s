%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tAhNZXh6Le

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:07 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  295 (3962 expanded)
%              Number of leaves         :   38 (1154 expanded)
%              Depth                    :   43
%              Number of atoms          : 2602 (86700 expanded)
%              Number of equality atoms :  112 (2375 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X2 ) )
        = X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
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

thf('3',plain,(
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

thf('4',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('12',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('17',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( v1_partfun1 @ X12 @ X13 )
      | ~ ( v1_funct_2 @ X12 @ X13 @ X14 )
      | ~ ( v1_funct_1 @ X12 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('21',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('27',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('28',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','30'])).

thf('32',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('33',plain,(
    ! [X25: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('34',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['31','38'])).

thf('40',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['11','39'])).

thf('41',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('43',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_partfun1 @ X16 @ X15 )
      | ( ( k1_relat_1 @ X16 )
        = X15 )
      | ~ ( v4_relat_1 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('46',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('47',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('53',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('54',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','47','54'])).

thf('56',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','47','54'])).

thf('57',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['31','38'])).

thf('58',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_partfun1 @ X16 @ X15 )
      | ( ( k1_relat_1 @ X16 )
        = X15 )
      | ~ ( v4_relat_1 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('63',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','63'])).

thf('65',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['10','55','56','64'])).

thf('66',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('67',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('68',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','47','54'])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

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

thf('70',plain,(
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

thf('71',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
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
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','47','54'])).

thf('79',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('82',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('83',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','47','54'])).

thf('85',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['71','72','79','80','85'])).

thf('87',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['66','86'])).

thf('88',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('89',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['65','91'])).

thf('93',plain,
    ( ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','92'])).

thf('94',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('95',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('97',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('98',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('99',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('100',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('104',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','47','54'])).

thf('106',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['104','105'])).

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

thf('107',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X21 )
       != X22 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('108',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('111',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('112',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('116',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','47','54'])).

thf('118',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('120',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('121',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['119','124'])).

thf('126',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('129',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('130',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('131',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','47','54'])).

thf('132',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['108','109','118','132','133'])).

thf('135',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
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

thf('137',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('139',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('140',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X21 )
       != X22 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('141',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('144',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('145',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['141','142','143','144','145'])).

thf('147',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['138','146'])).

thf('148',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('149',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['147','148','149'])).

thf('151',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('153',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X21 )
       != X22 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X21 ) @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('154',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('157',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('158',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['154','155','156','157','158'])).

thf('160',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['137','151','160'])).

thf('162',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('163',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('164',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('165',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('167',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relat_1 @ X1 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('168',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X2 ) )
        = X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('171',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('172',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','47','54'])).

thf('173',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('175',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('176',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X2 ) )
        = X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('177',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relat_1 @ X1 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('178',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k1_relat_1 @ X16 )
       != X15 )
      | ( v1_partfun1 @ X16 @ X15 )
      | ~ ( v4_relat_1 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('179',plain,(
    ! [X16: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v4_relat_1 @ X16 @ ( k1_relat_1 @ X16 ) )
      | ( v1_partfun1 @ X16 @ ( k1_relat_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['177','179'])).

thf('181',plain,(
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
    inference('sup-',[status(thm)],['176','180'])).

thf('182',plain,(
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
    inference('sup-',[status(thm)],['175','181'])).

thf('183',plain,(
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
    inference(simplify,[status(thm)],['182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['174','183'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['184'])).

thf('186',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['173','185'])).

thf('187',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('188',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['186','187','188','189'])).

thf('191',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['150'])).

thf('192',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['190','191'])).

thf('193',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['170','192'])).

thf('194',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('195',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['193','194','195','196'])).

thf('198',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['169','197'])).

thf('199',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('200',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['198','199','200','201'])).

thf('203',plain,
    ( ( v1_partfun1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['168','202'])).

thf('204',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('205',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    v1_partfun1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['203','204','205','206'])).

thf('208',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['167','207'])).

thf('209',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['150'])).

thf('210',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['208','209'])).

thf('211',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('212',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('213',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['210','213'])).

thf('215',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['166','214'])).

thf('216',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('217',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['215','216','217','218'])).

thf('220',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_partfun1 @ X16 @ X15 )
      | ( ( k1_relat_1 @ X16 )
        = X15 )
      | ~ ( v4_relat_1 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('221',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['219','220'])).

thf('222',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('223',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['221','222'])).

thf('224',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['165','223'])).

thf('225',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['171','172'])).

thf('226',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('227',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['224','225','226','227','228'])).

thf('230',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['164','229'])).

thf('231',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['161','230'])).

thf('232',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['231'])).

thf('233',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['97','232'])).

thf('234',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('235',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['233','234','235','236'])).

thf('238',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['96','237'])).

thf('239',plain,
    ( ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','238'])).

thf('240',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('241',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['239','240','241','242'])).

thf('244',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('245',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf(reflexivity_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_funct_2 @ A @ B @ C @ C ) ) )).

thf('246',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_funct_2 @ X17 @ X18 @ X19 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( v1_funct_2 @ X19 @ X17 @ X18 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_2 @ X20 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('247',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['245','246'])).

thf('248',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('250',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['247','248','249'])).

thf('251',plain,
    ( ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['244','250'])).

thf('252',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('254',plain,(
    r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['251','252','253'])).

thf('255',plain,(
    $false ),
    inference(demod,[status(thm)],['243','254'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tAhNZXh6Le
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:35:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.45/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.64  % Solved by: fo/fo7.sh
% 0.45/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.64  % done 373 iterations in 0.185s
% 0.45/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.64  % SZS output start Refutation
% 0.45/0.64  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.45/0.64  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.45/0.64  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.45/0.64  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.45/0.64  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.64  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.64  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.45/0.64  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.64  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.45/0.64  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.45/0.64  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.64  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.64  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.45/0.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.64  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.45/0.64  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.45/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.64  thf(t65_funct_1, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.64       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.45/0.64  thf('0', plain,
% 0.45/0.64      (![X2 : $i]:
% 0.45/0.64         (~ (v2_funct_1 @ X2)
% 0.45/0.64          | ((k2_funct_1 @ (k2_funct_1 @ X2)) = (X2))
% 0.45/0.64          | ~ (v1_funct_1 @ X2)
% 0.45/0.64          | ~ (v1_relat_1 @ X2))),
% 0.45/0.64      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.45/0.64  thf(d3_struct_0, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.45/0.64  thf('1', plain,
% 0.45/0.64      (![X24 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('2', plain,
% 0.45/0.64      (![X24 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('3', plain,
% 0.45/0.64      (![X24 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf(t64_tops_2, conjecture,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( l1_struct_0 @ A ) =>
% 0.45/0.64       ( ![B:$i]:
% 0.45/0.64         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.45/0.64           ( ![C:$i]:
% 0.45/0.64             ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.64                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.64                 ( m1_subset_1 @
% 0.45/0.64                   C @ 
% 0.45/0.64                   ( k1_zfmisc_1 @
% 0.45/0.64                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.64               ( ( ( ( k2_relset_1 @
% 0.45/0.64                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.45/0.64                     ( k2_struct_0 @ B ) ) & 
% 0.45/0.64                   ( v2_funct_1 @ C ) ) =>
% 0.45/0.64                 ( r2_funct_2 @
% 0.45/0.64                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.45/0.64                   ( k2_tops_2 @
% 0.45/0.64                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.45/0.64                     ( k2_tops_2 @
% 0.45/0.64                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.45/0.64                   C ) ) ) ) ) ) ))).
% 0.45/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.64    (~( ![A:$i]:
% 0.45/0.64        ( ( l1_struct_0 @ A ) =>
% 0.45/0.64          ( ![B:$i]:
% 0.45/0.64            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.45/0.64              ( ![C:$i]:
% 0.45/0.64                ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.64                    ( v1_funct_2 @
% 0.45/0.64                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.64                    ( m1_subset_1 @
% 0.45/0.64                      C @ 
% 0.45/0.64                      ( k1_zfmisc_1 @
% 0.45/0.64                        ( k2_zfmisc_1 @
% 0.45/0.64                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.64                  ( ( ( ( k2_relset_1 @
% 0.45/0.64                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.45/0.64                        ( k2_struct_0 @ B ) ) & 
% 0.45/0.64                      ( v2_funct_1 @ C ) ) =>
% 0.45/0.64                    ( r2_funct_2 @
% 0.45/0.64                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.45/0.64                      ( k2_tops_2 @
% 0.45/0.64                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.45/0.64                        ( k2_tops_2 @
% 0.45/0.64                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.45/0.64                      C ) ) ) ) ) ) ) )),
% 0.45/0.64    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.45/0.64  thf('4', plain,
% 0.45/0.64      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.64          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.64           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.64          sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('5', plain,
% 0.45/0.64      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.64           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.64            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.64           sk_C)
% 0.45/0.64        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['3', '4'])).
% 0.45/0.64  thf('6', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('7', plain,
% 0.45/0.64      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.64          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.64           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.64          sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['5', '6'])).
% 0.45/0.64  thf('8', plain,
% 0.45/0.64      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.64           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.64            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.64           sk_C)
% 0.45/0.64        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['2', '7'])).
% 0.45/0.64  thf('9', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('10', plain,
% 0.45/0.64      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.64          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.64           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.64          sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['8', '9'])).
% 0.45/0.64  thf('11', plain,
% 0.45/0.64      (![X24 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('12', plain,
% 0.45/0.64      (![X24 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('13', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('14', plain,
% 0.45/0.64      (((m1_subset_1 @ sk_C @ 
% 0.45/0.64         (k1_zfmisc_1 @ 
% 0.45/0.64          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.45/0.64        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['12', '13'])).
% 0.45/0.64  thf('15', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('16', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.45/0.64      inference('demod', [status(thm)], ['14', '15'])).
% 0.45/0.64  thf(cc5_funct_2, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.45/0.64       ( ![C:$i]:
% 0.45/0.64         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.64           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.45/0.64             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.45/0.64  thf('17', plain,
% 0.45/0.64      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.45/0.64          | (v1_partfun1 @ X12 @ X13)
% 0.45/0.64          | ~ (v1_funct_2 @ X12 @ X13 @ X14)
% 0.45/0.64          | ~ (v1_funct_1 @ X12)
% 0.45/0.64          | (v1_xboole_0 @ X14))),
% 0.45/0.64      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.45/0.64  thf('18', plain,
% 0.45/0.64      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.45/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.45/0.64        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.64  thf('19', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('20', plain,
% 0.45/0.64      (![X24 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('21', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('22', plain,
% 0.45/0.64      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.45/0.64        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['20', '21'])).
% 0.45/0.64  thf('23', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('24', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['22', '23'])).
% 0.45/0.64  thf('25', plain,
% 0.45/0.64      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.45/0.64        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('demod', [status(thm)], ['18', '19', '24'])).
% 0.45/0.64  thf('26', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(redefinition_k2_relset_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.64       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.45/0.64  thf('27', plain,
% 0.45/0.64      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.64         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 0.45/0.64          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.45/0.64      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.64  thf('28', plain,
% 0.45/0.64      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64         = (k2_relat_1 @ sk_C))),
% 0.45/0.64      inference('sup-', [status(thm)], ['26', '27'])).
% 0.45/0.64  thf('29', plain,
% 0.45/0.64      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64         = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('30', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['28', '29'])).
% 0.45/0.64  thf('31', plain,
% 0.45/0.64      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.45/0.64        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('demod', [status(thm)], ['25', '30'])).
% 0.45/0.64  thf('32', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['28', '29'])).
% 0.45/0.64  thf(fc5_struct_0, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.45/0.64       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.45/0.64  thf('33', plain,
% 0.45/0.64      (![X25 : $i]:
% 0.45/0.64         (~ (v1_xboole_0 @ (k2_struct_0 @ X25))
% 0.45/0.64          | ~ (l1_struct_0 @ X25)
% 0.45/0.64          | (v2_struct_0 @ X25))),
% 0.45/0.64      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.45/0.64  thf('34', plain,
% 0.45/0.64      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.45/0.64        | (v2_struct_0 @ sk_B)
% 0.45/0.64        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup-', [status(thm)], ['32', '33'])).
% 0.45/0.64  thf('35', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('36', plain,
% 0.45/0.64      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['34', '35'])).
% 0.45/0.64  thf('37', plain, (~ (v2_struct_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('38', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.45/0.64      inference('clc', [status(thm)], ['36', '37'])).
% 0.45/0.64  thf('39', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.45/0.64      inference('clc', [status(thm)], ['31', '38'])).
% 0.45/0.64  thf('40', plain,
% 0.45/0.64      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.64      inference('sup+', [status(thm)], ['11', '39'])).
% 0.45/0.64  thf('41', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('42', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['40', '41'])).
% 0.45/0.64  thf(d4_partfun1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.45/0.64       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.45/0.64  thf('43', plain,
% 0.45/0.64      (![X15 : $i, X16 : $i]:
% 0.45/0.64         (~ (v1_partfun1 @ X16 @ X15)
% 0.45/0.64          | ((k1_relat_1 @ X16) = (X15))
% 0.45/0.64          | ~ (v4_relat_1 @ X16 @ X15)
% 0.45/0.64          | ~ (v1_relat_1 @ X16))),
% 0.45/0.64      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.45/0.64  thf('44', plain,
% 0.45/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.64        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.45/0.64        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['42', '43'])).
% 0.45/0.64  thf('45', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(cc1_relset_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.64       ( v1_relat_1 @ C ) ))).
% 0.45/0.64  thf('46', plain,
% 0.45/0.64      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.45/0.64         ((v1_relat_1 @ X3)
% 0.45/0.64          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.45/0.64      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.45/0.64  thf('47', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.64      inference('sup-', [status(thm)], ['45', '46'])).
% 0.45/0.64  thf('48', plain,
% 0.45/0.64      (![X24 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('49', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('50', plain,
% 0.45/0.64      (((m1_subset_1 @ sk_C @ 
% 0.45/0.64         (k1_zfmisc_1 @ 
% 0.45/0.64          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.45/0.64        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.64      inference('sup+', [status(thm)], ['48', '49'])).
% 0.45/0.64  thf('51', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('52', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('demod', [status(thm)], ['50', '51'])).
% 0.45/0.64  thf(cc2_relset_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.64       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.45/0.64  thf('53', plain,
% 0.45/0.64      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.45/0.64         ((v4_relat_1 @ X6 @ X7)
% 0.45/0.64          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.45/0.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.64  thf('54', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['52', '53'])).
% 0.45/0.64  thf('55', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['44', '47', '54'])).
% 0.45/0.64  thf('56', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['44', '47', '54'])).
% 0.45/0.64  thf('57', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.45/0.64      inference('clc', [status(thm)], ['31', '38'])).
% 0.45/0.64  thf('58', plain,
% 0.45/0.64      (![X15 : $i, X16 : $i]:
% 0.45/0.64         (~ (v1_partfun1 @ X16 @ X15)
% 0.45/0.64          | ((k1_relat_1 @ X16) = (X15))
% 0.45/0.64          | ~ (v4_relat_1 @ X16 @ X15)
% 0.45/0.64          | ~ (v1_relat_1 @ X16))),
% 0.45/0.64      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.45/0.64  thf('59', plain,
% 0.45/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.64        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.45/0.64        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['57', '58'])).
% 0.45/0.64  thf('60', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.64      inference('sup-', [status(thm)], ['45', '46'])).
% 0.45/0.64  thf('61', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('62', plain,
% 0.45/0.64      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.45/0.64         ((v4_relat_1 @ X6 @ X7)
% 0.45/0.64          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.45/0.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.64  thf('63', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['61', '62'])).
% 0.45/0.64  thf('64', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['59', '60', '63'])).
% 0.45/0.64  thf('65', plain,
% 0.45/0.64      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.64          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.64           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.64          sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['10', '55', '56', '64'])).
% 0.45/0.64  thf('66', plain,
% 0.45/0.64      (![X24 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('67', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('demod', [status(thm)], ['50', '51'])).
% 0.45/0.64  thf('68', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['44', '47', '54'])).
% 0.45/0.64  thf('69', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('demod', [status(thm)], ['67', '68'])).
% 0.45/0.64  thf(d4_tops_2, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.64       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.45/0.64         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.45/0.64  thf('70', plain,
% 0.45/0.64      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.45/0.64         (((k2_relset_1 @ X27 @ X26 @ X28) != (X26))
% 0.45/0.64          | ~ (v2_funct_1 @ X28)
% 0.45/0.64          | ((k2_tops_2 @ X27 @ X26 @ X28) = (k2_funct_1 @ X28))
% 0.45/0.64          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 0.45/0.64          | ~ (v1_funct_2 @ X28 @ X27 @ X26)
% 0.45/0.64          | ~ (v1_funct_1 @ X28))),
% 0.45/0.64      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.45/0.64  thf('71', plain,
% 0.45/0.64      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.45/0.64        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64            = (k2_funct_1 @ sk_C))
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.64        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64            != (u1_struct_0 @ sk_B)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['69', '70'])).
% 0.45/0.64  thf('72', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('73', plain,
% 0.45/0.64      (![X24 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('74', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('75', plain,
% 0.45/0.64      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.64        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.64      inference('sup+', [status(thm)], ['73', '74'])).
% 0.45/0.64  thf('76', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('77', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['75', '76'])).
% 0.45/0.64  thf('78', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['44', '47', '54'])).
% 0.45/0.64  thf('79', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['77', '78'])).
% 0.45/0.64  thf('80', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('81', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('demod', [status(thm)], ['50', '51'])).
% 0.45/0.64  thf('82', plain,
% 0.45/0.64      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.64         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 0.45/0.64          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.45/0.64      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.64  thf('83', plain,
% 0.45/0.64      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64         = (k2_relat_1 @ sk_C))),
% 0.45/0.64      inference('sup-', [status(thm)], ['81', '82'])).
% 0.45/0.64  thf('84', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['44', '47', '54'])).
% 0.45/0.64  thf('85', plain,
% 0.45/0.64      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64         = (k2_relat_1 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['83', '84'])).
% 0.45/0.64  thf('86', plain,
% 0.45/0.64      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64          = (k2_funct_1 @ sk_C))
% 0.45/0.64        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.45/0.64      inference('demod', [status(thm)], ['71', '72', '79', '80', '85'])).
% 0.45/0.64  thf('87', plain,
% 0.45/0.64      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.45/0.64        | ~ (l1_struct_0 @ sk_B)
% 0.45/0.64        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64            = (k2_funct_1 @ sk_C)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['66', '86'])).
% 0.45/0.64  thf('88', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['28', '29'])).
% 0.45/0.64  thf('89', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('90', plain,
% 0.45/0.64      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.45/0.64        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64            = (k2_funct_1 @ sk_C)))),
% 0.45/0.64      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.45/0.64  thf('91', plain,
% 0.45/0.64      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64         = (k2_funct_1 @ sk_C))),
% 0.45/0.64      inference('simplify', [status(thm)], ['90'])).
% 0.45/0.64  thf('92', plain,
% 0.45/0.64      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.64          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.64           (k2_funct_1 @ sk_C)) @ 
% 0.45/0.64          sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['65', '91'])).
% 0.45/0.64  thf('93', plain,
% 0.45/0.64      ((~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.64           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.64            (k2_funct_1 @ sk_C)) @ 
% 0.45/0.64           sk_C)
% 0.45/0.64        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup-', [status(thm)], ['1', '92'])).
% 0.45/0.64  thf('94', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['28', '29'])).
% 0.45/0.64  thf('95', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('96', plain,
% 0.45/0.64      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.64          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.64           (k2_funct_1 @ sk_C)) @ 
% 0.45/0.64          sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.45/0.64  thf(fc6_funct_1, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.45/0.64       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.45/0.64         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.45/0.64         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.45/0.64  thf('97', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0))),
% 0.45/0.64      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.45/0.64  thf('98', plain,
% 0.45/0.64      (![X24 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('99', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('demod', [status(thm)], ['50', '51'])).
% 0.45/0.64  thf('100', plain,
% 0.45/0.64      (((m1_subset_1 @ sk_C @ 
% 0.45/0.64         (k1_zfmisc_1 @ 
% 0.45/0.64          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.45/0.64        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['98', '99'])).
% 0.45/0.64  thf('101', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('102', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.45/0.64      inference('demod', [status(thm)], ['100', '101'])).
% 0.45/0.64  thf('103', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['28', '29'])).
% 0.45/0.64  thf('104', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.45/0.64      inference('demod', [status(thm)], ['102', '103'])).
% 0.45/0.64  thf('105', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['44', '47', '54'])).
% 0.45/0.64  thf('106', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.45/0.64      inference('demod', [status(thm)], ['104', '105'])).
% 0.45/0.64  thf(t31_funct_2, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.64       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.45/0.64         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.45/0.64           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.45/0.64           ( m1_subset_1 @
% 0.45/0.64             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.45/0.64  thf('107', plain,
% 0.45/0.64      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.45/0.64         (~ (v2_funct_1 @ X21)
% 0.45/0.64          | ((k2_relset_1 @ X23 @ X22 @ X21) != (X22))
% 0.45/0.64          | (m1_subset_1 @ (k2_funct_1 @ X21) @ 
% 0.45/0.64             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.45/0.64          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.45/0.64          | ~ (v1_funct_2 @ X21 @ X23 @ X22)
% 0.45/0.64          | ~ (v1_funct_1 @ X21))),
% 0.45/0.64      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.45/0.64  thf('108', plain,
% 0.45/0.64      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.45/0.64        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.64           (k1_zfmisc_1 @ 
% 0.45/0.64            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.45/0.64        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.64            != (k2_relat_1 @ sk_C))
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.64      inference('sup-', [status(thm)], ['106', '107'])).
% 0.45/0.64  thf('109', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('110', plain,
% 0.45/0.64      (![X24 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('111', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['75', '76'])).
% 0.45/0.64  thf('112', plain,
% 0.45/0.64      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.45/0.64        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['110', '111'])).
% 0.45/0.64  thf('113', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('114', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['112', '113'])).
% 0.45/0.64  thf('115', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['28', '29'])).
% 0.45/0.64  thf('116', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['114', '115'])).
% 0.45/0.64  thf('117', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['44', '47', '54'])).
% 0.45/0.64  thf('118', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['116', '117'])).
% 0.45/0.64  thf('119', plain,
% 0.45/0.64      (![X24 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('120', plain,
% 0.45/0.64      (![X24 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('121', plain,
% 0.45/0.64      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64         = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('122', plain,
% 0.45/0.64      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64          = (k2_struct_0 @ sk_B))
% 0.45/0.64        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.64      inference('sup+', [status(thm)], ['120', '121'])).
% 0.45/0.64  thf('123', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('124', plain,
% 0.45/0.64      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64         = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['122', '123'])).
% 0.45/0.64  thf('125', plain,
% 0.45/0.64      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64          = (k2_struct_0 @ sk_B))
% 0.45/0.64        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['119', '124'])).
% 0.45/0.64  thf('126', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('127', plain,
% 0.45/0.64      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64         = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['125', '126'])).
% 0.45/0.64  thf('128', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['28', '29'])).
% 0.45/0.64  thf('129', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['28', '29'])).
% 0.45/0.64  thf('130', plain,
% 0.45/0.64      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.64         = (k2_relat_1 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['127', '128', '129'])).
% 0.45/0.64  thf('131', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['44', '47', '54'])).
% 0.45/0.64  thf('132', plain,
% 0.45/0.64      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.64         = (k2_relat_1 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['130', '131'])).
% 0.45/0.64  thf('133', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('134', plain,
% 0.45/0.64      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.64         (k1_zfmisc_1 @ 
% 0.45/0.64          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.45/0.64        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.45/0.64      inference('demod', [status(thm)], ['108', '109', '118', '132', '133'])).
% 0.45/0.64  thf('135', plain,
% 0.45/0.64      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.45/0.64      inference('simplify', [status(thm)], ['134'])).
% 0.45/0.64  thf('136', plain,
% 0.45/0.64      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.45/0.64         (((k2_relset_1 @ X27 @ X26 @ X28) != (X26))
% 0.45/0.64          | ~ (v2_funct_1 @ X28)
% 0.45/0.64          | ((k2_tops_2 @ X27 @ X26 @ X28) = (k2_funct_1 @ X28))
% 0.45/0.64          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 0.45/0.64          | ~ (v1_funct_2 @ X28 @ X27 @ X26)
% 0.45/0.64          | ~ (v1_funct_1 @ X28))),
% 0.45/0.64      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.45/0.64  thf('137', plain,
% 0.45/0.64      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.45/0.64             (k1_relat_1 @ sk_C))
% 0.45/0.64        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.64            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.64            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['135', '136'])).
% 0.45/0.64  thf('138', plain,
% 0.45/0.64      (![X24 : $i]:
% 0.45/0.64         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.64  thf('139', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('demod', [status(thm)], ['67', '68'])).
% 0.45/0.64  thf('140', plain,
% 0.45/0.64      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.45/0.64         (~ (v2_funct_1 @ X21)
% 0.45/0.64          | ((k2_relset_1 @ X23 @ X22 @ X21) != (X22))
% 0.45/0.64          | (v1_funct_1 @ (k2_funct_1 @ X21))
% 0.45/0.64          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.45/0.64          | ~ (v1_funct_2 @ X21 @ X23 @ X22)
% 0.45/0.64          | ~ (v1_funct_1 @ X21))),
% 0.45/0.64      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.45/0.64  thf('141', plain,
% 0.45/0.64      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.45/0.64        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64            != (u1_struct_0 @ sk_B))
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.64      inference('sup-', [status(thm)], ['139', '140'])).
% 0.45/0.64  thf('142', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('143', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['77', '78'])).
% 0.45/0.64  thf('144', plain,
% 0.45/0.64      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.64         = (k2_relat_1 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['83', '84'])).
% 0.45/0.64  thf('145', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('146', plain,
% 0.45/0.64      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.45/0.64      inference('demod', [status(thm)], ['141', '142', '143', '144', '145'])).
% 0.45/0.64  thf('147', plain,
% 0.45/0.64      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.45/0.64        | ~ (l1_struct_0 @ sk_B)
% 0.45/0.64        | (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['138', '146'])).
% 0.45/0.64  thf('148', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['28', '29'])).
% 0.45/0.64  thf('149', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('150', plain,
% 0.45/0.64      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.45/0.64        | (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.64      inference('demod', [status(thm)], ['147', '148', '149'])).
% 0.45/0.64  thf('151', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.64      inference('simplify', [status(thm)], ['150'])).
% 0.45/0.64  thf('152', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.45/0.64      inference('demod', [status(thm)], ['104', '105'])).
% 0.45/0.64  thf('153', plain,
% 0.45/0.64      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.45/0.64         (~ (v2_funct_1 @ X21)
% 0.45/0.64          | ((k2_relset_1 @ X23 @ X22 @ X21) != (X22))
% 0.45/0.64          | (v1_funct_2 @ (k2_funct_1 @ X21) @ X22 @ X23)
% 0.45/0.64          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.45/0.64          | ~ (v1_funct_2 @ X21 @ X23 @ X22)
% 0.45/0.64          | ~ (v1_funct_1 @ X21))),
% 0.45/0.64      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.45/0.64  thf('154', plain,
% 0.45/0.64      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.45/0.64        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.45/0.64           (k1_relat_1 @ sk_C))
% 0.45/0.64        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.64            != (k2_relat_1 @ sk_C))
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.64      inference('sup-', [status(thm)], ['152', '153'])).
% 0.45/0.64  thf('155', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('156', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['116', '117'])).
% 0.45/0.64  thf('157', plain,
% 0.45/0.64      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.64         = (k2_relat_1 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['130', '131'])).
% 0.45/0.64  thf('158', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('159', plain,
% 0.45/0.64      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.45/0.64         (k1_relat_1 @ sk_C))
% 0.45/0.64        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.45/0.64      inference('demod', [status(thm)], ['154', '155', '156', '157', '158'])).
% 0.45/0.64  thf('160', plain,
% 0.45/0.64      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.45/0.64        (k1_relat_1 @ sk_C))),
% 0.45/0.64      inference('simplify', [status(thm)], ['159'])).
% 0.45/0.64  thf('161', plain,
% 0.45/0.64      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.64          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.64            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.45/0.64      inference('demod', [status(thm)], ['137', '151', '160'])).
% 0.45/0.64  thf('162', plain,
% 0.45/0.64      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.45/0.64      inference('simplify', [status(thm)], ['134'])).
% 0.45/0.64  thf('163', plain,
% 0.45/0.64      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.64         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 0.45/0.64          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.45/0.64      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.64  thf('164', plain,
% 0.45/0.64      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.64         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['162', '163'])).
% 0.45/0.64  thf(t55_funct_1, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.64       ( ( v2_funct_1 @ A ) =>
% 0.45/0.64         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.45/0.64           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.45/0.64  thf('165', plain,
% 0.45/0.64      (![X1 : $i]:
% 0.45/0.64         (~ (v2_funct_1 @ X1)
% 0.45/0.64          | ((k1_relat_1 @ X1) = (k2_relat_1 @ (k2_funct_1 @ X1)))
% 0.45/0.64          | ~ (v1_funct_1 @ X1)
% 0.45/0.64          | ~ (v1_relat_1 @ X1))),
% 0.45/0.64      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.45/0.64  thf('166', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0))),
% 0.45/0.64      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.45/0.64  thf('167', plain,
% 0.45/0.64      (![X1 : $i]:
% 0.45/0.64         (~ (v2_funct_1 @ X1)
% 0.45/0.64          | ((k2_relat_1 @ X1) = (k1_relat_1 @ (k2_funct_1 @ X1)))
% 0.45/0.64          | ~ (v1_funct_1 @ X1)
% 0.45/0.64          | ~ (v1_relat_1 @ X1))),
% 0.45/0.64      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.45/0.64  thf('168', plain,
% 0.45/0.64      (![X2 : $i]:
% 0.45/0.64         (~ (v2_funct_1 @ X2)
% 0.45/0.64          | ((k2_funct_1 @ (k2_funct_1 @ X2)) = (X2))
% 0.45/0.64          | ~ (v1_funct_1 @ X2)
% 0.45/0.64          | ~ (v1_relat_1 @ X2))),
% 0.45/0.64      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.45/0.64  thf('169', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0))),
% 0.45/0.64      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.45/0.64  thf('170', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0))),
% 0.45/0.64      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.45/0.64  thf('171', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['52', '53'])).
% 0.45/0.64  thf('172', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.64      inference('demod', [status(thm)], ['44', '47', '54'])).
% 0.45/0.64  thf('173', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['171', '172'])).
% 0.45/0.64  thf('174', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0))),
% 0.45/0.64      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.45/0.64  thf('175', plain,
% 0.45/0.64      (![X1 : $i]:
% 0.45/0.64         (~ (v2_funct_1 @ X1)
% 0.45/0.64          | ((k1_relat_1 @ X1) = (k2_relat_1 @ (k2_funct_1 @ X1)))
% 0.45/0.64          | ~ (v1_funct_1 @ X1)
% 0.45/0.64          | ~ (v1_relat_1 @ X1))),
% 0.45/0.64      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.45/0.64  thf('176', plain,
% 0.45/0.64      (![X2 : $i]:
% 0.45/0.64         (~ (v2_funct_1 @ X2)
% 0.45/0.64          | ((k2_funct_1 @ (k2_funct_1 @ X2)) = (X2))
% 0.45/0.64          | ~ (v1_funct_1 @ X2)
% 0.45/0.64          | ~ (v1_relat_1 @ X2))),
% 0.45/0.64      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.45/0.64  thf('177', plain,
% 0.45/0.64      (![X1 : $i]:
% 0.45/0.64         (~ (v2_funct_1 @ X1)
% 0.45/0.64          | ((k2_relat_1 @ X1) = (k1_relat_1 @ (k2_funct_1 @ X1)))
% 0.45/0.64          | ~ (v1_funct_1 @ X1)
% 0.45/0.64          | ~ (v1_relat_1 @ X1))),
% 0.45/0.64      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.45/0.64  thf('178', plain,
% 0.45/0.64      (![X15 : $i, X16 : $i]:
% 0.45/0.64         (((k1_relat_1 @ X16) != (X15))
% 0.45/0.64          | (v1_partfun1 @ X16 @ X15)
% 0.45/0.64          | ~ (v4_relat_1 @ X16 @ X15)
% 0.45/0.64          | ~ (v1_relat_1 @ X16))),
% 0.45/0.64      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.45/0.64  thf('179', plain,
% 0.45/0.64      (![X16 : $i]:
% 0.45/0.64         (~ (v1_relat_1 @ X16)
% 0.45/0.64          | ~ (v4_relat_1 @ X16 @ (k1_relat_1 @ X16))
% 0.45/0.64          | (v1_partfun1 @ X16 @ (k1_relat_1 @ X16)))),
% 0.45/0.64      inference('simplify', [status(thm)], ['178'])).
% 0.45/0.64  thf('180', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.45/0.64          | ~ (v1_relat_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.45/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['177', '179'])).
% 0.45/0.64  thf('181', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.45/0.64          | ~ (v1_relat_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.45/0.64          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.45/0.64             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.45/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['176', '180'])).
% 0.45/0.64  thf('182', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.45/0.64          | ~ (v1_relat_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.45/0.64             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.45/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['175', '181'])).
% 0.45/0.64  thf('183', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.45/0.64          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.45/0.64             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.45/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0)
% 0.45/0.64          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.45/0.64      inference('simplify', [status(thm)], ['182'])).
% 0.45/0.64  thf('184', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.45/0.64          | ~ (v1_relat_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.45/0.64             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['174', '183'])).
% 0.45/0.64  thf('185', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.45/0.64           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.45/0.64          | ~ (v2_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0)
% 0.45/0.64          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.45/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.45/0.64      inference('simplify', [status(thm)], ['184'])).
% 0.45/0.64  thf('186', plain,
% 0.45/0.64      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.64        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.45/0.64           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['173', '185'])).
% 0.45/0.64  thf('187', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.64      inference('sup-', [status(thm)], ['45', '46'])).
% 0.45/0.64  thf('188', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('189', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('190', plain,
% 0.45/0.64      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.45/0.64           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.45/0.64      inference('demod', [status(thm)], ['186', '187', '188', '189'])).
% 0.45/0.64  thf('191', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.64      inference('simplify', [status(thm)], ['150'])).
% 0.45/0.64  thf('192', plain,
% 0.45/0.64      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.45/0.64           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.45/0.64      inference('demod', [status(thm)], ['190', '191'])).
% 0.45/0.64  thf('193', plain,
% 0.45/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.64        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.45/0.64           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.45/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['170', '192'])).
% 0.45/0.64  thf('194', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.64      inference('sup-', [status(thm)], ['45', '46'])).
% 0.45/0.64  thf('195', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('196', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('197', plain,
% 0.45/0.64      (((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.45/0.64         (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.45/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.64      inference('demod', [status(thm)], ['193', '194', '195', '196'])).
% 0.45/0.64  thf('198', plain,
% 0.45/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.64        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.45/0.64           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['169', '197'])).
% 0.45/0.64  thf('199', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.64      inference('sup-', [status(thm)], ['45', '46'])).
% 0.45/0.64  thf('200', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('201', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('202', plain,
% 0.45/0.64      ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.45/0.64        (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.64      inference('demod', [status(thm)], ['198', '199', '200', '201'])).
% 0.45/0.64  thf('203', plain,
% 0.45/0.64      (((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.45/0.64        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.64      inference('sup+', [status(thm)], ['168', '202'])).
% 0.45/0.64  thf('204', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.64      inference('sup-', [status(thm)], ['45', '46'])).
% 0.45/0.64  thf('205', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('206', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('207', plain,
% 0.45/0.64      ((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.64      inference('demod', [status(thm)], ['203', '204', '205', '206'])).
% 0.45/0.64  thf('208', plain,
% 0.45/0.64      (((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.64        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.64      inference('sup+', [status(thm)], ['167', '207'])).
% 0.45/0.64  thf('209', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.64      inference('simplify', [status(thm)], ['150'])).
% 0.45/0.64  thf('210', plain,
% 0.45/0.64      (((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.64        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.64      inference('demod', [status(thm)], ['208', '209'])).
% 0.45/0.64  thf('211', plain,
% 0.45/0.64      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.45/0.64      inference('simplify', [status(thm)], ['134'])).
% 0.45/0.64  thf('212', plain,
% 0.45/0.64      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.45/0.64         ((v1_relat_1 @ X3)
% 0.45/0.64          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.45/0.64      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.45/0.64  thf('213', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.64      inference('sup-', [status(thm)], ['211', '212'])).
% 0.45/0.64  thf('214', plain,
% 0.45/0.64      (((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.64      inference('demod', [status(thm)], ['210', '213'])).
% 0.45/0.64  thf('215', plain,
% 0.45/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.64        | (v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['166', '214'])).
% 0.45/0.64  thf('216', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.64      inference('sup-', [status(thm)], ['45', '46'])).
% 0.45/0.64  thf('217', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('218', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('219', plain,
% 0.45/0.64      ((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.64      inference('demod', [status(thm)], ['215', '216', '217', '218'])).
% 0.45/0.64  thf('220', plain,
% 0.45/0.64      (![X15 : $i, X16 : $i]:
% 0.45/0.64         (~ (v1_partfun1 @ X16 @ X15)
% 0.45/0.64          | ((k1_relat_1 @ X16) = (X15))
% 0.45/0.64          | ~ (v4_relat_1 @ X16 @ X15)
% 0.45/0.64          | ~ (v1_relat_1 @ X16))),
% 0.45/0.64      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.45/0.64  thf('221', plain,
% 0.45/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.64        | ~ (v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.64        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['219', '220'])).
% 0.45/0.64  thf('222', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.64      inference('sup-', [status(thm)], ['45', '46'])).
% 0.45/0.64  thf('223', plain,
% 0.45/0.64      ((~ (v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.64        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.64      inference('demod', [status(thm)], ['221', '222'])).
% 0.45/0.64  thf('224', plain,
% 0.45/0.64      ((~ (v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.45/0.64        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.64        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['165', '223'])).
% 0.45/0.64  thf('225', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['171', '172'])).
% 0.45/0.64  thf('226', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.64      inference('sup-', [status(thm)], ['45', '46'])).
% 0.45/0.64  thf('227', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('228', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('229', plain,
% 0.45/0.64      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.64      inference('demod', [status(thm)], ['224', '225', '226', '227', '228'])).
% 0.45/0.64  thf('230', plain,
% 0.45/0.64      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.64         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['164', '229'])).
% 0.45/0.64  thf('231', plain,
% 0.45/0.64      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.64          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))),
% 0.45/0.64      inference('demod', [status(thm)], ['161', '230'])).
% 0.45/0.64  thf('232', plain,
% 0.45/0.64      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.64        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.64            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.64      inference('simplify', [status(thm)], ['231'])).
% 0.45/0.64  thf('233', plain,
% 0.45/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.64        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.64            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['97', '232'])).
% 0.45/0.64  thf('234', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.64      inference('sup-', [status(thm)], ['45', '46'])).
% 0.45/0.64  thf('235', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('236', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('237', plain,
% 0.45/0.64      (((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.64         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.64      inference('demod', [status(thm)], ['233', '234', '235', '236'])).
% 0.45/0.64  thf('238', plain,
% 0.45/0.64      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.64          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['96', '237'])).
% 0.45/0.64  thf('239', plain,
% 0.45/0.64      ((~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.45/0.64           sk_C)
% 0.45/0.64        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.64      inference('sup-', [status(thm)], ['0', '238'])).
% 0.45/0.64  thf('240', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.64      inference('sup-', [status(thm)], ['45', '46'])).
% 0.45/0.64  thf('241', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('242', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('243', plain,
% 0.45/0.64      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['239', '240', '241', '242'])).
% 0.45/0.64  thf('244', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('demod', [status(thm)], ['67', '68'])).
% 0.45/0.64  thf('245', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_C @ 
% 0.45/0.64        (k1_zfmisc_1 @ 
% 0.45/0.64         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.64      inference('demod', [status(thm)], ['67', '68'])).
% 0.45/0.64  thf(reflexivity_r2_funct_2, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.64     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.45/0.64         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.45/0.64         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.64       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.45/0.64  thf('246', plain,
% 0.45/0.64      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.64         ((r2_funct_2 @ X17 @ X18 @ X19 @ X19)
% 0.45/0.64          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.45/0.64          | ~ (v1_funct_2 @ X19 @ X17 @ X18)
% 0.45/0.64          | ~ (v1_funct_1 @ X19)
% 0.45/0.64          | ~ (v1_funct_1 @ X20)
% 0.45/0.64          | ~ (v1_funct_2 @ X20 @ X17 @ X18)
% 0.45/0.64          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.45/0.64      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.45/0.64  thf('247', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X0 @ 
% 0.45/0.64             (k1_zfmisc_1 @ 
% 0.45/0.64              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.45/0.64          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | ~ (v1_funct_1 @ sk_C)
% 0.45/0.64          | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.45/0.64          | (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.45/0.64             sk_C))),
% 0.45/0.64      inference('sup-', [status(thm)], ['245', '246'])).
% 0.45/0.64  thf('248', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('249', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['77', '78'])).
% 0.45/0.64  thf('250', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X0 @ 
% 0.45/0.64             (k1_zfmisc_1 @ 
% 0.45/0.64              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.45/0.64          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.45/0.64          | ~ (v1_funct_1 @ X0)
% 0.45/0.64          | (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.45/0.64             sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['247', '248', '249'])).
% 0.45/0.64  thf('251', plain,
% 0.45/0.64      (((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 0.45/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.64        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['244', '250'])).
% 0.45/0.64  thf('252', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('253', plain,
% 0.45/0.64      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.45/0.64      inference('demod', [status(thm)], ['77', '78'])).
% 0.45/0.64  thf('254', plain,
% 0.45/0.64      ((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.45/0.64      inference('demod', [status(thm)], ['251', '252', '253'])).
% 0.45/0.64  thf('255', plain, ($false), inference('demod', [status(thm)], ['243', '254'])).
% 0.45/0.64  
% 0.45/0.64  % SZS output end Refutation
% 0.45/0.64  
% 0.45/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
