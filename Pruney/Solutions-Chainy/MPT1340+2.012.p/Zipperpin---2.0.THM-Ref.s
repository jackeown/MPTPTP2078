%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4HmTOUgcOu

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:07 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  304 (8341 expanded)
%              Number of leaves         :   38 (2389 expanded)
%              Depth                    :   35
%              Number of atoms          : 2944 (181358 expanded)
%              Number of equality atoms :  138 (5192 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('0',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X1 ) )
        = X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
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
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
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

thf('11',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('14',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['11','16','17'])).

thf('19',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('20',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('27',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( v1_partfun1 @ X11 @ X12 )
      | ~ ( v1_funct_2 @ X11 @ X12 @ X13 )
      | ~ ( v1_funct_1 @ X11 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('28',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('31',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('36',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29','36'])).

thf('38',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('39',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('40',plain,(
    ! [X24: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['38','42'])).

thf('44',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['37','47'])).

thf('49',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['19','48'])).

thf('50',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('52',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_partfun1 @ X15 @ X14 )
      | ( ( k1_relat_1 @ X15 )
        = X14 )
      | ~ ( v4_relat_1 @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('53',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('55',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('56',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
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

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('62',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('63',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','56','63'])).

thf('65',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','56','63'])).

thf('66',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['37','47'])).

thf('67',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_partfun1 @ X15 @ X14 )
      | ( ( k1_relat_1 @ X15 )
        = X14 )
      | ~ ( v4_relat_1 @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('68',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['54','55'])).

thf('70',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('72',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69','72'])).

thf('74',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('76',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','56','63'])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

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

thf('78',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X25 @ X27 )
       != X25 )
      | ~ ( v2_funct_1 @ X27 )
      | ( ( k2_tops_2 @ X26 @ X25 @ X27 )
        = ( k2_funct_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('79',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
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
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','56','63'])).

thf('87',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('90',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('91',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','56','63'])).

thf('93',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['79','80','87','88','93'])).

thf('95',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['74','94'])).

thf('96',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('97',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['18','64','65','73','99'])).

thf('101',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('102',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('103',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('107',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','56','63'])).

thf('109',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

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

thf('110',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_relset_1 @ X22 @ X21 @ X20 )
       != X21 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X22 @ X21 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('111',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('114',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('115',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('119',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','56','63'])).

thf('121',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('123',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('124',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['122','127'])).

thf('129',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('132',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('133',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('134',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','56','63'])).

thf('135',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['111','112','121','135','136'])).

thf('138',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X25 @ X27 )
       != X25 )
      | ~ ( v2_funct_1 @ X27 )
      | ( ( k2_tops_2 @ X26 @ X25 @ X27 )
        = ( k2_funct_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('140',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('142',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('143',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_relset_1 @ X22 @ X21 @ X20 )
       != X21 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X22 @ X21 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('144',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('147',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('148',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['144','145','146','147','148'])).

thf('150',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['141','149'])).

thf('151',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('152',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['150','151','152'])).

thf('154',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('156',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_relset_1 @ X22 @ X21 @ X20 )
       != X21 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X20 ) @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X22 @ X21 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('157',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('160',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('161',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['157','158','159','160','161'])).

thf('163',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['140','154','163'])).

thf('165',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('166',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('167',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['164','167'])).

thf('169',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('170',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','56','63'])).

thf('171',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('172',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('173',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
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

thf('174',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( l1_struct_0 @ X28 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) @ X30 )
       != ( k2_struct_0 @ X28 ) )
      | ~ ( v2_funct_1 @ X30 )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t63_tops_2])).

thf('175',plain,(
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
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
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
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,(
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
    inference('sup-',[status(thm)],['172','176'])).

thf('178',plain,(
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
    inference(simplify,[status(thm)],['177'])).

thf('179',plain,(
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
    inference('sup-',[status(thm)],['171','178'])).

thf('180',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ X0 ) @ ( k2_relat_1 @ sk_C ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 )
       != ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['179','180','181'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X0 )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X0 ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['170','182'])).

thf('184',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69','72'])).

thf('185',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69','72'])).

thf('186',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69','72'])).

thf('187',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ X0 )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ X0 ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['183','184','185','186','187'])).

thf('189',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['169','188'])).

thf('190',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('192',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['98'])).

thf('193',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('195',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['189','190','191','192','193','194'])).

thf('196',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['195'])).

thf('197',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['168','196'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('198',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('199',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('200',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X1 ) )
        = X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('201',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['195'])).

thf('202',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X1 ) )
        = X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('203',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('204',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X1 ) )
        = X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('205',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('206',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k1_relat_1 @ X15 )
       != X14 )
      | ( v1_partfun1 @ X15 @ X14 )
      | ~ ( v4_relat_1 @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('207',plain,(
    ! [X15: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v4_relat_1 @ X15 @ ( k1_relat_1 @ X15 ) )
      | ( v1_partfun1 @ X15 @ ( k1_relat_1 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['206'])).

thf('208',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['205','207'])).

thf('209',plain,(
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
    inference('sup-',[status(thm)],['204','208'])).

thf('210',plain,(
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
    inference('sup-',[status(thm)],['203','209'])).

thf('211',plain,(
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
    inference(simplify,[status(thm)],['210'])).

thf('212',plain,(
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
    inference('sup-',[status(thm)],['202','211'])).

thf('213',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['212'])).

thf('214',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['201','213'])).

thf('215',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['54','55'])).

thf('216',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('219',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','56','63'])).

thf('220',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['218','219'])).

thf('221',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('222',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('223',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['221','222'])).

thf('224',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['153'])).

thf('225',plain,(
    v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['214','215','216','217','220','223','224'])).

thf('226',plain,
    ( ( v1_partfun1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['200','225'])).

thf('227',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['54','55'])).

thf('228',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    v1_partfun1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['226','227','228','229'])).

thf('231',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['199','230'])).

thf('232',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['221','222'])).

thf('233',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['153'])).

thf('234',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['195'])).

thf('235',plain,(
    v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['231','232','233','234'])).

thf('236',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_partfun1 @ X15 @ X14 )
      | ( ( k1_relat_1 @ X15 )
        = X14 )
      | ~ ( v4_relat_1 @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('237',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['235','236'])).

thf('238',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['54','55'])).

thf('239',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['237','238'])).

thf('240',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['198','239'])).

thf('241',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['218','219'])).

thf('242',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['54','55'])).

thf('243',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['240','241','242','243','244'])).

thf('246',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['197','245'])).

thf('247',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['246'])).

thf('248',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['100','247'])).

thf('249',plain,
    ( ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','248'])).

thf('250',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('251',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf(reflexivity_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_funct_2 @ A @ B @ C @ C ) ) )).

thf('252',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( r2_funct_2 @ X16 @ X17 @ X18 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X16 @ X17 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_2 @ X19 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('253',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['251','252'])).

thf('254',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('256',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['253','254','255'])).

thf('257',plain,
    ( ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['250','256'])).

thf('258',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('260',plain,(
    r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['257','258','259'])).

thf('261',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['54','55'])).

thf('262',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,(
    $false ),
    inference(demod,[status(thm)],['249','260','261','262','263'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4HmTOUgcOu
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:12:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.36/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.62  % Solved by: fo/fo7.sh
% 0.36/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.62  % done 354 iterations in 0.157s
% 0.36/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.62  % SZS output start Refutation
% 0.36/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.62  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.36/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.62  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.36/0.62  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.36/0.62  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.36/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.62  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.36/0.62  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.36/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.62  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.36/0.62  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.36/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.62  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.62  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.36/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.62  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.36/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.62  thf(t65_funct_1, axiom,
% 0.36/0.62    (![A:$i]:
% 0.36/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.36/0.62       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.36/0.62  thf('0', plain,
% 0.36/0.62      (![X1 : $i]:
% 0.36/0.62         (~ (v2_funct_1 @ X1)
% 0.36/0.62          | ((k2_funct_1 @ (k2_funct_1 @ X1)) = (X1))
% 0.36/0.62          | ~ (v1_funct_1 @ X1)
% 0.36/0.62          | ~ (v1_relat_1 @ X1))),
% 0.36/0.62      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.36/0.62  thf(d3_struct_0, axiom,
% 0.36/0.62    (![A:$i]:
% 0.36/0.62     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.36/0.62  thf('1', plain,
% 0.36/0.62      (![X23 : $i]:
% 0.36/0.62         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.36/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.62  thf('2', plain,
% 0.36/0.62      (![X23 : $i]:
% 0.36/0.62         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.36/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.62  thf('3', plain,
% 0.36/0.62      (![X23 : $i]:
% 0.36/0.62         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.36/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.62  thf(t64_tops_2, conjecture,
% 0.36/0.62    (![A:$i]:
% 0.36/0.62     ( ( l1_struct_0 @ A ) =>
% 0.36/0.62       ( ![B:$i]:
% 0.36/0.62         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.36/0.62           ( ![C:$i]:
% 0.36/0.62             ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.62                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.62                 ( m1_subset_1 @
% 0.36/0.62                   C @ 
% 0.36/0.62                   ( k1_zfmisc_1 @
% 0.36/0.62                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.62               ( ( ( ( k2_relset_1 @
% 0.36/0.62                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.36/0.62                     ( k2_struct_0 @ B ) ) & 
% 0.36/0.62                   ( v2_funct_1 @ C ) ) =>
% 0.36/0.62                 ( r2_funct_2 @
% 0.36/0.62                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.36/0.62                   ( k2_tops_2 @
% 0.36/0.62                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.36/0.62                     ( k2_tops_2 @
% 0.36/0.62                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.36/0.62                   C ) ) ) ) ) ) ))).
% 0.36/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.62    (~( ![A:$i]:
% 0.36/0.62        ( ( l1_struct_0 @ A ) =>
% 0.36/0.62          ( ![B:$i]:
% 0.36/0.62            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.36/0.62              ( ![C:$i]:
% 0.36/0.62                ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.62                    ( v1_funct_2 @
% 0.36/0.62                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.62                    ( m1_subset_1 @
% 0.36/0.62                      C @ 
% 0.36/0.62                      ( k1_zfmisc_1 @
% 0.36/0.62                        ( k2_zfmisc_1 @
% 0.36/0.62                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.62                  ( ( ( ( k2_relset_1 @
% 0.36/0.62                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.36/0.62                        ( k2_struct_0 @ B ) ) & 
% 0.36/0.62                      ( v2_funct_1 @ C ) ) =>
% 0.36/0.62                    ( r2_funct_2 @
% 0.36/0.62                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.36/0.62                      ( k2_tops_2 @
% 0.36/0.62                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.36/0.62                        ( k2_tops_2 @
% 0.36/0.62                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.36/0.62                      C ) ) ) ) ) ) ) )),
% 0.36/0.62    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.36/0.62  thf('4', plain,
% 0.36/0.62      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.62          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.62           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.36/0.62          sk_C)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('5', plain,
% 0.36/0.62      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.62           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.62            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.36/0.62           sk_C)
% 0.36/0.62        | ~ (l1_struct_0 @ sk_A))),
% 0.36/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.36/0.62  thf('6', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('7', plain,
% 0.36/0.62      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.62          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.62           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.36/0.62          sk_C)),
% 0.36/0.62      inference('demod', [status(thm)], ['5', '6'])).
% 0.36/0.62  thf('8', plain,
% 0.36/0.62      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.62           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.36/0.62            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.36/0.62           sk_C)
% 0.36/0.62        | ~ (l1_struct_0 @ sk_A))),
% 0.36/0.62      inference('sup-', [status(thm)], ['2', '7'])).
% 0.36/0.62  thf('9', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('10', plain,
% 0.36/0.62      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.62          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.36/0.62           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.36/0.62          sk_C)),
% 0.36/0.62      inference('demod', [status(thm)], ['8', '9'])).
% 0.36/0.62  thf('11', plain,
% 0.36/0.62      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.62           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.36/0.62            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.36/0.62           sk_C)
% 0.36/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.36/0.62      inference('sup-', [status(thm)], ['1', '10'])).
% 0.36/0.62  thf('12', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_C @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf(redefinition_k2_relset_1, axiom,
% 0.36/0.62    (![A:$i,B:$i,C:$i]:
% 0.36/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.62       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.36/0.62  thf('13', plain,
% 0.36/0.62      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.36/0.62         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 0.36/0.62          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.36/0.62      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.36/0.62  thf('14', plain,
% 0.36/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.62         = (k2_relat_1 @ sk_C))),
% 0.36/0.62      inference('sup-', [status(thm)], ['12', '13'])).
% 0.36/0.62  thf('15', plain,
% 0.36/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.62         = (k2_struct_0 @ sk_B))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('16', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.36/0.62  thf('17', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('18', plain,
% 0.36/0.62      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.62          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.36/0.62           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.36/0.62          sk_C)),
% 0.36/0.62      inference('demod', [status(thm)], ['11', '16', '17'])).
% 0.36/0.62  thf('19', plain,
% 0.36/0.62      (![X23 : $i]:
% 0.36/0.62         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.36/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.62  thf('20', plain,
% 0.36/0.62      (![X23 : $i]:
% 0.36/0.62         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.36/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.62  thf('21', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_C @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('22', plain,
% 0.36/0.62      (((m1_subset_1 @ sk_C @ 
% 0.36/0.62         (k1_zfmisc_1 @ 
% 0.36/0.62          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.36/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.36/0.62      inference('sup+', [status(thm)], ['20', '21'])).
% 0.36/0.62  thf('23', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('24', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_C @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.36/0.62      inference('demod', [status(thm)], ['22', '23'])).
% 0.36/0.62  thf('25', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.36/0.62  thf('26', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_C @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.36/0.62      inference('demod', [status(thm)], ['24', '25'])).
% 0.36/0.62  thf(cc5_funct_2, axiom,
% 0.36/0.62    (![A:$i,B:$i]:
% 0.36/0.62     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.36/0.62       ( ![C:$i]:
% 0.36/0.62         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.62           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.36/0.62             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.36/0.62  thf('27', plain,
% 0.36/0.62      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.36/0.62         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.36/0.62          | (v1_partfun1 @ X11 @ X12)
% 0.36/0.62          | ~ (v1_funct_2 @ X11 @ X12 @ X13)
% 0.36/0.62          | ~ (v1_funct_1 @ X11)
% 0.36/0.62          | (v1_xboole_0 @ X13))),
% 0.36/0.62      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.36/0.62  thf('28', plain,
% 0.36/0.62      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.36/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.36/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.36/0.62        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['26', '27'])).
% 0.36/0.62  thf('29', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('30', plain,
% 0.36/0.62      (![X23 : $i]:
% 0.36/0.62         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.36/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.62  thf('31', plain,
% 0.36/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('32', plain,
% 0.36/0.62      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.36/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.36/0.62      inference('sup+', [status(thm)], ['30', '31'])).
% 0.36/0.62  thf('33', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('34', plain,
% 0.36/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.36/0.62      inference('demod', [status(thm)], ['32', '33'])).
% 0.36/0.62  thf('35', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.36/0.62  thf('36', plain,
% 0.36/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.36/0.62      inference('demod', [status(thm)], ['34', '35'])).
% 0.36/0.62  thf('37', plain,
% 0.36/0.62      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.36/0.62        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.36/0.62      inference('demod', [status(thm)], ['28', '29', '36'])).
% 0.36/0.62  thf('38', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.36/0.62  thf('39', plain,
% 0.36/0.62      (![X23 : $i]:
% 0.36/0.62         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.36/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.62  thf(fc2_struct_0, axiom,
% 0.36/0.62    (![A:$i]:
% 0.36/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.36/0.62       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.36/0.62  thf('40', plain,
% 0.36/0.62      (![X24 : $i]:
% 0.36/0.62         (~ (v1_xboole_0 @ (u1_struct_0 @ X24))
% 0.36/0.62          | ~ (l1_struct_0 @ X24)
% 0.36/0.62          | (v2_struct_0 @ X24))),
% 0.36/0.62      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.36/0.62  thf('41', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.36/0.62          | ~ (l1_struct_0 @ X0)
% 0.36/0.62          | (v2_struct_0 @ X0)
% 0.36/0.62          | ~ (l1_struct_0 @ X0))),
% 0.36/0.62      inference('sup-', [status(thm)], ['39', '40'])).
% 0.36/0.62  thf('42', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         ((v2_struct_0 @ X0)
% 0.36/0.62          | ~ (l1_struct_0 @ X0)
% 0.36/0.62          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.36/0.62      inference('simplify', [status(thm)], ['41'])).
% 0.36/0.62  thf('43', plain,
% 0.36/0.62      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.36/0.62        | ~ (l1_struct_0 @ sk_B)
% 0.36/0.62        | (v2_struct_0 @ sk_B))),
% 0.36/0.62      inference('sup-', [status(thm)], ['38', '42'])).
% 0.36/0.62  thf('44', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('45', plain,
% 0.36/0.62      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.36/0.62      inference('demod', [status(thm)], ['43', '44'])).
% 0.36/0.62  thf('46', plain, (~ (v2_struct_0 @ sk_B)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('47', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.36/0.62      inference('clc', [status(thm)], ['45', '46'])).
% 0.36/0.62  thf('48', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.36/0.62      inference('clc', [status(thm)], ['37', '47'])).
% 0.36/0.62  thf('49', plain,
% 0.36/0.62      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.36/0.62      inference('sup+', [status(thm)], ['19', '48'])).
% 0.36/0.62  thf('50', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('51', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.36/0.62      inference('demod', [status(thm)], ['49', '50'])).
% 0.36/0.62  thf(d4_partfun1, axiom,
% 0.36/0.62    (![A:$i,B:$i]:
% 0.36/0.62     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.36/0.62       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.36/0.62  thf('52', plain,
% 0.36/0.62      (![X14 : $i, X15 : $i]:
% 0.36/0.62         (~ (v1_partfun1 @ X15 @ X14)
% 0.36/0.62          | ((k1_relat_1 @ X15) = (X14))
% 0.36/0.62          | ~ (v4_relat_1 @ X15 @ X14)
% 0.36/0.62          | ~ (v1_relat_1 @ X15))),
% 0.36/0.62      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.36/0.62  thf('53', plain,
% 0.36/0.62      ((~ (v1_relat_1 @ sk_C)
% 0.36/0.62        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.36/0.62        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['51', '52'])).
% 0.36/0.62  thf('54', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_C @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf(cc1_relset_1, axiom,
% 0.36/0.62    (![A:$i,B:$i,C:$i]:
% 0.36/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.62       ( v1_relat_1 @ C ) ))).
% 0.36/0.62  thf('55', plain,
% 0.36/0.62      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.62         ((v1_relat_1 @ X2)
% 0.36/0.62          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.36/0.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.36/0.62  thf('56', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.62      inference('sup-', [status(thm)], ['54', '55'])).
% 0.36/0.62  thf('57', plain,
% 0.36/0.62      (![X23 : $i]:
% 0.36/0.62         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.36/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.62  thf('58', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_C @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('59', plain,
% 0.36/0.62      (((m1_subset_1 @ sk_C @ 
% 0.36/0.62         (k1_zfmisc_1 @ 
% 0.36/0.62          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.36/0.62        | ~ (l1_struct_0 @ sk_A))),
% 0.36/0.62      inference('sup+', [status(thm)], ['57', '58'])).
% 0.36/0.62  thf('60', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('61', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_C @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.62      inference('demod', [status(thm)], ['59', '60'])).
% 0.36/0.62  thf(cc2_relset_1, axiom,
% 0.36/0.62    (![A:$i,B:$i,C:$i]:
% 0.36/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.62       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.36/0.62  thf('62', plain,
% 0.36/0.62      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.36/0.62         ((v4_relat_1 @ X5 @ X6)
% 0.36/0.62          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.36/0.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.36/0.62  thf('63', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.36/0.62      inference('sup-', [status(thm)], ['61', '62'])).
% 0.36/0.62  thf('64', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.36/0.62      inference('demod', [status(thm)], ['53', '56', '63'])).
% 0.36/0.62  thf('65', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.36/0.62      inference('demod', [status(thm)], ['53', '56', '63'])).
% 0.36/0.62  thf('66', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.36/0.62      inference('clc', [status(thm)], ['37', '47'])).
% 0.36/0.62  thf('67', plain,
% 0.36/0.62      (![X14 : $i, X15 : $i]:
% 0.36/0.62         (~ (v1_partfun1 @ X15 @ X14)
% 0.36/0.62          | ((k1_relat_1 @ X15) = (X14))
% 0.36/0.62          | ~ (v4_relat_1 @ X15 @ X14)
% 0.36/0.62          | ~ (v1_relat_1 @ X15))),
% 0.36/0.62      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.36/0.62  thf('68', plain,
% 0.36/0.62      ((~ (v1_relat_1 @ sk_C)
% 0.36/0.62        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.36/0.62        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['66', '67'])).
% 0.36/0.62  thf('69', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.62      inference('sup-', [status(thm)], ['54', '55'])).
% 0.36/0.62  thf('70', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_C @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('71', plain,
% 0.36/0.62      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.36/0.62         ((v4_relat_1 @ X5 @ X6)
% 0.36/0.62          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.36/0.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.36/0.62  thf('72', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.36/0.62      inference('sup-', [status(thm)], ['70', '71'])).
% 0.36/0.62  thf('73', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.36/0.62      inference('demod', [status(thm)], ['68', '69', '72'])).
% 0.36/0.62  thf('74', plain,
% 0.36/0.62      (![X23 : $i]:
% 0.36/0.62         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.36/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.62  thf('75', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_C @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.62      inference('demod', [status(thm)], ['59', '60'])).
% 0.36/0.62  thf('76', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.36/0.62      inference('demod', [status(thm)], ['53', '56', '63'])).
% 0.36/0.62  thf('77', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_C @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.62      inference('demod', [status(thm)], ['75', '76'])).
% 0.36/0.62  thf(d4_tops_2, axiom,
% 0.36/0.62    (![A:$i,B:$i,C:$i]:
% 0.36/0.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.36/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.62       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.36/0.62         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.36/0.62  thf('78', plain,
% 0.36/0.62      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.36/0.62         (((k2_relset_1 @ X26 @ X25 @ X27) != (X25))
% 0.36/0.62          | ~ (v2_funct_1 @ X27)
% 0.36/0.62          | ((k2_tops_2 @ X26 @ X25 @ X27) = (k2_funct_1 @ X27))
% 0.36/0.62          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 0.36/0.62          | ~ (v1_funct_2 @ X27 @ X26 @ X25)
% 0.36/0.62          | ~ (v1_funct_1 @ X27))),
% 0.36/0.62      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.36/0.62  thf('79', plain,
% 0.36/0.62      ((~ (v1_funct_1 @ sk_C)
% 0.36/0.62        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.36/0.62        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.62            = (k2_funct_1 @ sk_C))
% 0.36/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.36/0.62        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.62            != (u1_struct_0 @ sk_B)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['77', '78'])).
% 0.36/0.62  thf('80', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('81', plain,
% 0.36/0.62      (![X23 : $i]:
% 0.36/0.62         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.36/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.62  thf('82', plain,
% 0.36/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('83', plain,
% 0.36/0.62      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.36/0.62        | ~ (l1_struct_0 @ sk_A))),
% 0.36/0.62      inference('sup+', [status(thm)], ['81', '82'])).
% 0.36/0.62  thf('84', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('85', plain,
% 0.36/0.62      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.36/0.62      inference('demod', [status(thm)], ['83', '84'])).
% 0.36/0.62  thf('86', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.36/0.62      inference('demod', [status(thm)], ['53', '56', '63'])).
% 0.36/0.62  thf('87', plain,
% 0.36/0.62      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.36/0.62      inference('demod', [status(thm)], ['85', '86'])).
% 0.36/0.62  thf('88', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('89', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_C @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.62      inference('demod', [status(thm)], ['59', '60'])).
% 0.36/0.62  thf('90', plain,
% 0.36/0.62      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.36/0.62         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 0.36/0.62          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.36/0.62      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.36/0.62  thf('91', plain,
% 0.36/0.62      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.62         = (k2_relat_1 @ sk_C))),
% 0.36/0.62      inference('sup-', [status(thm)], ['89', '90'])).
% 0.36/0.62  thf('92', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.36/0.62      inference('demod', [status(thm)], ['53', '56', '63'])).
% 0.36/0.62  thf('93', plain,
% 0.36/0.62      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.62         = (k2_relat_1 @ sk_C))),
% 0.36/0.62      inference('demod', [status(thm)], ['91', '92'])).
% 0.36/0.62  thf('94', plain,
% 0.36/0.62      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.62          = (k2_funct_1 @ sk_C))
% 0.36/0.62        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.36/0.62      inference('demod', [status(thm)], ['79', '80', '87', '88', '93'])).
% 0.36/0.62  thf('95', plain,
% 0.36/0.62      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.36/0.62        | ~ (l1_struct_0 @ sk_B)
% 0.36/0.62        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.62            = (k2_funct_1 @ sk_C)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['74', '94'])).
% 0.36/0.62  thf('96', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.36/0.62  thf('97', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('98', plain,
% 0.36/0.62      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.36/0.62        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.62            = (k2_funct_1 @ sk_C)))),
% 0.36/0.62      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.36/0.62  thf('99', plain,
% 0.36/0.62      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.62         = (k2_funct_1 @ sk_C))),
% 0.36/0.62      inference('simplify', [status(thm)], ['98'])).
% 0.36/0.62  thf('100', plain,
% 0.36/0.62      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.62          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.36/0.62           (k2_funct_1 @ sk_C)) @ 
% 0.36/0.62          sk_C)),
% 0.36/0.62      inference('demod', [status(thm)], ['18', '64', '65', '73', '99'])).
% 0.36/0.62  thf('101', plain,
% 0.36/0.62      (![X23 : $i]:
% 0.36/0.62         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.36/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.62  thf('102', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_C @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.62      inference('demod', [status(thm)], ['59', '60'])).
% 0.36/0.62  thf('103', plain,
% 0.36/0.62      (((m1_subset_1 @ sk_C @ 
% 0.36/0.62         (k1_zfmisc_1 @ 
% 0.36/0.62          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.36/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.36/0.62      inference('sup+', [status(thm)], ['101', '102'])).
% 0.36/0.62  thf('104', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('105', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_C @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.36/0.62      inference('demod', [status(thm)], ['103', '104'])).
% 0.36/0.62  thf('106', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.36/0.62  thf('107', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_C @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.36/0.62      inference('demod', [status(thm)], ['105', '106'])).
% 0.36/0.62  thf('108', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.36/0.62      inference('demod', [status(thm)], ['53', '56', '63'])).
% 0.36/0.62  thf('109', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_C @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.36/0.62      inference('demod', [status(thm)], ['107', '108'])).
% 0.36/0.62  thf(t31_funct_2, axiom,
% 0.36/0.62    (![A:$i,B:$i,C:$i]:
% 0.36/0.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.36/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.62       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.36/0.62         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.36/0.62           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.36/0.62           ( m1_subset_1 @
% 0.36/0.62             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.36/0.62  thf('110', plain,
% 0.36/0.62      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.36/0.62         (~ (v2_funct_1 @ X20)
% 0.36/0.62          | ((k2_relset_1 @ X22 @ X21 @ X20) != (X21))
% 0.36/0.62          | (m1_subset_1 @ (k2_funct_1 @ X20) @ 
% 0.36/0.62             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.36/0.62          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21)))
% 0.36/0.62          | ~ (v1_funct_2 @ X20 @ X22 @ X21)
% 0.36/0.62          | ~ (v1_funct_1 @ X20))),
% 0.36/0.62      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.36/0.62  thf('111', plain,
% 0.36/0.62      ((~ (v1_funct_1 @ sk_C)
% 0.36/0.62        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.36/0.62        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.62           (k1_zfmisc_1 @ 
% 0.36/0.62            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.36/0.62        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.36/0.62            != (k2_relat_1 @ sk_C))
% 0.36/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.36/0.62      inference('sup-', [status(thm)], ['109', '110'])).
% 0.36/0.62  thf('112', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('113', plain,
% 0.36/0.62      (![X23 : $i]:
% 0.36/0.62         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.36/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.62  thf('114', plain,
% 0.36/0.62      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.36/0.62      inference('demod', [status(thm)], ['83', '84'])).
% 0.36/0.62  thf('115', plain,
% 0.36/0.62      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.36/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.36/0.62      inference('sup+', [status(thm)], ['113', '114'])).
% 0.36/0.62  thf('116', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('117', plain,
% 0.36/0.62      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.36/0.62      inference('demod', [status(thm)], ['115', '116'])).
% 0.36/0.62  thf('118', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.36/0.62  thf('119', plain,
% 0.36/0.62      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.36/0.62      inference('demod', [status(thm)], ['117', '118'])).
% 0.36/0.62  thf('120', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.36/0.62      inference('demod', [status(thm)], ['53', '56', '63'])).
% 0.36/0.62  thf('121', plain,
% 0.36/0.62      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.36/0.62      inference('demod', [status(thm)], ['119', '120'])).
% 0.36/0.62  thf('122', plain,
% 0.36/0.62      (![X23 : $i]:
% 0.36/0.62         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.36/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.62  thf('123', plain,
% 0.36/0.62      (![X23 : $i]:
% 0.36/0.62         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.36/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.62  thf('124', plain,
% 0.36/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.62         = (k2_struct_0 @ sk_B))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('125', plain,
% 0.36/0.62      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.62          = (k2_struct_0 @ sk_B))
% 0.36/0.62        | ~ (l1_struct_0 @ sk_A))),
% 0.36/0.62      inference('sup+', [status(thm)], ['123', '124'])).
% 0.36/0.62  thf('126', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('127', plain,
% 0.36/0.62      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.62         = (k2_struct_0 @ sk_B))),
% 0.36/0.62      inference('demod', [status(thm)], ['125', '126'])).
% 0.36/0.62  thf('128', plain,
% 0.36/0.62      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.36/0.62          = (k2_struct_0 @ sk_B))
% 0.36/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.36/0.62      inference('sup+', [status(thm)], ['122', '127'])).
% 0.36/0.62  thf('129', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('130', plain,
% 0.36/0.62      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.36/0.62         = (k2_struct_0 @ sk_B))),
% 0.36/0.62      inference('demod', [status(thm)], ['128', '129'])).
% 0.36/0.62  thf('131', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.36/0.62  thf('132', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.36/0.62  thf('133', plain,
% 0.36/0.62      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.36/0.62         = (k2_relat_1 @ sk_C))),
% 0.36/0.62      inference('demod', [status(thm)], ['130', '131', '132'])).
% 0.36/0.62  thf('134', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.36/0.62      inference('demod', [status(thm)], ['53', '56', '63'])).
% 0.36/0.62  thf('135', plain,
% 0.36/0.62      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.36/0.62         = (k2_relat_1 @ sk_C))),
% 0.36/0.62      inference('demod', [status(thm)], ['133', '134'])).
% 0.36/0.62  thf('136', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('137', plain,
% 0.36/0.62      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.62         (k1_zfmisc_1 @ 
% 0.36/0.62          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.36/0.62        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.36/0.62      inference('demod', [status(thm)], ['111', '112', '121', '135', '136'])).
% 0.36/0.62  thf('138', plain,
% 0.36/0.62      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.36/0.62      inference('simplify', [status(thm)], ['137'])).
% 0.36/0.62  thf('139', plain,
% 0.36/0.62      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.36/0.62         (((k2_relset_1 @ X26 @ X25 @ X27) != (X25))
% 0.36/0.62          | ~ (v2_funct_1 @ X27)
% 0.36/0.62          | ((k2_tops_2 @ X26 @ X25 @ X27) = (k2_funct_1 @ X27))
% 0.36/0.62          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 0.36/0.62          | ~ (v1_funct_2 @ X27 @ X26 @ X25)
% 0.36/0.62          | ~ (v1_funct_1 @ X27))),
% 0.36/0.62      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.36/0.62  thf('140', plain,
% 0.36/0.62      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.36/0.62        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.36/0.62             (k1_relat_1 @ sk_C))
% 0.36/0.62        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.36/0.62            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.36/0.62        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.36/0.62        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.36/0.62            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['138', '139'])).
% 0.36/0.62  thf('141', plain,
% 0.36/0.62      (![X23 : $i]:
% 0.36/0.62         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.36/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.62  thf('142', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_C @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.62      inference('demod', [status(thm)], ['75', '76'])).
% 0.36/0.62  thf('143', plain,
% 0.36/0.62      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.36/0.62         (~ (v2_funct_1 @ X20)
% 0.36/0.62          | ((k2_relset_1 @ X22 @ X21 @ X20) != (X21))
% 0.36/0.62          | (v1_funct_1 @ (k2_funct_1 @ X20))
% 0.36/0.62          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21)))
% 0.36/0.62          | ~ (v1_funct_2 @ X20 @ X22 @ X21)
% 0.36/0.62          | ~ (v1_funct_1 @ X20))),
% 0.36/0.62      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.36/0.62  thf('144', plain,
% 0.36/0.62      ((~ (v1_funct_1 @ sk_C)
% 0.36/0.62        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.36/0.62        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.36/0.62        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.62            != (u1_struct_0 @ sk_B))
% 0.36/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.36/0.62      inference('sup-', [status(thm)], ['142', '143'])).
% 0.36/0.62  thf('145', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('146', plain,
% 0.36/0.62      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.36/0.62      inference('demod', [status(thm)], ['85', '86'])).
% 0.36/0.62  thf('147', plain,
% 0.36/0.62      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.62         = (k2_relat_1 @ sk_C))),
% 0.36/0.62      inference('demod', [status(thm)], ['91', '92'])).
% 0.36/0.62  thf('148', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('149', plain,
% 0.36/0.62      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.36/0.62        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.36/0.62      inference('demod', [status(thm)], ['144', '145', '146', '147', '148'])).
% 0.36/0.62  thf('150', plain,
% 0.36/0.62      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.36/0.62        | ~ (l1_struct_0 @ sk_B)
% 0.36/0.62        | (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['141', '149'])).
% 0.36/0.62  thf('151', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.36/0.62  thf('152', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('153', plain,
% 0.36/0.62      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.36/0.62        | (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.36/0.62      inference('demod', [status(thm)], ['150', '151', '152'])).
% 0.36/0.62  thf('154', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.36/0.62      inference('simplify', [status(thm)], ['153'])).
% 0.36/0.62  thf('155', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_C @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.36/0.62      inference('demod', [status(thm)], ['107', '108'])).
% 0.36/0.62  thf('156', plain,
% 0.36/0.62      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.36/0.62         (~ (v2_funct_1 @ X20)
% 0.36/0.62          | ((k2_relset_1 @ X22 @ X21 @ X20) != (X21))
% 0.36/0.62          | (v1_funct_2 @ (k2_funct_1 @ X20) @ X21 @ X22)
% 0.36/0.62          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21)))
% 0.36/0.62          | ~ (v1_funct_2 @ X20 @ X22 @ X21)
% 0.36/0.62          | ~ (v1_funct_1 @ X20))),
% 0.36/0.62      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.36/0.62  thf('157', plain,
% 0.36/0.62      ((~ (v1_funct_1 @ sk_C)
% 0.36/0.62        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.36/0.62        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.36/0.62           (k1_relat_1 @ sk_C))
% 0.36/0.62        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.36/0.62            != (k2_relat_1 @ sk_C))
% 0.36/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.36/0.62      inference('sup-', [status(thm)], ['155', '156'])).
% 0.36/0.62  thf('158', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('159', plain,
% 0.36/0.62      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.36/0.62      inference('demod', [status(thm)], ['119', '120'])).
% 0.36/0.62  thf('160', plain,
% 0.36/0.62      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.36/0.62         = (k2_relat_1 @ sk_C))),
% 0.36/0.62      inference('demod', [status(thm)], ['133', '134'])).
% 0.36/0.62  thf('161', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('162', plain,
% 0.36/0.62      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.36/0.62         (k1_relat_1 @ sk_C))
% 0.36/0.62        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.36/0.62      inference('demod', [status(thm)], ['157', '158', '159', '160', '161'])).
% 0.36/0.62  thf('163', plain,
% 0.36/0.62      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.36/0.62        (k1_relat_1 @ sk_C))),
% 0.36/0.62      inference('simplify', [status(thm)], ['162'])).
% 0.36/0.62  thf('164', plain,
% 0.36/0.62      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.36/0.62          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.36/0.62        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.36/0.62        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.36/0.62            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.36/0.62      inference('demod', [status(thm)], ['140', '154', '163'])).
% 0.36/0.62  thf('165', plain,
% 0.36/0.62      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.36/0.62      inference('simplify', [status(thm)], ['137'])).
% 0.36/0.62  thf('166', plain,
% 0.36/0.62      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.36/0.62         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 0.36/0.62          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.36/0.62      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.36/0.62  thf('167', plain,
% 0.36/0.62      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.36/0.62         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['165', '166'])).
% 0.36/0.62  thf('168', plain,
% 0.36/0.62      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.36/0.62          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.36/0.62        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.36/0.62        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.36/0.62      inference('demod', [status(thm)], ['164', '167'])).
% 0.36/0.62  thf('169', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_C @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.36/0.62      inference('demod', [status(thm)], ['107', '108'])).
% 0.36/0.62  thf('170', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.36/0.62      inference('demod', [status(thm)], ['53', '56', '63'])).
% 0.36/0.62  thf('171', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.36/0.62  thf('172', plain,
% 0.36/0.62      (![X23 : $i]:
% 0.36/0.62         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.36/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.62  thf('173', plain,
% 0.36/0.62      (![X23 : $i]:
% 0.36/0.62         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.36/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.62  thf(t63_tops_2, axiom,
% 0.36/0.62    (![A:$i]:
% 0.36/0.62     ( ( l1_struct_0 @ A ) =>
% 0.36/0.62       ( ![B:$i]:
% 0.36/0.62         ( ( l1_struct_0 @ B ) =>
% 0.36/0.62           ( ![C:$i]:
% 0.36/0.62             ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.62                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.62                 ( m1_subset_1 @
% 0.36/0.62                   C @ 
% 0.36/0.62                   ( k1_zfmisc_1 @
% 0.36/0.62                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.62               ( ( ( ( k2_relset_1 @
% 0.36/0.62                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.36/0.62                     ( k2_struct_0 @ B ) ) & 
% 0.36/0.62                   ( v2_funct_1 @ C ) ) =>
% 0.36/0.62                 ( v2_funct_1 @
% 0.36/0.62                   ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) ) ))).
% 0.36/0.62  thf('174', plain,
% 0.36/0.62      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.36/0.62         (~ (l1_struct_0 @ X28)
% 0.36/0.62          | ((k2_relset_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28) @ X30)
% 0.36/0.62              != (k2_struct_0 @ X28))
% 0.36/0.62          | ~ (v2_funct_1 @ X30)
% 0.36/0.62          | (v2_funct_1 @ 
% 0.36/0.62             (k2_tops_2 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28) @ X30))
% 0.36/0.62          | ~ (m1_subset_1 @ X30 @ 
% 0.36/0.62               (k1_zfmisc_1 @ 
% 0.36/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28))))
% 0.36/0.62          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28))
% 0.36/0.62          | ~ (v1_funct_1 @ X30)
% 0.36/0.62          | ~ (l1_struct_0 @ X29))),
% 0.36/0.62      inference('cnf', [status(esa)], [t63_tops_2])).
% 0.36/0.62  thf('175', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.62         (~ (m1_subset_1 @ X2 @ 
% 0.36/0.62             (k1_zfmisc_1 @ 
% 0.36/0.62              (k2_zfmisc_1 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1))))
% 0.36/0.62          | ~ (l1_struct_0 @ X0)
% 0.36/0.62          | ~ (l1_struct_0 @ X0)
% 0.36/0.62          | ~ (v1_funct_1 @ X2)
% 0.36/0.62          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.36/0.62          | (v2_funct_1 @ 
% 0.36/0.62             (k2_tops_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1) @ X2))
% 0.36/0.62          | ~ (v2_funct_1 @ X2)
% 0.36/0.62          | ((k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1) @ X2)
% 0.36/0.62              != (k2_struct_0 @ X1))
% 0.36/0.62          | ~ (l1_struct_0 @ X1))),
% 0.36/0.62      inference('sup-', [status(thm)], ['173', '174'])).
% 0.36/0.62  thf('176', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.62         (~ (l1_struct_0 @ X1)
% 0.36/0.62          | ((k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1) @ X2)
% 0.36/0.62              != (k2_struct_0 @ X1))
% 0.36/0.62          | ~ (v2_funct_1 @ X2)
% 0.36/0.62          | (v2_funct_1 @ 
% 0.36/0.62             (k2_tops_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1) @ X2))
% 0.36/0.62          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.36/0.62          | ~ (v1_funct_1 @ X2)
% 0.36/0.62          | ~ (l1_struct_0 @ X0)
% 0.36/0.62          | ~ (m1_subset_1 @ X2 @ 
% 0.36/0.62               (k1_zfmisc_1 @ 
% 0.36/0.62                (k2_zfmisc_1 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1)))))),
% 0.36/0.62      inference('simplify', [status(thm)], ['175'])).
% 0.36/0.62  thf('177', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.62         (~ (m1_subset_1 @ X2 @ 
% 0.36/0.62             (k1_zfmisc_1 @ 
% 0.36/0.62              (k2_zfmisc_1 @ (k2_struct_0 @ X1) @ (k2_struct_0 @ X0))))
% 0.36/0.62          | ~ (l1_struct_0 @ X0)
% 0.36/0.62          | ~ (l1_struct_0 @ X1)
% 0.36/0.62          | ~ (v1_funct_1 @ X2)
% 0.36/0.62          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 0.36/0.62          | (v2_funct_1 @ 
% 0.36/0.62             (k2_tops_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ X2))
% 0.36/0.62          | ~ (v2_funct_1 @ X2)
% 0.36/0.62          | ((k2_relset_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ X2)
% 0.36/0.62              != (k2_struct_0 @ X0))
% 0.36/0.62          | ~ (l1_struct_0 @ X0))),
% 0.36/0.62      inference('sup-', [status(thm)], ['172', '176'])).
% 0.36/0.62  thf('178', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.62         (((k2_relset_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ X2)
% 0.36/0.62            != (k2_struct_0 @ X0))
% 0.36/0.62          | ~ (v2_funct_1 @ X2)
% 0.36/0.62          | (v2_funct_1 @ 
% 0.36/0.62             (k2_tops_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ X2))
% 0.36/0.62          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 0.36/0.62          | ~ (v1_funct_1 @ X2)
% 0.36/0.62          | ~ (l1_struct_0 @ X1)
% 0.36/0.62          | ~ (l1_struct_0 @ X0)
% 0.36/0.62          | ~ (m1_subset_1 @ X2 @ 
% 0.36/0.62               (k1_zfmisc_1 @ 
% 0.36/0.62                (k2_zfmisc_1 @ (k2_struct_0 @ X1) @ (k2_struct_0 @ X0)))))),
% 0.36/0.62      inference('simplify', [status(thm)], ['177'])).
% 0.36/0.62  thf('179', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         (~ (m1_subset_1 @ X1 @ 
% 0.36/0.62             (k1_zfmisc_1 @ 
% 0.36/0.62              (k2_zfmisc_1 @ (k2_struct_0 @ X0) @ (k2_relat_1 @ sk_C))))
% 0.36/0.62          | ~ (l1_struct_0 @ sk_B)
% 0.36/0.62          | ~ (l1_struct_0 @ X0)
% 0.36/0.62          | ~ (v1_funct_1 @ X1)
% 0.36/0.62          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.36/0.62          | (v2_funct_1 @ 
% 0.36/0.62             (k2_tops_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1))
% 0.36/0.62          | ~ (v2_funct_1 @ X1)
% 0.36/0.62          | ((k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1)
% 0.36/0.62              != (k2_struct_0 @ sk_B)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['171', '178'])).
% 0.36/0.62  thf('180', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('181', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.36/0.62  thf('182', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         (~ (m1_subset_1 @ X1 @ 
% 0.36/0.62             (k1_zfmisc_1 @ 
% 0.36/0.62              (k2_zfmisc_1 @ (k2_struct_0 @ X0) @ (k2_relat_1 @ sk_C))))
% 0.36/0.62          | ~ (l1_struct_0 @ X0)
% 0.36/0.62          | ~ (v1_funct_1 @ X1)
% 0.36/0.62          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.36/0.62          | (v2_funct_1 @ 
% 0.36/0.62             (k2_tops_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1))
% 0.36/0.62          | ~ (v2_funct_1 @ X1)
% 0.36/0.62          | ((k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1)
% 0.36/0.62              != (k2_relat_1 @ sk_C)))),
% 0.36/0.62      inference('demod', [status(thm)], ['179', '180', '181'])).
% 0.36/0.62  thf('183', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         (~ (m1_subset_1 @ X0 @ 
% 0.36/0.62             (k1_zfmisc_1 @ 
% 0.36/0.62              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))
% 0.36/0.62          | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ X0)
% 0.36/0.62              != (k2_relat_1 @ sk_C))
% 0.36/0.62          | ~ (v2_funct_1 @ X0)
% 0.36/0.62          | (v2_funct_1 @ 
% 0.36/0.62             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ X0))
% 0.36/0.62          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.36/0.62          | ~ (v1_funct_1 @ X0)
% 0.36/0.62          | ~ (l1_struct_0 @ sk_A))),
% 0.36/0.62      inference('sup-', [status(thm)], ['170', '182'])).
% 0.36/0.62  thf('184', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.36/0.62      inference('demod', [status(thm)], ['68', '69', '72'])).
% 0.36/0.62  thf('185', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.36/0.62      inference('demod', [status(thm)], ['68', '69', '72'])).
% 0.36/0.62  thf('186', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.36/0.62      inference('demod', [status(thm)], ['68', '69', '72'])).
% 0.36/0.62  thf('187', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('188', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         (~ (m1_subset_1 @ X0 @ 
% 0.36/0.62             (k1_zfmisc_1 @ 
% 0.36/0.62              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))
% 0.36/0.62          | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ X0)
% 0.36/0.62              != (k2_relat_1 @ sk_C))
% 0.36/0.62          | ~ (v2_funct_1 @ X0)
% 0.36/0.62          | (v2_funct_1 @ 
% 0.36/0.62             (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ X0))
% 0.36/0.62          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.36/0.62          | ~ (v1_funct_1 @ X0))),
% 0.36/0.62      inference('demod', [status(thm)], ['183', '184', '185', '186', '187'])).
% 0.36/0.62  thf('189', plain,
% 0.36/0.62      ((~ (v1_funct_1 @ sk_C)
% 0.36/0.62        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.36/0.62        | (v2_funct_1 @ 
% 0.36/0.62           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.36/0.62        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.62            != (k2_relat_1 @ sk_C)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['169', '188'])).
% 0.36/0.62  thf('190', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('191', plain,
% 0.36/0.62      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.36/0.62      inference('demod', [status(thm)], ['85', '86'])).
% 0.36/0.62  thf('192', plain,
% 0.36/0.62      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.62         = (k2_funct_1 @ sk_C))),
% 0.36/0.62      inference('simplify', [status(thm)], ['98'])).
% 0.36/0.62  thf('193', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('194', plain,
% 0.36/0.62      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.62         = (k2_relat_1 @ sk_C))),
% 0.36/0.62      inference('demod', [status(thm)], ['91', '92'])).
% 0.36/0.62  thf('195', plain,
% 0.36/0.62      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.36/0.62        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.36/0.62      inference('demod', [status(thm)],
% 0.36/0.62                ['189', '190', '191', '192', '193', '194'])).
% 0.36/0.62  thf('196', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.36/0.62      inference('simplify', [status(thm)], ['195'])).
% 0.36/0.62  thf('197', plain,
% 0.36/0.62      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.36/0.62          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.36/0.62        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.36/0.62      inference('demod', [status(thm)], ['168', '196'])).
% 0.36/0.62  thf(t55_funct_1, axiom,
% 0.36/0.62    (![A:$i]:
% 0.36/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.36/0.62       ( ( v2_funct_1 @ A ) =>
% 0.36/0.62         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.36/0.62           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.36/0.62  thf('198', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         (~ (v2_funct_1 @ X0)
% 0.36/0.62          | ((k1_relat_1 @ X0) = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.36/0.62          | ~ (v1_funct_1 @ X0)
% 0.36/0.62          | ~ (v1_relat_1 @ X0))),
% 0.36/0.62      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.36/0.62  thf('199', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         (~ (v2_funct_1 @ X0)
% 0.36/0.62          | ((k2_relat_1 @ X0) = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.36/0.62          | ~ (v1_funct_1 @ X0)
% 0.36/0.62          | ~ (v1_relat_1 @ X0))),
% 0.36/0.62      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.36/0.62  thf('200', plain,
% 0.36/0.62      (![X1 : $i]:
% 0.36/0.62         (~ (v2_funct_1 @ X1)
% 0.36/0.62          | ((k2_funct_1 @ (k2_funct_1 @ X1)) = (X1))
% 0.36/0.62          | ~ (v1_funct_1 @ X1)
% 0.36/0.62          | ~ (v1_relat_1 @ X1))),
% 0.36/0.62      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.36/0.62  thf('201', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.36/0.62      inference('simplify', [status(thm)], ['195'])).
% 0.36/0.62  thf('202', plain,
% 0.36/0.62      (![X1 : $i]:
% 0.36/0.62         (~ (v2_funct_1 @ X1)
% 0.36/0.62          | ((k2_funct_1 @ (k2_funct_1 @ X1)) = (X1))
% 0.36/0.62          | ~ (v1_funct_1 @ X1)
% 0.36/0.62          | ~ (v1_relat_1 @ X1))),
% 0.36/0.62      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.36/0.62  thf('203', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         (~ (v2_funct_1 @ X0)
% 0.36/0.62          | ((k1_relat_1 @ X0) = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.36/0.62          | ~ (v1_funct_1 @ X0)
% 0.36/0.62          | ~ (v1_relat_1 @ X0))),
% 0.36/0.62      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.36/0.62  thf('204', plain,
% 0.36/0.62      (![X1 : $i]:
% 0.36/0.62         (~ (v2_funct_1 @ X1)
% 0.36/0.62          | ((k2_funct_1 @ (k2_funct_1 @ X1)) = (X1))
% 0.36/0.62          | ~ (v1_funct_1 @ X1)
% 0.36/0.62          | ~ (v1_relat_1 @ X1))),
% 0.36/0.62      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.36/0.62  thf('205', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         (~ (v2_funct_1 @ X0)
% 0.36/0.62          | ((k2_relat_1 @ X0) = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.36/0.62          | ~ (v1_funct_1 @ X0)
% 0.36/0.62          | ~ (v1_relat_1 @ X0))),
% 0.36/0.62      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.36/0.62  thf('206', plain,
% 0.36/0.62      (![X14 : $i, X15 : $i]:
% 0.36/0.62         (((k1_relat_1 @ X15) != (X14))
% 0.36/0.62          | (v1_partfun1 @ X15 @ X14)
% 0.36/0.62          | ~ (v4_relat_1 @ X15 @ X14)
% 0.36/0.62          | ~ (v1_relat_1 @ X15))),
% 0.36/0.62      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.36/0.62  thf('207', plain,
% 0.36/0.62      (![X15 : $i]:
% 0.36/0.62         (~ (v1_relat_1 @ X15)
% 0.36/0.62          | ~ (v4_relat_1 @ X15 @ (k1_relat_1 @ X15))
% 0.36/0.62          | (v1_partfun1 @ X15 @ (k1_relat_1 @ X15)))),
% 0.36/0.62      inference('simplify', [status(thm)], ['206'])).
% 0.36/0.62  thf('208', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.36/0.62          | ~ (v1_relat_1 @ X0)
% 0.36/0.62          | ~ (v1_funct_1 @ X0)
% 0.36/0.62          | ~ (v2_funct_1 @ X0)
% 0.36/0.62          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.36/0.62          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['205', '207'])).
% 0.36/0.62  thf('209', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         (~ (v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.36/0.62          | ~ (v1_relat_1 @ X0)
% 0.36/0.62          | ~ (v1_funct_1 @ X0)
% 0.36/0.62          | ~ (v2_funct_1 @ X0)
% 0.36/0.62          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.36/0.62          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.36/0.62             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.36/0.62          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.36/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.36/0.62          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['204', '208'])).
% 0.36/0.62  thf('210', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         (~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.36/0.62          | ~ (v1_relat_1 @ X0)
% 0.36/0.62          | ~ (v1_funct_1 @ X0)
% 0.36/0.62          | ~ (v2_funct_1 @ X0)
% 0.36/0.62          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.36/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.36/0.62          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.36/0.62          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.36/0.62             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.36/0.62          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.36/0.62          | ~ (v2_funct_1 @ X0)
% 0.36/0.62          | ~ (v1_funct_1 @ X0)
% 0.36/0.62          | ~ (v1_relat_1 @ X0))),
% 0.36/0.62      inference('sup-', [status(thm)], ['203', '209'])).
% 0.36/0.62  thf('211', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         (~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.36/0.62          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.36/0.62             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.36/0.62          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.36/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.36/0.62          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.36/0.62          | ~ (v2_funct_1 @ X0)
% 0.36/0.62          | ~ (v1_funct_1 @ X0)
% 0.36/0.62          | ~ (v1_relat_1 @ X0)
% 0.36/0.62          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.36/0.62      inference('simplify', [status(thm)], ['210'])).
% 0.36/0.62  thf('212', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         (~ (v1_relat_1 @ X0)
% 0.36/0.62          | ~ (v1_relat_1 @ X0)
% 0.36/0.62          | ~ (v1_funct_1 @ X0)
% 0.36/0.62          | ~ (v2_funct_1 @ X0)
% 0.36/0.62          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.36/0.62          | ~ (v1_relat_1 @ X0)
% 0.36/0.62          | ~ (v1_funct_1 @ X0)
% 0.36/0.62          | ~ (v2_funct_1 @ X0)
% 0.36/0.62          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.36/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.36/0.62          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.36/0.62          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.36/0.62             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.36/0.62      inference('sup-', [status(thm)], ['202', '211'])).
% 0.36/0.62  thf('213', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.36/0.62           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.36/0.62          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.36/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.36/0.62          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.36/0.62          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.36/0.62          | ~ (v2_funct_1 @ X0)
% 0.36/0.62          | ~ (v1_funct_1 @ X0)
% 0.36/0.62          | ~ (v1_relat_1 @ X0))),
% 0.36/0.62      inference('simplify', [status(thm)], ['212'])).
% 0.36/0.62  thf('214', plain,
% 0.36/0.62      ((~ (v1_relat_1 @ sk_C)
% 0.36/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.36/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.36/0.62        | ~ (v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.36/0.62        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.36/0.62        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.36/0.62        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.36/0.62           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.36/0.62      inference('sup-', [status(thm)], ['201', '213'])).
% 0.36/0.62  thf('215', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.62      inference('sup-', [status(thm)], ['54', '55'])).
% 0.36/0.62  thf('216', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('217', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('218', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.36/0.62      inference('sup-', [status(thm)], ['61', '62'])).
% 0.36/0.62  thf('219', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.36/0.62      inference('demod', [status(thm)], ['53', '56', '63'])).
% 0.36/0.62  thf('220', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 0.36/0.62      inference('demod', [status(thm)], ['218', '219'])).
% 0.36/0.62  thf('221', plain,
% 0.36/0.62      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.36/0.62      inference('simplify', [status(thm)], ['137'])).
% 0.36/0.62  thf('222', plain,
% 0.36/0.62      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.62         ((v1_relat_1 @ X2)
% 0.36/0.62          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.36/0.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.36/0.62  thf('223', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.36/0.62      inference('sup-', [status(thm)], ['221', '222'])).
% 0.36/0.62  thf('224', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.36/0.62      inference('simplify', [status(thm)], ['153'])).
% 0.36/0.62  thf('225', plain,
% 0.36/0.62      ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.36/0.62        (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.36/0.62      inference('demod', [status(thm)],
% 0.36/0.62                ['214', '215', '216', '217', '220', '223', '224'])).
% 0.36/0.62  thf('226', plain,
% 0.36/0.62      (((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.36/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.36/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.36/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.36/0.62      inference('sup+', [status(thm)], ['200', '225'])).
% 0.36/0.62  thf('227', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.62      inference('sup-', [status(thm)], ['54', '55'])).
% 0.36/0.62  thf('228', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('229', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('230', plain,
% 0.36/0.62      ((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.36/0.62      inference('demod', [status(thm)], ['226', '227', '228', '229'])).
% 0.36/0.62  thf('231', plain,
% 0.36/0.62      (((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.36/0.62        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.36/0.62        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.36/0.62        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.36/0.62      inference('sup+', [status(thm)], ['199', '230'])).
% 0.36/0.62  thf('232', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.36/0.62      inference('sup-', [status(thm)], ['221', '222'])).
% 0.36/0.62  thf('233', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.36/0.62      inference('simplify', [status(thm)], ['153'])).
% 0.36/0.62  thf('234', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.36/0.62      inference('simplify', [status(thm)], ['195'])).
% 0.36/0.62  thf('235', plain,
% 0.36/0.62      ((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.36/0.62      inference('demod', [status(thm)], ['231', '232', '233', '234'])).
% 0.36/0.62  thf('236', plain,
% 0.36/0.62      (![X14 : $i, X15 : $i]:
% 0.36/0.62         (~ (v1_partfun1 @ X15 @ X14)
% 0.36/0.62          | ((k1_relat_1 @ X15) = (X14))
% 0.36/0.62          | ~ (v4_relat_1 @ X15 @ X14)
% 0.36/0.62          | ~ (v1_relat_1 @ X15))),
% 0.36/0.62      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.36/0.62  thf('237', plain,
% 0.36/0.62      ((~ (v1_relat_1 @ sk_C)
% 0.36/0.62        | ~ (v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.36/0.62        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.36/0.62      inference('sup-', [status(thm)], ['235', '236'])).
% 0.36/0.62  thf('238', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.62      inference('sup-', [status(thm)], ['54', '55'])).
% 0.36/0.62  thf('239', plain,
% 0.36/0.62      ((~ (v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.36/0.62        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.36/0.62      inference('demod', [status(thm)], ['237', '238'])).
% 0.36/0.62  thf('240', plain,
% 0.36/0.62      ((~ (v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.36/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.36/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.36/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.36/0.62        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.36/0.62      inference('sup-', [status(thm)], ['198', '239'])).
% 0.36/0.62  thf('241', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 0.36/0.62      inference('demod', [status(thm)], ['218', '219'])).
% 0.36/0.62  thf('242', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.62      inference('sup-', [status(thm)], ['54', '55'])).
% 0.36/0.62  thf('243', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('244', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('245', plain,
% 0.36/0.62      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.36/0.62      inference('demod', [status(thm)], ['240', '241', '242', '243', '244'])).
% 0.36/0.62  thf('246', plain,
% 0.36/0.62      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.36/0.62          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.36/0.62        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))),
% 0.36/0.62      inference('demod', [status(thm)], ['197', '245'])).
% 0.36/0.62  thf('247', plain,
% 0.36/0.62      (((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.36/0.62         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.36/0.62      inference('simplify', [status(thm)], ['246'])).
% 0.36/0.62  thf('248', plain,
% 0.36/0.62      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.62          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 0.36/0.62      inference('demod', [status(thm)], ['100', '247'])).
% 0.36/0.62  thf('249', plain,
% 0.36/0.62      ((~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.36/0.62           sk_C)
% 0.36/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.36/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.36/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.36/0.62      inference('sup-', [status(thm)], ['0', '248'])).
% 0.36/0.62  thf('250', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_C @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.62      inference('demod', [status(thm)], ['75', '76'])).
% 0.36/0.62  thf('251', plain,
% 0.36/0.62      ((m1_subset_1 @ sk_C @ 
% 0.36/0.62        (k1_zfmisc_1 @ 
% 0.36/0.62         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.62      inference('demod', [status(thm)], ['75', '76'])).
% 0.36/0.62  thf(reflexivity_r2_funct_2, axiom,
% 0.36/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.36/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.36/0.62         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.36/0.62         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.62       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.36/0.62  thf('252', plain,
% 0.36/0.62      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.36/0.62         ((r2_funct_2 @ X16 @ X17 @ X18 @ X18)
% 0.36/0.62          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.36/0.62          | ~ (v1_funct_2 @ X18 @ X16 @ X17)
% 0.36/0.62          | ~ (v1_funct_1 @ X18)
% 0.36/0.62          | ~ (v1_funct_1 @ X19)
% 0.36/0.62          | ~ (v1_funct_2 @ X19 @ X16 @ X17)
% 0.36/0.62          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.36/0.62      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.36/0.62  thf('253', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         (~ (m1_subset_1 @ X0 @ 
% 0.36/0.62             (k1_zfmisc_1 @ 
% 0.36/0.62              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.36/0.62          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.36/0.62          | ~ (v1_funct_1 @ X0)
% 0.36/0.62          | ~ (v1_funct_1 @ sk_C)
% 0.36/0.62          | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.36/0.62          | (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.36/0.62             sk_C))),
% 0.36/0.62      inference('sup-', [status(thm)], ['251', '252'])).
% 0.36/0.62  thf('254', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('255', plain,
% 0.36/0.62      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.36/0.62      inference('demod', [status(thm)], ['85', '86'])).
% 0.36/0.62  thf('256', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         (~ (m1_subset_1 @ X0 @ 
% 0.36/0.62             (k1_zfmisc_1 @ 
% 0.36/0.62              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.36/0.62          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.36/0.62          | ~ (v1_funct_1 @ X0)
% 0.36/0.62          | (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.36/0.62             sk_C))),
% 0.36/0.62      inference('demod', [status(thm)], ['253', '254', '255'])).
% 0.36/0.62  thf('257', plain,
% 0.36/0.62      (((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 0.36/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.36/0.62        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['250', '256'])).
% 0.36/0.62  thf('258', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('259', plain,
% 0.36/0.62      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.36/0.62      inference('demod', [status(thm)], ['85', '86'])).
% 0.36/0.62  thf('260', plain,
% 0.36/0.62      ((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.36/0.62      inference('demod', [status(thm)], ['257', '258', '259'])).
% 0.36/0.62  thf('261', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.62      inference('sup-', [status(thm)], ['54', '55'])).
% 0.36/0.62  thf('262', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('263', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('264', plain, ($false),
% 0.36/0.62      inference('demod', [status(thm)], ['249', '260', '261', '262', '263'])).
% 0.36/0.62  
% 0.36/0.62  % SZS output end Refutation
% 0.36/0.62  
% 0.36/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
