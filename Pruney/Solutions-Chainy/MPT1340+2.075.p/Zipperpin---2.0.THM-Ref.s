%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SvODQYvVbg

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:19 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  396 (25835 expanded)
%              Number of leaves         :   39 (7399 expanded)
%              Depth                    :   39
%              Number of atoms          : 3955 (552282 expanded)
%              Number of equality atoms :  198 (15668 expanded)
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

thf('116',plain,
    ( ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','115'])).

thf('117',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('118',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

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

thf('121',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X21 )
       != X22 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('122',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('125',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('126',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['122','123','124','125','126'])).

thf('128',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
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

thf('130',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('132',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('133',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','53','60'])).

thf('134',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X21 )
       != X22 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('136',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('139',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','53','60'])).

thf('140',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('142',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('143',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','53','60'])).

thf('145',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['136','137','140','145','146'])).

thf('148',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['131','147'])).

thf('149',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('150',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['148','149','150'])).

thf('152',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('154',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X21 )
       != X22 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X21 ) @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('155',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('158',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('159',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['155','156','157','158','159'])).

thf('161',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['130','152','161'])).

thf('163',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('164',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('165',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['162','165'])).

thf('167',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('168',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','68'])).

thf('169',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('170',plain,(
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

thf('171',plain,(
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

thf('172',plain,(
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
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
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
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,(
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
    inference('sup-',[status(thm)],['169','173'])).

thf('175',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( k2_relat_1 @ sk_C ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 )
       != ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['174','175','176'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X0 )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X0 ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['168','177'])).

thf('179',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','68'])).

thf('180',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','68'])).

thf('181',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','68'])).

thf('182',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ X0 )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ X0 ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['178','179','180','181','182'])).

thf('184',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['167','183'])).

thf('185',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('187',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('188',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('189',plain,(
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

thf('190',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('193',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('195',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['190','191','192','193','194'])).

thf('196',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['187','195'])).

thf('197',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('198',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['196','197','198'])).

thf('200',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('203',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['184','185','186','200','201','202'])).

thf('204',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['203'])).

thf('205',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['166','204'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('206',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X5 ) )
        = X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('207',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('208',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('209',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X21 )
       != X22 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('210',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['208','209'])).

thf('211',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('213',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('214',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['210','211','212','213','214'])).

thf('216',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['207','215'])).

thf('217',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('218',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['216','217','218'])).

thf('220',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['219'])).

thf('221',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X21 )
       != X22 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('222',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['220','221'])).

thf('223',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['151'])).

thf('224',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('225',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('226',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X21 )
       != X22 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X21 ) @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('227',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['225','226'])).

thf('228',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('230',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('231',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['227','228','229','230','231'])).

thf('233',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['224','232'])).

thf('234',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('235',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['233','234','235'])).

thf('237',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['236'])).

thf('238',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['222','223','237'])).

thf('239',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['219'])).

thf('240',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('241',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['239','240'])).

thf('242',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['238','241'])).

thf('243',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['203'])).

thf('244',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['242','243'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('245',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('246',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('247',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X5 ) )
        = X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('248',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['203'])).

thf('249',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X5 ) )
        = X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('250',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('251',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X5 ) )
        = X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('252',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('253',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k1_relat_1 @ X16 )
       != X15 )
      | ( v1_partfun1 @ X16 @ X15 )
      | ~ ( v4_relat_1 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('254',plain,(
    ! [X16: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v4_relat_1 @ X16 @ ( k1_relat_1 @ X16 ) )
      | ( v1_partfun1 @ X16 @ ( k1_relat_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['253'])).

thf('255',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['252','254'])).

thf('256',plain,(
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
    inference('sup-',[status(thm)],['251','255'])).

thf('257',plain,(
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
    inference('sup-',[status(thm)],['250','256'])).

thf('258',plain,(
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
    inference(simplify,[status(thm)],['257'])).

thf('259',plain,(
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
    inference('sup-',[status(thm)],['249','258'])).

thf('260',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['259'])).

thf('261',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['248','260'])).

thf('262',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('263',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('266',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','53','60'])).

thf('267',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['265','266'])).

thf('268',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('269',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('270',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['268','269'])).

thf('271',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('272',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['270','271'])).

thf('273',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['151'])).

thf('274',plain,(
    v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['261','262','263','264','267','272','273'])).

thf('275',plain,
    ( ( v1_partfun1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['247','274'])).

thf('276',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('277',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('278',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,(
    v1_partfun1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['275','276','277','278'])).

thf('280',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['246','279'])).

thf('281',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['270','271'])).

thf('282',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['151'])).

thf('283',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['203'])).

thf('284',plain,(
    v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['280','281','282','283'])).

thf('285',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_partfun1 @ X16 @ X15 )
      | ( ( k1_relat_1 @ X16 )
        = X15 )
      | ~ ( v4_relat_1 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('286',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['284','285'])).

thf('287',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('288',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['286','287'])).

thf('289',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['245','288'])).

thf('290',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['265','266'])).

thf('291',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('292',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('293',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('294',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['289','290','291','292','293'])).

thf('295',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['244','294'])).

thf('296',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['295'])).

thf('297',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_funct_2 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('298',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X17 @ X18 @ X19 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( X17 = X20 )
      | ~ ( r2_funct_2 @ X18 @ X19 @ X17 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('299',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['297','298'])).

thf('300',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('301',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('302',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['299','300','301'])).

thf('303',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','68'])).

thf('304',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','68'])).

thf('305',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','68'])).

thf('306',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['302','303','304','305'])).

thf('307',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['296','306'])).

thf('308',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('309',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['219'])).

thf('310',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X21 )
       != X22 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('311',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['309','310'])).

thf('312',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['151'])).

thf('313',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['236'])).

thf('314',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['311','312','313'])).

thf('315',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['239','240'])).

thf('316',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['314','315'])).

thf('317',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['203'])).

thf('318',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['316','317'])).

thf('319',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['308','318'])).

thf('320',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('321',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('322',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('323',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['319','320','321','322'])).

thf('324',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['323'])).

thf('325',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['219'])).

thf('326',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X21 )
       != X22 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X21 ) @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('327',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['325','326'])).

thf('328',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['151'])).

thf('329',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['236'])).

thf('330',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['327','328','329'])).

thf('331',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['239','240'])).

thf('332',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['330','331'])).

thf('333',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['203'])).

thf('334',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['332','333'])).

thf('335',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['289','290','291','292','293'])).

thf('336',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['334','335'])).

thf('337',plain,(
    v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['336'])).

thf('338',plain,
    ( ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['307','324','337'])).

thf('339',plain,
    ( ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['206','338'])).

thf('340',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('341',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X17 @ X18 @ X19 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( r2_funct_2 @ X18 @ X19 @ X17 @ X20 )
      | ( X17 != X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('342',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_funct_2 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['341'])).

thf('343',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['340','342'])).

thf('344',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('345',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('346',plain,(
    r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['343','344','345'])).

thf('347',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('348',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('349',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('350',plain,
    ( sk_C
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['339','346','347','348','349'])).

thf('351',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['289','290','291','292','293'])).

thf('352',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['205','350','351'])).

thf('353',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = sk_C ),
    inference(simplify,[status(thm)],['352'])).

thf('354',plain,(
    r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['343','344','345'])).

thf('355',plain,(
    $false ),
    inference(demod,[status(thm)],['119','353','354'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SvODQYvVbg
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:05:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.67  % Solved by: fo/fo7.sh
% 0.45/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.67  % done 428 iterations in 0.210s
% 0.45/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.67  % SZS output start Refutation
% 0.45/0.67  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.45/0.67  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.45/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.67  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.67  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.45/0.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.67  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.67  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.45/0.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.67  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.45/0.67  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.45/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.67  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.67  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.45/0.67  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.45/0.67  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.45/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.67  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.45/0.67  thf(d3_struct_0, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.45/0.67  thf('0', plain,
% 0.45/0.67      (![X24 : $i]:
% 0.45/0.67         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.67  thf('1', plain,
% 0.45/0.67      (![X24 : $i]:
% 0.45/0.67         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.67  thf('2', plain,
% 0.45/0.67      (![X24 : $i]:
% 0.45/0.67         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.67  thf(t64_tops_2, conjecture,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( l1_struct_0 @ A ) =>
% 0.45/0.67       ( ![B:$i]:
% 0.45/0.67         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.45/0.67           ( ![C:$i]:
% 0.45/0.67             ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.67                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.67                 ( m1_subset_1 @
% 0.45/0.67                   C @ 
% 0.45/0.67                   ( k1_zfmisc_1 @
% 0.45/0.67                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.67               ( ( ( ( k2_relset_1 @
% 0.45/0.67                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.45/0.67                     ( k2_struct_0 @ B ) ) & 
% 0.45/0.67                   ( v2_funct_1 @ C ) ) =>
% 0.45/0.67                 ( r2_funct_2 @
% 0.45/0.67                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.45/0.67                   ( k2_tops_2 @
% 0.45/0.67                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.45/0.67                     ( k2_tops_2 @
% 0.45/0.67                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.45/0.67                   C ) ) ) ) ) ) ))).
% 0.45/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.67    (~( ![A:$i]:
% 0.45/0.67        ( ( l1_struct_0 @ A ) =>
% 0.45/0.67          ( ![B:$i]:
% 0.45/0.67            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.45/0.67              ( ![C:$i]:
% 0.45/0.67                ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.67                    ( v1_funct_2 @
% 0.45/0.67                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.67                    ( m1_subset_1 @
% 0.45/0.67                      C @ 
% 0.45/0.67                      ( k1_zfmisc_1 @
% 0.45/0.67                        ( k2_zfmisc_1 @
% 0.45/0.67                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.67                  ( ( ( ( k2_relset_1 @
% 0.45/0.67                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.45/0.67                        ( k2_struct_0 @ B ) ) & 
% 0.45/0.67                      ( v2_funct_1 @ C ) ) =>
% 0.45/0.67                    ( r2_funct_2 @
% 0.45/0.67                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.45/0.67                      ( k2_tops_2 @
% 0.45/0.67                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.45/0.67                        ( k2_tops_2 @
% 0.45/0.67                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.45/0.67                      C ) ) ) ) ) ) ) )),
% 0.45/0.67    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.45/0.67  thf('3', plain,
% 0.45/0.67      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.67          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.67          sk_C)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('4', plain,
% 0.45/0.67      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.67           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.67           sk_C)
% 0.45/0.67        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['2', '3'])).
% 0.45/0.67  thf('5', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('6', plain,
% 0.45/0.67      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.67          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.67          sk_C)),
% 0.45/0.67      inference('demod', [status(thm)], ['4', '5'])).
% 0.45/0.67  thf('7', plain,
% 0.45/0.67      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.67           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.67           sk_C)
% 0.45/0.67        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.67      inference('sup-', [status(thm)], ['1', '6'])).
% 0.45/0.67  thf('8', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('9', plain,
% 0.45/0.67      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.67          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.67           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.67          sk_C)),
% 0.45/0.67      inference('demod', [status(thm)], ['7', '8'])).
% 0.45/0.67  thf('10', plain,
% 0.45/0.67      (![X24 : $i]:
% 0.45/0.67         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.67  thf('11', plain,
% 0.45/0.67      (![X24 : $i]:
% 0.45/0.67         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.67  thf('12', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('13', plain,
% 0.45/0.67      (((m1_subset_1 @ sk_C @ 
% 0.45/0.67         (k1_zfmisc_1 @ 
% 0.45/0.67          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.45/0.67        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.67      inference('sup+', [status(thm)], ['11', '12'])).
% 0.45/0.67  thf('14', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('15', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.45/0.67      inference('demod', [status(thm)], ['13', '14'])).
% 0.45/0.67  thf('16', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(redefinition_k2_relset_1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.67       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.45/0.67  thf('17', plain,
% 0.45/0.67      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.67         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 0.45/0.67          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.45/0.67      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.67  thf('18', plain,
% 0.45/0.67      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.67         = (k2_relat_1 @ sk_C))),
% 0.45/0.67      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.67  thf('19', plain,
% 0.45/0.67      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.67         = (k2_struct_0 @ sk_B))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('20', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.67      inference('sup+', [status(thm)], ['18', '19'])).
% 0.45/0.67  thf('21', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.45/0.67      inference('demod', [status(thm)], ['15', '20'])).
% 0.45/0.67  thf(cc5_funct_2, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.45/0.67       ( ![C:$i]:
% 0.45/0.67         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.67           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.45/0.67             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.45/0.67  thf('22', plain,
% 0.45/0.67      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.45/0.67         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.45/0.67          | (v1_partfun1 @ X12 @ X13)
% 0.45/0.67          | ~ (v1_funct_2 @ X12 @ X13 @ X14)
% 0.45/0.67          | ~ (v1_funct_1 @ X12)
% 0.45/0.67          | (v1_xboole_0 @ X14))),
% 0.45/0.67      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.45/0.67  thf('23', plain,
% 0.45/0.67      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.45/0.67        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.67        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.45/0.67        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['21', '22'])).
% 0.45/0.67  thf('24', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('25', plain,
% 0.45/0.67      (![X24 : $i]:
% 0.45/0.67         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.67  thf('26', plain,
% 0.45/0.67      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('27', plain,
% 0.45/0.67      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.45/0.67        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.67      inference('sup+', [status(thm)], ['25', '26'])).
% 0.45/0.67  thf('28', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('29', plain,
% 0.45/0.67      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.45/0.67      inference('demod', [status(thm)], ['27', '28'])).
% 0.45/0.67  thf('30', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.67      inference('sup+', [status(thm)], ['18', '19'])).
% 0.45/0.67  thf('31', plain,
% 0.45/0.67      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.45/0.67      inference('demod', [status(thm)], ['29', '30'])).
% 0.45/0.67  thf('32', plain,
% 0.45/0.67      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.45/0.67        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('demod', [status(thm)], ['23', '24', '31'])).
% 0.45/0.67  thf('33', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.67      inference('sup+', [status(thm)], ['18', '19'])).
% 0.45/0.67  thf('34', plain,
% 0.45/0.67      (![X24 : $i]:
% 0.45/0.67         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.67  thf(fc2_struct_0, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.45/0.67       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.45/0.67  thf('35', plain,
% 0.45/0.67      (![X25 : $i]:
% 0.45/0.67         (~ (v1_xboole_0 @ (u1_struct_0 @ X25))
% 0.45/0.67          | ~ (l1_struct_0 @ X25)
% 0.45/0.67          | (v2_struct_0 @ X25))),
% 0.45/0.67      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.45/0.67  thf('36', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.45/0.67          | ~ (l1_struct_0 @ X0)
% 0.45/0.67          | (v2_struct_0 @ X0)
% 0.45/0.67          | ~ (l1_struct_0 @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['34', '35'])).
% 0.45/0.67  thf('37', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((v2_struct_0 @ X0)
% 0.45/0.67          | ~ (l1_struct_0 @ X0)
% 0.45/0.67          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.45/0.67      inference('simplify', [status(thm)], ['36'])).
% 0.45/0.67  thf('38', plain,
% 0.45/0.67      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.45/0.67        | ~ (l1_struct_0 @ sk_B)
% 0.45/0.67        | (v2_struct_0 @ sk_B))),
% 0.45/0.67      inference('sup-', [status(thm)], ['33', '37'])).
% 0.45/0.67  thf('39', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('40', plain,
% 0.45/0.67      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.45/0.67      inference('demod', [status(thm)], ['38', '39'])).
% 0.45/0.67  thf('41', plain, (~ (v2_struct_0 @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('42', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.45/0.67      inference('clc', [status(thm)], ['40', '41'])).
% 0.45/0.67  thf('43', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.45/0.67      inference('clc', [status(thm)], ['32', '42'])).
% 0.45/0.67  thf('44', plain,
% 0.45/0.67      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.67      inference('sup+', [status(thm)], ['10', '43'])).
% 0.45/0.67  thf('45', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('46', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['44', '45'])).
% 0.45/0.67  thf(d4_partfun1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.45/0.67       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.45/0.67  thf('47', plain,
% 0.45/0.67      (![X15 : $i, X16 : $i]:
% 0.45/0.67         (~ (v1_partfun1 @ X16 @ X15)
% 0.45/0.67          | ((k1_relat_1 @ X16) = (X15))
% 0.45/0.67          | ~ (v4_relat_1 @ X16 @ X15)
% 0.45/0.67          | ~ (v1_relat_1 @ X16))),
% 0.45/0.67      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.45/0.67  thf('48', plain,
% 0.45/0.67      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.67        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.45/0.67        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['46', '47'])).
% 0.45/0.67  thf('49', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(cc2_relat_1, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( v1_relat_1 @ A ) =>
% 0.45/0.67       ( ![B:$i]:
% 0.45/0.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.45/0.67  thf('50', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.45/0.67          | (v1_relat_1 @ X0)
% 0.45/0.67          | ~ (v1_relat_1 @ X1))),
% 0.45/0.67      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.45/0.67  thf('51', plain,
% 0.45/0.67      ((~ (v1_relat_1 @ 
% 0.45/0.67           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.45/0.67        | (v1_relat_1 @ sk_C))),
% 0.45/0.67      inference('sup-', [status(thm)], ['49', '50'])).
% 0.45/0.67  thf(fc6_relat_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.45/0.67  thf('52', plain,
% 0.45/0.67      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.45/0.67      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.45/0.67  thf('53', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.67      inference('demod', [status(thm)], ['51', '52'])).
% 0.45/0.67  thf('54', plain,
% 0.45/0.67      (![X24 : $i]:
% 0.45/0.67         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.67  thf('55', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('56', plain,
% 0.45/0.67      (((m1_subset_1 @ sk_C @ 
% 0.45/0.67         (k1_zfmisc_1 @ 
% 0.45/0.67          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.45/0.67        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.67      inference('sup+', [status(thm)], ['54', '55'])).
% 0.45/0.67  thf('57', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('58', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.67      inference('demod', [status(thm)], ['56', '57'])).
% 0.45/0.67  thf(cc2_relset_1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.67       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.45/0.67  thf('59', plain,
% 0.45/0.67      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.45/0.67         ((v4_relat_1 @ X6 @ X7)
% 0.45/0.67          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.45/0.67      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.67  thf('60', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['58', '59'])).
% 0.45/0.67  thf('61', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['48', '53', '60'])).
% 0.45/0.67  thf('62', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.45/0.67      inference('clc', [status(thm)], ['32', '42'])).
% 0.45/0.67  thf('63', plain,
% 0.45/0.67      (![X15 : $i, X16 : $i]:
% 0.45/0.67         (~ (v1_partfun1 @ X16 @ X15)
% 0.45/0.67          | ((k1_relat_1 @ X16) = (X15))
% 0.45/0.67          | ~ (v4_relat_1 @ X16 @ X15)
% 0.45/0.67          | ~ (v1_relat_1 @ X16))),
% 0.45/0.67      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.45/0.67  thf('64', plain,
% 0.45/0.67      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.67        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.45/0.67        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['62', '63'])).
% 0.45/0.67  thf('65', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.67      inference('demod', [status(thm)], ['51', '52'])).
% 0.45/0.67  thf('66', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('67', plain,
% 0.45/0.67      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.45/0.67         ((v4_relat_1 @ X6 @ X7)
% 0.45/0.67          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.45/0.67      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.67  thf('68', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['66', '67'])).
% 0.45/0.67  thf('69', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['64', '65', '68'])).
% 0.45/0.67  thf('70', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['64', '65', '68'])).
% 0.45/0.67  thf('71', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.67      inference('sup+', [status(thm)], ['18', '19'])).
% 0.45/0.67  thf('72', plain,
% 0.45/0.67      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.67          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.67           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)) @ 
% 0.45/0.67          sk_C)),
% 0.45/0.67      inference('demod', [status(thm)], ['9', '61', '69', '70', '71'])).
% 0.45/0.67  thf('73', plain,
% 0.45/0.67      (![X24 : $i]:
% 0.45/0.67         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.67  thf('74', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.67      inference('demod', [status(thm)], ['56', '57'])).
% 0.45/0.67  thf('75', plain,
% 0.45/0.67      (((m1_subset_1 @ sk_C @ 
% 0.45/0.67         (k1_zfmisc_1 @ 
% 0.45/0.67          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.45/0.67        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.67      inference('sup+', [status(thm)], ['73', '74'])).
% 0.45/0.67  thf('76', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('77', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.45/0.67      inference('demod', [status(thm)], ['75', '76'])).
% 0.45/0.67  thf('78', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.67      inference('sup+', [status(thm)], ['18', '19'])).
% 0.45/0.67  thf('79', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.45/0.67      inference('demod', [status(thm)], ['77', '78'])).
% 0.45/0.67  thf('80', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['48', '53', '60'])).
% 0.45/0.67  thf('81', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.45/0.67      inference('demod', [status(thm)], ['79', '80'])).
% 0.45/0.67  thf(d4_tops_2, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.67         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.67       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.45/0.67         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.45/0.67  thf('82', plain,
% 0.45/0.67      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.45/0.67         (((k2_relset_1 @ X27 @ X26 @ X28) != (X26))
% 0.45/0.67          | ~ (v2_funct_1 @ X28)
% 0.45/0.67          | ((k2_tops_2 @ X27 @ X26 @ X28) = (k2_funct_1 @ X28))
% 0.45/0.67          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 0.45/0.67          | ~ (v1_funct_2 @ X28 @ X27 @ X26)
% 0.45/0.67          | ~ (v1_funct_1 @ X28))),
% 0.45/0.67      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.45/0.67  thf('83', plain,
% 0.45/0.67      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.67        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.45/0.67        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.67            = (k2_funct_1 @ sk_C))
% 0.45/0.67        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.67        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.67            != (k2_relat_1 @ sk_C)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['81', '82'])).
% 0.45/0.67  thf('84', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('85', plain,
% 0.45/0.67      (![X24 : $i]:
% 0.45/0.67         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.67  thf('86', plain,
% 0.45/0.67      (![X24 : $i]:
% 0.45/0.67         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.67  thf('87', plain,
% 0.45/0.67      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('88', plain,
% 0.45/0.67      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.67        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.67      inference('sup+', [status(thm)], ['86', '87'])).
% 0.45/0.67  thf('89', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('90', plain,
% 0.45/0.67      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.67      inference('demod', [status(thm)], ['88', '89'])).
% 0.45/0.67  thf('91', plain,
% 0.45/0.67      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.45/0.67        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.67      inference('sup+', [status(thm)], ['85', '90'])).
% 0.45/0.67  thf('92', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('93', plain,
% 0.45/0.67      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.45/0.67      inference('demod', [status(thm)], ['91', '92'])).
% 0.45/0.67  thf('94', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.67      inference('sup+', [status(thm)], ['18', '19'])).
% 0.45/0.67  thf('95', plain,
% 0.45/0.67      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.45/0.67      inference('demod', [status(thm)], ['93', '94'])).
% 0.45/0.67  thf('96', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['48', '53', '60'])).
% 0.45/0.67  thf('97', plain,
% 0.45/0.67      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.45/0.67      inference('demod', [status(thm)], ['95', '96'])).
% 0.45/0.67  thf('98', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('99', plain,
% 0.45/0.67      (![X24 : $i]:
% 0.45/0.67         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.67  thf('100', plain,
% 0.45/0.67      (![X24 : $i]:
% 0.45/0.67         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.67  thf('101', plain,
% 0.45/0.67      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.67         = (k2_struct_0 @ sk_B))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('102', plain,
% 0.45/0.67      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.67          = (k2_struct_0 @ sk_B))
% 0.45/0.67        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.67      inference('sup+', [status(thm)], ['100', '101'])).
% 0.45/0.67  thf('103', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('104', plain,
% 0.45/0.67      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.67         = (k2_struct_0 @ sk_B))),
% 0.45/0.67      inference('demod', [status(thm)], ['102', '103'])).
% 0.45/0.67  thf('105', plain,
% 0.45/0.67      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.67          = (k2_struct_0 @ sk_B))
% 0.45/0.67        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.67      inference('sup+', [status(thm)], ['99', '104'])).
% 0.45/0.67  thf('106', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('107', plain,
% 0.45/0.67      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.67         = (k2_struct_0 @ sk_B))),
% 0.45/0.67      inference('demod', [status(thm)], ['105', '106'])).
% 0.45/0.67  thf('108', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.67      inference('sup+', [status(thm)], ['18', '19'])).
% 0.45/0.67  thf('109', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.67      inference('sup+', [status(thm)], ['18', '19'])).
% 0.45/0.67  thf('110', plain,
% 0.45/0.67      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.67         = (k2_relat_1 @ sk_C))),
% 0.45/0.67      inference('demod', [status(thm)], ['107', '108', '109'])).
% 0.45/0.67  thf('111', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.67      inference('demod', [status(thm)], ['48', '53', '60'])).
% 0.45/0.67  thf('112', plain,
% 0.45/0.67      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.67         = (k2_relat_1 @ sk_C))),
% 0.45/0.67      inference('demod', [status(thm)], ['110', '111'])).
% 0.45/0.67  thf('113', plain,
% 0.45/0.67      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.67          = (k2_funct_1 @ sk_C))
% 0.45/0.67        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.45/0.67      inference('demod', [status(thm)], ['83', '84', '97', '98', '112'])).
% 0.45/0.67  thf('114', plain,
% 0.45/0.67      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.67         = (k2_funct_1 @ sk_C))),
% 0.45/0.67      inference('simplify', [status(thm)], ['113'])).
% 0.45/0.67  thf('115', plain,
% 0.45/0.67      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.67          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.67           (k2_funct_1 @ sk_C)) @ 
% 0.45/0.67          sk_C)),
% 0.45/0.67      inference('demod', [status(thm)], ['72', '114'])).
% 0.45/0.67  thf('116', plain,
% 0.45/0.67      ((~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.67           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.67            (k2_funct_1 @ sk_C)) @ 
% 0.45/0.67           sk_C)
% 0.45/0.67        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.67      inference('sup-', [status(thm)], ['0', '115'])).
% 0.45/0.67  thf('117', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.67      inference('sup+', [status(thm)], ['18', '19'])).
% 0.45/0.67  thf('118', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('119', plain,
% 0.45/0.67      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.67          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.67           (k2_funct_1 @ sk_C)) @ 
% 0.45/0.67          sk_C)),
% 0.45/0.67      inference('demod', [status(thm)], ['116', '117', '118'])).
% 0.45/0.67  thf('120', plain,
% 0.45/0.67      ((m1_subset_1 @ sk_C @ 
% 0.45/0.67        (k1_zfmisc_1 @ 
% 0.45/0.67         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.45/0.67      inference('demod', [status(thm)], ['79', '80'])).
% 0.45/0.67  thf(t31_funct_2, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.67         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.67       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.45/0.67         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.45/0.67           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.45/0.67           ( m1_subset_1 @
% 0.45/0.67             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.45/0.68  thf('121', plain,
% 0.45/0.68      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.45/0.68         (~ (v2_funct_1 @ X21)
% 0.45/0.68          | ((k2_relset_1 @ X23 @ X22 @ X21) != (X22))
% 0.45/0.68          | (m1_subset_1 @ (k2_funct_1 @ X21) @ 
% 0.45/0.68             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.45/0.68          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.45/0.68          | ~ (v1_funct_2 @ X21 @ X23 @ X22)
% 0.45/0.68          | ~ (v1_funct_1 @ X21))),
% 0.45/0.68      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.45/0.68  thf('122', plain,
% 0.45/0.68      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.68        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.45/0.68        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.68           (k1_zfmisc_1 @ 
% 0.45/0.68            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.45/0.68        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.68            != (k2_relat_1 @ sk_C))
% 0.45/0.68        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.68      inference('sup-', [status(thm)], ['120', '121'])).
% 0.45/0.68  thf('123', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('124', plain,
% 0.45/0.68      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.45/0.68      inference('demod', [status(thm)], ['95', '96'])).
% 0.45/0.68  thf('125', plain,
% 0.45/0.68      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.68         = (k2_relat_1 @ sk_C))),
% 0.45/0.68      inference('demod', [status(thm)], ['110', '111'])).
% 0.45/0.68  thf('126', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('127', plain,
% 0.45/0.68      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.68         (k1_zfmisc_1 @ 
% 0.45/0.68          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.45/0.68        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)], ['122', '123', '124', '125', '126'])).
% 0.45/0.68  thf('128', plain,
% 0.45/0.68      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.45/0.68      inference('simplify', [status(thm)], ['127'])).
% 0.45/0.68  thf('129', plain,
% 0.45/0.68      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.45/0.68         (((k2_relset_1 @ X27 @ X26 @ X28) != (X26))
% 0.45/0.68          | ~ (v2_funct_1 @ X28)
% 0.45/0.68          | ((k2_tops_2 @ X27 @ X26 @ X28) = (k2_funct_1 @ X28))
% 0.45/0.68          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 0.45/0.68          | ~ (v1_funct_2 @ X28 @ X27 @ X26)
% 0.45/0.68          | ~ (v1_funct_1 @ X28))),
% 0.45/0.68      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.45/0.68  thf('130', plain,
% 0.45/0.68      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.68        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.45/0.68             (k1_relat_1 @ sk_C))
% 0.45/0.68        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.68            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.68        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.68        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.68            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['128', '129'])).
% 0.45/0.68  thf('131', plain,
% 0.45/0.68      (![X24 : $i]:
% 0.45/0.68         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.68  thf('132', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.68      inference('demod', [status(thm)], ['56', '57'])).
% 0.45/0.68  thf('133', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['48', '53', '60'])).
% 0.45/0.68  thf('134', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.68      inference('demod', [status(thm)], ['132', '133'])).
% 0.45/0.68  thf('135', plain,
% 0.45/0.68      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.45/0.68         (~ (v2_funct_1 @ X21)
% 0.45/0.68          | ((k2_relset_1 @ X23 @ X22 @ X21) != (X22))
% 0.45/0.68          | (v1_funct_1 @ (k2_funct_1 @ X21))
% 0.45/0.68          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.45/0.68          | ~ (v1_funct_2 @ X21 @ X23 @ X22)
% 0.45/0.68          | ~ (v1_funct_1 @ X21))),
% 0.45/0.68      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.45/0.68  thf('136', plain,
% 0.45/0.68      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.68        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.45/0.68        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.68        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68            != (u1_struct_0 @ sk_B))
% 0.45/0.68        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.68      inference('sup-', [status(thm)], ['134', '135'])).
% 0.45/0.68  thf('137', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('138', plain,
% 0.45/0.68      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.68      inference('demod', [status(thm)], ['88', '89'])).
% 0.45/0.68  thf('139', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['48', '53', '60'])).
% 0.45/0.68  thf('140', plain,
% 0.45/0.68      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.45/0.68      inference('demod', [status(thm)], ['138', '139'])).
% 0.45/0.68  thf('141', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.68      inference('demod', [status(thm)], ['56', '57'])).
% 0.45/0.68  thf('142', plain,
% 0.45/0.68      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.68         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 0.45/0.68          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.45/0.68      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.68  thf('143', plain,
% 0.45/0.68      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68         = (k2_relat_1 @ sk_C))),
% 0.45/0.68      inference('sup-', [status(thm)], ['141', '142'])).
% 0.45/0.68  thf('144', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['48', '53', '60'])).
% 0.45/0.68  thf('145', plain,
% 0.45/0.68      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68         = (k2_relat_1 @ sk_C))),
% 0.45/0.68      inference('demod', [status(thm)], ['143', '144'])).
% 0.45/0.68  thf('146', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('147', plain,
% 0.45/0.68      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.68        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.45/0.68      inference('demod', [status(thm)], ['136', '137', '140', '145', '146'])).
% 0.45/0.68  thf('148', plain,
% 0.45/0.68      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.45/0.68        | ~ (l1_struct_0 @ sk_B)
% 0.45/0.68        | (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['131', '147'])).
% 0.45/0.68  thf('149', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.68      inference('sup+', [status(thm)], ['18', '19'])).
% 0.45/0.68  thf('150', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('151', plain,
% 0.45/0.68      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.45/0.68        | (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)], ['148', '149', '150'])).
% 0.45/0.68  thf('152', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.68      inference('simplify', [status(thm)], ['151'])).
% 0.45/0.68  thf('153', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.45/0.68      inference('demod', [status(thm)], ['79', '80'])).
% 0.45/0.68  thf('154', plain,
% 0.45/0.68      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.45/0.68         (~ (v2_funct_1 @ X21)
% 0.45/0.68          | ((k2_relset_1 @ X23 @ X22 @ X21) != (X22))
% 0.45/0.68          | (v1_funct_2 @ (k2_funct_1 @ X21) @ X22 @ X23)
% 0.45/0.68          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.45/0.68          | ~ (v1_funct_2 @ X21 @ X23 @ X22)
% 0.45/0.68          | ~ (v1_funct_1 @ X21))),
% 0.45/0.68      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.45/0.68  thf('155', plain,
% 0.45/0.68      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.68        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.45/0.68        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.45/0.68           (k1_relat_1 @ sk_C))
% 0.45/0.68        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.68            != (k2_relat_1 @ sk_C))
% 0.45/0.68        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.68      inference('sup-', [status(thm)], ['153', '154'])).
% 0.45/0.68  thf('156', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('157', plain,
% 0.45/0.68      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.45/0.68      inference('demod', [status(thm)], ['95', '96'])).
% 0.45/0.68  thf('158', plain,
% 0.45/0.68      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.68         = (k2_relat_1 @ sk_C))),
% 0.45/0.68      inference('demod', [status(thm)], ['110', '111'])).
% 0.45/0.68  thf('159', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('160', plain,
% 0.45/0.68      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.45/0.68         (k1_relat_1 @ sk_C))
% 0.45/0.68        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)], ['155', '156', '157', '158', '159'])).
% 0.45/0.68  thf('161', plain,
% 0.45/0.68      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.45/0.68        (k1_relat_1 @ sk_C))),
% 0.45/0.68      inference('simplify', [status(thm)], ['160'])).
% 0.45/0.68  thf('162', plain,
% 0.45/0.68      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.68          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.68        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.68        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.68            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)], ['130', '152', '161'])).
% 0.45/0.68  thf('163', plain,
% 0.45/0.68      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.45/0.68      inference('simplify', [status(thm)], ['127'])).
% 0.45/0.68  thf('164', plain,
% 0.45/0.68      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.68         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 0.45/0.68          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.45/0.68      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.68  thf('165', plain,
% 0.45/0.68      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.68         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['163', '164'])).
% 0.45/0.68  thf('166', plain,
% 0.45/0.68      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.68          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.68        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.68        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)], ['162', '165'])).
% 0.45/0.68  thf('167', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.45/0.68      inference('demod', [status(thm)], ['79', '80'])).
% 0.45/0.68  thf('168', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['64', '65', '68'])).
% 0.45/0.68  thf('169', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.68      inference('sup+', [status(thm)], ['18', '19'])).
% 0.45/0.68  thf('170', plain,
% 0.45/0.68      (![X24 : $i]:
% 0.45/0.68         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.68  thf(t63_tops_2, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( l1_struct_0 @ A ) =>
% 0.45/0.68       ( ![B:$i]:
% 0.45/0.68         ( ( l1_struct_0 @ B ) =>
% 0.45/0.68           ( ![C:$i]:
% 0.45/0.68             ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.68                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.68                 ( m1_subset_1 @
% 0.45/0.68                   C @ 
% 0.45/0.68                   ( k1_zfmisc_1 @
% 0.45/0.68                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.68               ( ( ( ( k2_relset_1 @
% 0.45/0.68                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.45/0.68                     ( k2_struct_0 @ B ) ) & 
% 0.45/0.68                   ( v2_funct_1 @ C ) ) =>
% 0.45/0.68                 ( v2_funct_1 @
% 0.45/0.68                   ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) ) ))).
% 0.45/0.68  thf('171', plain,
% 0.45/0.68      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.45/0.68         (~ (l1_struct_0 @ X29)
% 0.45/0.68          | ((k2_relset_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X29) @ X31)
% 0.45/0.68              != (k2_struct_0 @ X29))
% 0.45/0.68          | ~ (v2_funct_1 @ X31)
% 0.45/0.68          | (v2_funct_1 @ 
% 0.45/0.68             (k2_tops_2 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X29) @ X31))
% 0.45/0.68          | ~ (m1_subset_1 @ X31 @ 
% 0.45/0.68               (k1_zfmisc_1 @ 
% 0.45/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X29))))
% 0.45/0.68          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X29))
% 0.45/0.68          | ~ (v1_funct_1 @ X31)
% 0.45/0.68          | ~ (l1_struct_0 @ X30))),
% 0.45/0.68      inference('cnf', [status(esa)], [t63_tops_2])).
% 0.45/0.68  thf('172', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X2 @ 
% 0.45/0.68             (k1_zfmisc_1 @ 
% 0.45/0.68              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (k2_struct_0 @ X0))))
% 0.45/0.68          | ~ (l1_struct_0 @ X0)
% 0.45/0.68          | ~ (l1_struct_0 @ X1)
% 0.45/0.68          | ~ (v1_funct_1 @ X2)
% 0.45/0.68          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 0.45/0.68          | (v2_funct_1 @ 
% 0.45/0.68             (k2_tops_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ X2))
% 0.45/0.68          | ~ (v2_funct_1 @ X2)
% 0.45/0.68          | ((k2_relset_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ X2)
% 0.45/0.68              != (k2_struct_0 @ X0))
% 0.45/0.68          | ~ (l1_struct_0 @ X0))),
% 0.45/0.68      inference('sup-', [status(thm)], ['170', '171'])).
% 0.45/0.68  thf('173', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.68         (((k2_relset_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ X2)
% 0.45/0.68            != (k2_struct_0 @ X0))
% 0.45/0.68          | ~ (v2_funct_1 @ X2)
% 0.45/0.68          | (v2_funct_1 @ 
% 0.45/0.68             (k2_tops_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ X2))
% 0.45/0.68          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 0.45/0.68          | ~ (v1_funct_1 @ X2)
% 0.45/0.68          | ~ (l1_struct_0 @ X1)
% 0.45/0.68          | ~ (l1_struct_0 @ X0)
% 0.45/0.68          | ~ (m1_subset_1 @ X2 @ 
% 0.45/0.68               (k1_zfmisc_1 @ 
% 0.45/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (k2_struct_0 @ X0)))))),
% 0.45/0.68      inference('simplify', [status(thm)], ['172'])).
% 0.45/0.68  thf('174', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X1 @ 
% 0.45/0.68             (k1_zfmisc_1 @ 
% 0.45/0.68              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (k2_relat_1 @ sk_C))))
% 0.45/0.68          | ~ (l1_struct_0 @ sk_B)
% 0.45/0.68          | ~ (l1_struct_0 @ X0)
% 0.45/0.68          | ~ (v1_funct_1 @ X1)
% 0.45/0.68          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.45/0.68          | (v2_funct_1 @ 
% 0.45/0.68             (k2_tops_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1))
% 0.45/0.68          | ~ (v2_funct_1 @ X1)
% 0.45/0.68          | ((k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1)
% 0.45/0.68              != (k2_struct_0 @ sk_B)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['169', '173'])).
% 0.45/0.68  thf('175', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('176', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.68      inference('sup+', [status(thm)], ['18', '19'])).
% 0.45/0.68  thf('177', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X1 @ 
% 0.45/0.68             (k1_zfmisc_1 @ 
% 0.45/0.68              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (k2_relat_1 @ sk_C))))
% 0.45/0.68          | ~ (l1_struct_0 @ X0)
% 0.45/0.68          | ~ (v1_funct_1 @ X1)
% 0.45/0.68          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.45/0.68          | (v2_funct_1 @ 
% 0.45/0.68             (k2_tops_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1))
% 0.45/0.68          | ~ (v2_funct_1 @ X1)
% 0.45/0.68          | ((k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1)
% 0.45/0.68              != (k2_relat_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)], ['174', '175', '176'])).
% 0.45/0.68  thf('178', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X0 @ 
% 0.45/0.68             (k1_zfmisc_1 @ 
% 0.45/0.68              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))
% 0.45/0.68          | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ X0)
% 0.45/0.68              != (k2_relat_1 @ sk_C))
% 0.45/0.68          | ~ (v2_funct_1 @ X0)
% 0.45/0.68          | (v2_funct_1 @ 
% 0.45/0.68             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ X0))
% 0.45/0.68          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.68          | ~ (v1_funct_1 @ X0)
% 0.45/0.68          | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['168', '177'])).
% 0.45/0.68  thf('179', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['64', '65', '68'])).
% 0.45/0.68  thf('180', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['64', '65', '68'])).
% 0.45/0.68  thf('181', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['64', '65', '68'])).
% 0.45/0.68  thf('182', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('183', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X0 @ 
% 0.45/0.68             (k1_zfmisc_1 @ 
% 0.45/0.68              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))
% 0.45/0.68          | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ X0)
% 0.45/0.68              != (k2_relat_1 @ sk_C))
% 0.45/0.68          | ~ (v2_funct_1 @ X0)
% 0.45/0.68          | (v2_funct_1 @ 
% 0.45/0.68             (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ X0))
% 0.45/0.68          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.45/0.68          | ~ (v1_funct_1 @ X0))),
% 0.45/0.68      inference('demod', [status(thm)], ['178', '179', '180', '181', '182'])).
% 0.45/0.68  thf('184', plain,
% 0.45/0.68      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.68        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.45/0.68        | (v2_funct_1 @ 
% 0.45/0.68           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.45/0.68        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.68        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68            != (k2_relat_1 @ sk_C)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['167', '183'])).
% 0.45/0.68  thf('185', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('186', plain,
% 0.45/0.68      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.45/0.68      inference('demod', [status(thm)], ['138', '139'])).
% 0.45/0.68  thf('187', plain,
% 0.45/0.68      (![X24 : $i]:
% 0.45/0.68         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.68  thf('188', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.68      inference('demod', [status(thm)], ['132', '133'])).
% 0.45/0.68  thf('189', plain,
% 0.45/0.68      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.45/0.68         (((k2_relset_1 @ X27 @ X26 @ X28) != (X26))
% 0.45/0.68          | ~ (v2_funct_1 @ X28)
% 0.45/0.68          | ((k2_tops_2 @ X27 @ X26 @ X28) = (k2_funct_1 @ X28))
% 0.45/0.68          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 0.45/0.68          | ~ (v1_funct_2 @ X28 @ X27 @ X26)
% 0.45/0.68          | ~ (v1_funct_1 @ X28))),
% 0.45/0.68      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.45/0.68  thf('190', plain,
% 0.45/0.68      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.68        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.45/0.68        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68            = (k2_funct_1 @ sk_C))
% 0.45/0.68        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.68        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68            != (u1_struct_0 @ sk_B)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['188', '189'])).
% 0.45/0.68  thf('191', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('192', plain,
% 0.45/0.68      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.45/0.68      inference('demod', [status(thm)], ['138', '139'])).
% 0.45/0.68  thf('193', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('194', plain,
% 0.45/0.68      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68         = (k2_relat_1 @ sk_C))),
% 0.45/0.68      inference('demod', [status(thm)], ['143', '144'])).
% 0.45/0.68  thf('195', plain,
% 0.45/0.68      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68          = (k2_funct_1 @ sk_C))
% 0.45/0.68        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.45/0.68      inference('demod', [status(thm)], ['190', '191', '192', '193', '194'])).
% 0.45/0.68  thf('196', plain,
% 0.45/0.68      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.45/0.68        | ~ (l1_struct_0 @ sk_B)
% 0.45/0.68        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68            = (k2_funct_1 @ sk_C)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['187', '195'])).
% 0.45/0.68  thf('197', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.68      inference('sup+', [status(thm)], ['18', '19'])).
% 0.45/0.68  thf('198', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('199', plain,
% 0.45/0.68      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.45/0.68        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68            = (k2_funct_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)], ['196', '197', '198'])).
% 0.45/0.68  thf('200', plain,
% 0.45/0.68      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68         = (k2_funct_1 @ sk_C))),
% 0.45/0.68      inference('simplify', [status(thm)], ['199'])).
% 0.45/0.68  thf('201', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('202', plain,
% 0.45/0.68      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68         = (k2_relat_1 @ sk_C))),
% 0.45/0.68      inference('demod', [status(thm)], ['143', '144'])).
% 0.45/0.68  thf('203', plain,
% 0.45/0.68      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.68        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)],
% 0.45/0.68                ['184', '185', '186', '200', '201', '202'])).
% 0.45/0.68  thf('204', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.68      inference('simplify', [status(thm)], ['203'])).
% 0.45/0.68  thf('205', plain,
% 0.45/0.68      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.68          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.68        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)], ['166', '204'])).
% 0.45/0.68  thf(t65_funct_1, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.68       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.45/0.68  thf('206', plain,
% 0.45/0.68      (![X5 : $i]:
% 0.45/0.68         (~ (v2_funct_1 @ X5)
% 0.45/0.68          | ((k2_funct_1 @ (k2_funct_1 @ X5)) = (X5))
% 0.45/0.68          | ~ (v1_funct_1 @ X5)
% 0.45/0.68          | ~ (v1_relat_1 @ X5))),
% 0.45/0.68      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.45/0.68  thf('207', plain,
% 0.45/0.68      (![X24 : $i]:
% 0.45/0.68         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.68  thf('208', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.68      inference('demod', [status(thm)], ['132', '133'])).
% 0.45/0.68  thf('209', plain,
% 0.45/0.68      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.45/0.68         (~ (v2_funct_1 @ X21)
% 0.45/0.68          | ((k2_relset_1 @ X23 @ X22 @ X21) != (X22))
% 0.45/0.68          | (m1_subset_1 @ (k2_funct_1 @ X21) @ 
% 0.45/0.68             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.45/0.68          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.45/0.68          | ~ (v1_funct_2 @ X21 @ X23 @ X22)
% 0.45/0.68          | ~ (v1_funct_1 @ X21))),
% 0.45/0.68      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.45/0.68  thf('210', plain,
% 0.45/0.68      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.68        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.45/0.68        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.68           (k1_zfmisc_1 @ 
% 0.45/0.68            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 0.45/0.68        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68            != (u1_struct_0 @ sk_B))
% 0.45/0.68        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.68      inference('sup-', [status(thm)], ['208', '209'])).
% 0.45/0.68  thf('211', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('212', plain,
% 0.45/0.68      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.45/0.68      inference('demod', [status(thm)], ['138', '139'])).
% 0.45/0.68  thf('213', plain,
% 0.45/0.68      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68         = (k2_relat_1 @ sk_C))),
% 0.45/0.68      inference('demod', [status(thm)], ['143', '144'])).
% 0.45/0.68  thf('214', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('215', plain,
% 0.45/0.68      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.68         (k1_zfmisc_1 @ 
% 0.45/0.68          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 0.45/0.68        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.45/0.68      inference('demod', [status(thm)], ['210', '211', '212', '213', '214'])).
% 0.45/0.68  thf('216', plain,
% 0.45/0.68      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.45/0.68        | ~ (l1_struct_0 @ sk_B)
% 0.45/0.68        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.68           (k1_zfmisc_1 @ 
% 0.45/0.68            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['207', '215'])).
% 0.45/0.68  thf('217', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.68      inference('sup+', [status(thm)], ['18', '19'])).
% 0.45/0.68  thf('218', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('219', plain,
% 0.45/0.68      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.45/0.68        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.68           (k1_zfmisc_1 @ 
% 0.45/0.68            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 0.45/0.68      inference('demod', [status(thm)], ['216', '217', '218'])).
% 0.45/0.68  thf('220', plain,
% 0.45/0.68      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 0.45/0.68      inference('simplify', [status(thm)], ['219'])).
% 0.45/0.68  thf('221', plain,
% 0.45/0.68      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.45/0.68         (~ (v2_funct_1 @ X21)
% 0.45/0.68          | ((k2_relset_1 @ X23 @ X22 @ X21) != (X22))
% 0.45/0.68          | (m1_subset_1 @ (k2_funct_1 @ X21) @ 
% 0.45/0.68             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.45/0.68          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.45/0.68          | ~ (v1_funct_2 @ X21 @ X23 @ X22)
% 0.45/0.68          | ~ (v1_funct_1 @ X21))),
% 0.45/0.68      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.45/0.68  thf('222', plain,
% 0.45/0.68      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.68        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68             (k1_relat_1 @ sk_C))
% 0.45/0.68        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.45/0.68           (k1_zfmisc_1 @ 
% 0.45/0.68            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.45/0.68        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.68            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.45/0.68        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['220', '221'])).
% 0.45/0.68  thf('223', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.68      inference('simplify', [status(thm)], ['151'])).
% 0.45/0.68  thf('224', plain,
% 0.45/0.68      (![X24 : $i]:
% 0.45/0.68         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.45/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.68  thf('225', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.68      inference('demod', [status(thm)], ['132', '133'])).
% 0.45/0.68  thf('226', plain,
% 0.45/0.68      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.45/0.68         (~ (v2_funct_1 @ X21)
% 0.45/0.68          | ((k2_relset_1 @ X23 @ X22 @ X21) != (X22))
% 0.45/0.68          | (v1_funct_2 @ (k2_funct_1 @ X21) @ X22 @ X23)
% 0.45/0.68          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.45/0.68          | ~ (v1_funct_2 @ X21 @ X23 @ X22)
% 0.45/0.68          | ~ (v1_funct_1 @ X21))),
% 0.45/0.68      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.45/0.68  thf('227', plain,
% 0.45/0.68      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.68        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.45/0.68        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68           (k1_relat_1 @ sk_C))
% 0.45/0.68        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68            != (u1_struct_0 @ sk_B))
% 0.45/0.68        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.68      inference('sup-', [status(thm)], ['225', '226'])).
% 0.45/0.68  thf('228', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('229', plain,
% 0.45/0.68      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.45/0.68      inference('demod', [status(thm)], ['138', '139'])).
% 0.45/0.68  thf('230', plain,
% 0.45/0.68      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68         = (k2_relat_1 @ sk_C))),
% 0.45/0.68      inference('demod', [status(thm)], ['143', '144'])).
% 0.45/0.68  thf('231', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('232', plain,
% 0.45/0.68      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68         (k1_relat_1 @ sk_C))
% 0.45/0.68        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.45/0.68      inference('demod', [status(thm)], ['227', '228', '229', '230', '231'])).
% 0.45/0.68  thf('233', plain,
% 0.45/0.68      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.45/0.68        | ~ (l1_struct_0 @ sk_B)
% 0.45/0.68        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68           (k1_relat_1 @ sk_C)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['224', '232'])).
% 0.45/0.68  thf('234', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.68      inference('sup+', [status(thm)], ['18', '19'])).
% 0.45/0.68  thf('235', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('236', plain,
% 0.45/0.68      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.45/0.68        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68           (k1_relat_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)], ['233', '234', '235'])).
% 0.45/0.68  thf('237', plain,
% 0.45/0.68      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68        (k1_relat_1 @ sk_C))),
% 0.45/0.68      inference('simplify', [status(thm)], ['236'])).
% 0.45/0.68  thf('238', plain,
% 0.45/0.68      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.45/0.68         (k1_zfmisc_1 @ 
% 0.45/0.68          (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.45/0.68        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.68            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.45/0.68        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)], ['222', '223', '237'])).
% 0.45/0.68  thf('239', plain,
% 0.45/0.68      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 0.45/0.68      inference('simplify', [status(thm)], ['219'])).
% 0.45/0.68  thf('240', plain,
% 0.45/0.68      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.68         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 0.45/0.68          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.45/0.68      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.68  thf('241', plain,
% 0.45/0.68      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.68         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['239', '240'])).
% 0.45/0.68  thf('242', plain,
% 0.45/0.68      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.45/0.68         (k1_zfmisc_1 @ 
% 0.45/0.68          (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.45/0.68        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.45/0.68        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)], ['238', '241'])).
% 0.45/0.68  thf('243', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.68      inference('simplify', [status(thm)], ['203'])).
% 0.45/0.68  thf('244', plain,
% 0.45/0.68      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.45/0.68         (k1_zfmisc_1 @ 
% 0.45/0.68          (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.45/0.68        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)], ['242', '243'])).
% 0.45/0.68  thf(t55_funct_1, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.68       ( ( v2_funct_1 @ A ) =>
% 0.45/0.68         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.45/0.68           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.45/0.68  thf('245', plain,
% 0.45/0.68      (![X4 : $i]:
% 0.45/0.68         (~ (v2_funct_1 @ X4)
% 0.45/0.68          | ((k1_relat_1 @ X4) = (k2_relat_1 @ (k2_funct_1 @ X4)))
% 0.45/0.68          | ~ (v1_funct_1 @ X4)
% 0.45/0.68          | ~ (v1_relat_1 @ X4))),
% 0.45/0.68      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.45/0.68  thf('246', plain,
% 0.45/0.68      (![X4 : $i]:
% 0.45/0.68         (~ (v2_funct_1 @ X4)
% 0.45/0.68          | ((k2_relat_1 @ X4) = (k1_relat_1 @ (k2_funct_1 @ X4)))
% 0.45/0.68          | ~ (v1_funct_1 @ X4)
% 0.45/0.68          | ~ (v1_relat_1 @ X4))),
% 0.45/0.68      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.45/0.68  thf('247', plain,
% 0.45/0.68      (![X5 : $i]:
% 0.45/0.68         (~ (v2_funct_1 @ X5)
% 0.45/0.68          | ((k2_funct_1 @ (k2_funct_1 @ X5)) = (X5))
% 0.45/0.68          | ~ (v1_funct_1 @ X5)
% 0.45/0.68          | ~ (v1_relat_1 @ X5))),
% 0.45/0.68      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.45/0.68  thf('248', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.68      inference('simplify', [status(thm)], ['203'])).
% 0.45/0.68  thf('249', plain,
% 0.45/0.68      (![X5 : $i]:
% 0.45/0.68         (~ (v2_funct_1 @ X5)
% 0.45/0.68          | ((k2_funct_1 @ (k2_funct_1 @ X5)) = (X5))
% 0.45/0.68          | ~ (v1_funct_1 @ X5)
% 0.45/0.68          | ~ (v1_relat_1 @ X5))),
% 0.45/0.68      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.45/0.68  thf('250', plain,
% 0.45/0.68      (![X4 : $i]:
% 0.45/0.68         (~ (v2_funct_1 @ X4)
% 0.45/0.68          | ((k1_relat_1 @ X4) = (k2_relat_1 @ (k2_funct_1 @ X4)))
% 0.45/0.68          | ~ (v1_funct_1 @ X4)
% 0.45/0.68          | ~ (v1_relat_1 @ X4))),
% 0.45/0.68      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.45/0.68  thf('251', plain,
% 0.45/0.68      (![X5 : $i]:
% 0.45/0.68         (~ (v2_funct_1 @ X5)
% 0.45/0.68          | ((k2_funct_1 @ (k2_funct_1 @ X5)) = (X5))
% 0.45/0.68          | ~ (v1_funct_1 @ X5)
% 0.45/0.68          | ~ (v1_relat_1 @ X5))),
% 0.45/0.68      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.45/0.68  thf('252', plain,
% 0.45/0.68      (![X4 : $i]:
% 0.45/0.68         (~ (v2_funct_1 @ X4)
% 0.45/0.68          | ((k2_relat_1 @ X4) = (k1_relat_1 @ (k2_funct_1 @ X4)))
% 0.45/0.68          | ~ (v1_funct_1 @ X4)
% 0.45/0.68          | ~ (v1_relat_1 @ X4))),
% 0.45/0.68      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.45/0.68  thf('253', plain,
% 0.45/0.68      (![X15 : $i, X16 : $i]:
% 0.45/0.68         (((k1_relat_1 @ X16) != (X15))
% 0.45/0.68          | (v1_partfun1 @ X16 @ X15)
% 0.45/0.68          | ~ (v4_relat_1 @ X16 @ X15)
% 0.45/0.68          | ~ (v1_relat_1 @ X16))),
% 0.45/0.68      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.45/0.68  thf('254', plain,
% 0.45/0.68      (![X16 : $i]:
% 0.45/0.68         (~ (v1_relat_1 @ X16)
% 0.45/0.68          | ~ (v4_relat_1 @ X16 @ (k1_relat_1 @ X16))
% 0.45/0.68          | (v1_partfun1 @ X16 @ (k1_relat_1 @ X16)))),
% 0.45/0.68      inference('simplify', [status(thm)], ['253'])).
% 0.45/0.68  thf('255', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.45/0.68          | ~ (v1_relat_1 @ X0)
% 0.45/0.68          | ~ (v1_funct_1 @ X0)
% 0.45/0.68          | ~ (v2_funct_1 @ X0)
% 0.45/0.68          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.45/0.68          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['252', '254'])).
% 0.45/0.68  thf('256', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (~ (v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.45/0.68          | ~ (v1_relat_1 @ X0)
% 0.45/0.68          | ~ (v1_funct_1 @ X0)
% 0.45/0.68          | ~ (v2_funct_1 @ X0)
% 0.45/0.68          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.45/0.68          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.45/0.68             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.45/0.68          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.68          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.68          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['251', '255'])).
% 0.45/0.68  thf('257', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.45/0.68          | ~ (v1_relat_1 @ X0)
% 0.45/0.68          | ~ (v1_funct_1 @ X0)
% 0.45/0.68          | ~ (v2_funct_1 @ X0)
% 0.45/0.68          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.68          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.68          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.68          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.45/0.68             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.45/0.68          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.45/0.68          | ~ (v2_funct_1 @ X0)
% 0.45/0.68          | ~ (v1_funct_1 @ X0)
% 0.45/0.68          | ~ (v1_relat_1 @ X0))),
% 0.45/0.68      inference('sup-', [status(thm)], ['250', '256'])).
% 0.45/0.68  thf('258', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.45/0.68          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.45/0.68             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.45/0.68          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.68          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.68          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.68          | ~ (v2_funct_1 @ X0)
% 0.45/0.68          | ~ (v1_funct_1 @ X0)
% 0.45/0.68          | ~ (v1_relat_1 @ X0)
% 0.45/0.68          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.45/0.68      inference('simplify', [status(thm)], ['257'])).
% 0.45/0.68  thf('259', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (~ (v1_relat_1 @ X0)
% 0.45/0.68          | ~ (v1_relat_1 @ X0)
% 0.45/0.68          | ~ (v1_funct_1 @ X0)
% 0.45/0.68          | ~ (v2_funct_1 @ X0)
% 0.45/0.68          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.45/0.68          | ~ (v1_relat_1 @ X0)
% 0.45/0.68          | ~ (v1_funct_1 @ X0)
% 0.45/0.68          | ~ (v2_funct_1 @ X0)
% 0.45/0.68          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.68          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.68          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.68          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.45/0.68             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['249', '258'])).
% 0.45/0.68  thf('260', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.45/0.68           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.45/0.68          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.68          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.68          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.68          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.45/0.68          | ~ (v2_funct_1 @ X0)
% 0.45/0.68          | ~ (v1_funct_1 @ X0)
% 0.45/0.68          | ~ (v1_relat_1 @ X0))),
% 0.45/0.68      inference('simplify', [status(thm)], ['259'])).
% 0.45/0.68  thf('261', plain,
% 0.45/0.68      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.68        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.68        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.68        | ~ (v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.45/0.68        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.68        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.68        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.45/0.68           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['248', '260'])).
% 0.45/0.68  thf('262', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.68      inference('demod', [status(thm)], ['51', '52'])).
% 0.45/0.68  thf('263', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('264', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('265', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['58', '59'])).
% 0.45/0.68  thf('266', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['48', '53', '60'])).
% 0.45/0.68  thf('267', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 0.45/0.68      inference('demod', [status(thm)], ['265', '266'])).
% 0.45/0.68  thf('268', plain,
% 0.45/0.68      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.45/0.68      inference('simplify', [status(thm)], ['127'])).
% 0.45/0.68  thf('269', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.45/0.68          | (v1_relat_1 @ X0)
% 0.45/0.68          | ~ (v1_relat_1 @ X1))),
% 0.45/0.68      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.45/0.68  thf('270', plain,
% 0.45/0.68      ((~ (v1_relat_1 @ 
% 0.45/0.68           (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C)))
% 0.45/0.68        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['268', '269'])).
% 0.45/0.68  thf('271', plain,
% 0.45/0.68      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.45/0.68      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.45/0.68  thf('272', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.68      inference('demod', [status(thm)], ['270', '271'])).
% 0.45/0.68  thf('273', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.68      inference('simplify', [status(thm)], ['151'])).
% 0.45/0.68  thf('274', plain,
% 0.45/0.68      ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.45/0.68        (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.68      inference('demod', [status(thm)],
% 0.45/0.68                ['261', '262', '263', '264', '267', '272', '273'])).
% 0.45/0.68  thf('275', plain,
% 0.45/0.68      (((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.45/0.68        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.68        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.68        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.68      inference('sup+', [status(thm)], ['247', '274'])).
% 0.45/0.68  thf('276', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.68      inference('demod', [status(thm)], ['51', '52'])).
% 0.45/0.68  thf('277', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('278', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('279', plain,
% 0.45/0.68      ((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.68      inference('demod', [status(thm)], ['275', '276', '277', '278'])).
% 0.45/0.68  thf('280', plain,
% 0.45/0.68      (((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.68        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.68        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.68        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.68      inference('sup+', [status(thm)], ['246', '279'])).
% 0.45/0.68  thf('281', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.68      inference('demod', [status(thm)], ['270', '271'])).
% 0.45/0.68  thf('282', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.68      inference('simplify', [status(thm)], ['151'])).
% 0.45/0.68  thf('283', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.68      inference('simplify', [status(thm)], ['203'])).
% 0.45/0.68  thf('284', plain,
% 0.45/0.68      ((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)], ['280', '281', '282', '283'])).
% 0.45/0.68  thf('285', plain,
% 0.45/0.68      (![X15 : $i, X16 : $i]:
% 0.45/0.68         (~ (v1_partfun1 @ X16 @ X15)
% 0.45/0.68          | ((k1_relat_1 @ X16) = (X15))
% 0.45/0.68          | ~ (v4_relat_1 @ X16 @ X15)
% 0.45/0.68          | ~ (v1_relat_1 @ X16))),
% 0.45/0.68      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.45/0.68  thf('286', plain,
% 0.45/0.68      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.68        | ~ (v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.68        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['284', '285'])).
% 0.45/0.68  thf('287', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.68      inference('demod', [status(thm)], ['51', '52'])).
% 0.45/0.68  thf('288', plain,
% 0.45/0.68      ((~ (v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.68        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.68      inference('demod', [status(thm)], ['286', '287'])).
% 0.45/0.68  thf('289', plain,
% 0.45/0.68      ((~ (v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.45/0.68        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.68        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.68        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.68        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['245', '288'])).
% 0.45/0.68  thf('290', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 0.45/0.68      inference('demod', [status(thm)], ['265', '266'])).
% 0.45/0.68  thf('291', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.68      inference('demod', [status(thm)], ['51', '52'])).
% 0.45/0.68  thf('292', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('293', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('294', plain,
% 0.45/0.68      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)], ['289', '290', '291', '292', '293'])).
% 0.45/0.68  thf('295', plain,
% 0.45/0.68      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.45/0.68         (k1_zfmisc_1 @ 
% 0.45/0.68          (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.45/0.68        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)], ['244', '294'])).
% 0.45/0.68  thf('296', plain,
% 0.45/0.68      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.68      inference('simplify', [status(thm)], ['295'])).
% 0.45/0.68  thf('297', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(redefinition_r2_funct_2, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.68     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.68         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.45/0.68         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.45/0.68         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.68       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.45/0.68  thf('298', plain,
% 0.45/0.68      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.45/0.68          | ~ (v1_funct_2 @ X17 @ X18 @ X19)
% 0.45/0.68          | ~ (v1_funct_1 @ X17)
% 0.45/0.68          | ~ (v1_funct_1 @ X20)
% 0.45/0.68          | ~ (v1_funct_2 @ X20 @ X18 @ X19)
% 0.45/0.68          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.45/0.68          | ((X17) = (X20))
% 0.45/0.68          | ~ (r2_funct_2 @ X18 @ X19 @ X17 @ X20))),
% 0.45/0.68      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.45/0.68  thf('299', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.45/0.68             X0)
% 0.45/0.68          | ((sk_C) = (X0))
% 0.45/0.68          | ~ (m1_subset_1 @ X0 @ 
% 0.45/0.68               (k1_zfmisc_1 @ 
% 0.45/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.45/0.68          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.68          | ~ (v1_funct_1 @ X0)
% 0.45/0.68          | ~ (v1_funct_1 @ sk_C)
% 0.45/0.68          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['297', '298'])).
% 0.45/0.68  thf('300', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('301', plain,
% 0.45/0.68      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('302', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.45/0.68             X0)
% 0.45/0.68          | ((sk_C) = (X0))
% 0.45/0.68          | ~ (m1_subset_1 @ X0 @ 
% 0.45/0.68               (k1_zfmisc_1 @ 
% 0.45/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.45/0.68          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.68          | ~ (v1_funct_1 @ X0))),
% 0.45/0.68      inference('demod', [status(thm)], ['299', '300', '301'])).
% 0.45/0.68  thf('303', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['64', '65', '68'])).
% 0.45/0.68  thf('304', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['64', '65', '68'])).
% 0.45/0.68  thf('305', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['64', '65', '68'])).
% 0.45/0.68  thf('306', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.45/0.68             X0)
% 0.45/0.68          | ((sk_C) = (X0))
% 0.45/0.68          | ~ (m1_subset_1 @ X0 @ 
% 0.45/0.68               (k1_zfmisc_1 @ 
% 0.45/0.68                (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.45/0.68          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.45/0.68          | ~ (v1_funct_1 @ X0))),
% 0.45/0.68      inference('demod', [status(thm)], ['302', '303', '304', '305'])).
% 0.45/0.68  thf('307', plain,
% 0.45/0.68      ((~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.68        | ~ (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.45/0.68             (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.45/0.68        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.68        | ~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.45/0.68             (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['296', '306'])).
% 0.45/0.68  thf('308', plain,
% 0.45/0.68      (![X4 : $i]:
% 0.45/0.68         (~ (v2_funct_1 @ X4)
% 0.45/0.68          | ((k1_relat_1 @ X4) = (k2_relat_1 @ (k2_funct_1 @ X4)))
% 0.45/0.68          | ~ (v1_funct_1 @ X4)
% 0.45/0.68          | ~ (v1_relat_1 @ X4))),
% 0.45/0.68      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.45/0.68  thf('309', plain,
% 0.45/0.68      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 0.45/0.68      inference('simplify', [status(thm)], ['219'])).
% 0.45/0.68  thf('310', plain,
% 0.45/0.68      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.45/0.68         (~ (v2_funct_1 @ X21)
% 0.45/0.68          | ((k2_relset_1 @ X23 @ X22 @ X21) != (X22))
% 0.45/0.68          | (v1_funct_1 @ (k2_funct_1 @ X21))
% 0.45/0.68          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.45/0.68          | ~ (v1_funct_2 @ X21 @ X23 @ X22)
% 0.45/0.68          | ~ (v1_funct_1 @ X21))),
% 0.45/0.68      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.45/0.68  thf('311', plain,
% 0.45/0.68      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.68        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68             (k1_relat_1 @ sk_C))
% 0.45/0.68        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.68        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.68            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.45/0.68        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['309', '310'])).
% 0.45/0.68  thf('312', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.68      inference('simplify', [status(thm)], ['151'])).
% 0.45/0.68  thf('313', plain,
% 0.45/0.68      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68        (k1_relat_1 @ sk_C))),
% 0.45/0.68      inference('simplify', [status(thm)], ['236'])).
% 0.45/0.68  thf('314', plain,
% 0.45/0.68      (((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.68        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.68            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.45/0.68        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)], ['311', '312', '313'])).
% 0.45/0.68  thf('315', plain,
% 0.45/0.68      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.68         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['239', '240'])).
% 0.45/0.68  thf('316', plain,
% 0.45/0.68      (((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.68        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.45/0.68        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)], ['314', '315'])).
% 0.45/0.68  thf('317', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.68      inference('simplify', [status(thm)], ['203'])).
% 0.45/0.68  thf('318', plain,
% 0.45/0.68      (((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.68        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)], ['316', '317'])).
% 0.45/0.68  thf('319', plain,
% 0.45/0.68      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 0.45/0.68        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.68        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.68        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.68        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['308', '318'])).
% 0.45/0.68  thf('320', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.68      inference('demod', [status(thm)], ['51', '52'])).
% 0.45/0.68  thf('321', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('322', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('323', plain,
% 0.45/0.68      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 0.45/0.68        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.68      inference('demod', [status(thm)], ['319', '320', '321', '322'])).
% 0.45/0.68  thf('324', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.68      inference('simplify', [status(thm)], ['323'])).
% 0.45/0.68  thf('325', plain,
% 0.45/0.68      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 0.45/0.68      inference('simplify', [status(thm)], ['219'])).
% 0.45/0.68  thf('326', plain,
% 0.45/0.68      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.45/0.68         (~ (v2_funct_1 @ X21)
% 0.45/0.68          | ((k2_relset_1 @ X23 @ X22 @ X21) != (X22))
% 0.45/0.68          | (v1_funct_2 @ (k2_funct_1 @ X21) @ X22 @ X23)
% 0.45/0.68          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.45/0.68          | ~ (v1_funct_2 @ X21 @ X23 @ X22)
% 0.45/0.68          | ~ (v1_funct_1 @ X21))),
% 0.45/0.68      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.45/0.68  thf('327', plain,
% 0.45/0.68      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.68        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68             (k1_relat_1 @ sk_C))
% 0.45/0.68        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.45/0.68           (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.45/0.68        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.68            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.45/0.68        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['325', '326'])).
% 0.45/0.68  thf('328', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.68      inference('simplify', [status(thm)], ['151'])).
% 0.45/0.68  thf('329', plain,
% 0.45/0.68      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68        (k1_relat_1 @ sk_C))),
% 0.45/0.68      inference('simplify', [status(thm)], ['236'])).
% 0.45/0.68  thf('330', plain,
% 0.45/0.68      (((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.45/0.68         (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.45/0.68        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.68            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.45/0.68        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)], ['327', '328', '329'])).
% 0.45/0.68  thf('331', plain,
% 0.45/0.68      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.68         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['239', '240'])).
% 0.45/0.68  thf('332', plain,
% 0.45/0.68      (((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.45/0.68         (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.45/0.68        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.45/0.68        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)], ['330', '331'])).
% 0.45/0.68  thf('333', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.68      inference('simplify', [status(thm)], ['203'])).
% 0.45/0.68  thf('334', plain,
% 0.45/0.68      (((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.45/0.68         (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.45/0.68        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)], ['332', '333'])).
% 0.45/0.68  thf('335', plain,
% 0.45/0.68      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)], ['289', '290', '291', '292', '293'])).
% 0.45/0.68  thf('336', plain,
% 0.45/0.68      (((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.45/0.68         (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.45/0.68        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)], ['334', '335'])).
% 0.45/0.68  thf('337', plain,
% 0.45/0.68      ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.45/0.68        (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.45/0.68      inference('simplify', [status(thm)], ['336'])).
% 0.45/0.68  thf('338', plain,
% 0.45/0.68      ((((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.68        | ~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.45/0.68             (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.68      inference('demod', [status(thm)], ['307', '324', '337'])).
% 0.45/0.68  thf('339', plain,
% 0.45/0.68      ((~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.45/0.68           sk_C)
% 0.45/0.68        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.68        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.68        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.68        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['206', '338'])).
% 0.45/0.68  thf('340', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.68      inference('demod', [status(thm)], ['132', '133'])).
% 0.45/0.68  thf('341', plain,
% 0.45/0.68      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.45/0.68          | ~ (v1_funct_2 @ X17 @ X18 @ X19)
% 0.45/0.68          | ~ (v1_funct_1 @ X17)
% 0.45/0.68          | ~ (v1_funct_1 @ X20)
% 0.45/0.68          | ~ (v1_funct_2 @ X20 @ X18 @ X19)
% 0.45/0.68          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.45/0.68          | (r2_funct_2 @ X18 @ X19 @ X17 @ X20)
% 0.45/0.68          | ((X17) != (X20)))),
% 0.45/0.68      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.45/0.68  thf('342', plain,
% 0.45/0.68      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.68         ((r2_funct_2 @ X18 @ X19 @ X20 @ X20)
% 0.45/0.68          | ~ (v1_funct_1 @ X20)
% 0.45/0.68          | ~ (v1_funct_2 @ X20 @ X18 @ X19)
% 0.45/0.68          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.45/0.68      inference('simplify', [status(thm)], ['341'])).
% 0.45/0.68  thf('343', plain,
% 0.45/0.68      ((~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.45/0.68        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.68        | (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.45/0.68           sk_C))),
% 0.45/0.68      inference('sup-', [status(thm)], ['340', '342'])).
% 0.45/0.68  thf('344', plain,
% 0.45/0.68      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.45/0.68      inference('demod', [status(thm)], ['138', '139'])).
% 0.45/0.68  thf('345', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('346', plain,
% 0.45/0.68      ((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.45/0.68      inference('demod', [status(thm)], ['343', '344', '345'])).
% 0.45/0.68  thf('347', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.68      inference('demod', [status(thm)], ['51', '52'])).
% 0.45/0.68  thf('348', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('349', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('350', plain, (((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)], ['339', '346', '347', '348', '349'])).
% 0.45/0.68  thf('351', plain,
% 0.45/0.68      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)], ['289', '290', '291', '292', '293'])).
% 0.45/0.68  thf('352', plain,
% 0.45/0.68      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.68          (k2_funct_1 @ sk_C)) = (sk_C))
% 0.45/0.68        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)], ['205', '350', '351'])).
% 0.45/0.68  thf('353', plain,
% 0.45/0.68      (((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.68         (k2_funct_1 @ sk_C)) = (sk_C))),
% 0.45/0.68      inference('simplify', [status(thm)], ['352'])).
% 0.45/0.68  thf('354', plain,
% 0.45/0.68      ((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.45/0.68      inference('demod', [status(thm)], ['343', '344', '345'])).
% 0.45/0.68  thf('355', plain, ($false),
% 0.45/0.68      inference('demod', [status(thm)], ['119', '353', '354'])).
% 0.45/0.68  
% 0.45/0.68  % SZS output end Refutation
% 0.45/0.68  
% 0.45/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
