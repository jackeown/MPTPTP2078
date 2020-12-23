%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gougTQMXGY

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:18 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  289 (1899 expanded)
%              Number of leaves         :   43 ( 574 expanded)
%              Depth                    :   34
%              Number of atoms          : 2818 (40683 expanded)
%              Number of equality atoms :  131 (1179 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X9 ) )
        = X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
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
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( v1_partfun1 @ X16 @ X17 )
      | ~ ( v1_funct_2 @ X16 @ X17 @ X18 )
      | ~ ( v1_funct_1 @ X16 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('16',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_partfun1 @ X20 @ X19 )
      | ( ( k1_relat_1 @ X20 )
        = X19 )
      | ~ ( v4_relat_1 @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('22',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('24',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v4_relat_1 @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('25',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','22','25'])).

thf('27',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( v1_partfun1 @ X16 @ X17 )
      | ~ ( v1_funct_2 @ X16 @ X17 @ X18 )
      | ~ ( v1_funct_1 @ X16 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('36',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34','39'])).

thf('41',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_partfun1 @ X20 @ X19 )
      | ( ( k1_relat_1 @ X20 )
        = X19 )
      | ~ ( v4_relat_1 @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('45',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v4_relat_1 @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('46',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43','46'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('48',plain,(
    ! [X29: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('49',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','53'])).

thf('55',plain,(
    ! [X29: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('56',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('62',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('63',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['9','60','61','62'])).

thf('64',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('66',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

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

thf('69',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k2_relset_1 @ X31 @ X30 @ X32 )
       != X30 )
      | ~ ( v2_funct_1 @ X32 )
      | ( ( k2_tops_2 @ X31 @ X30 @ X32 )
        = ( k2_funct_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('70',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('73',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('74',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('79',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('80',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['78','83'])).

thf('85',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['70','71','76','77','86'])).

thf('88',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['63','88'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('90',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k1_relat_1 @ X7 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('91',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

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

thf('92',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k2_relset_1 @ X27 @ X26 @ X25 )
       != X26 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('93',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('96',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('97',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['93','94','95','96','97'])).

thf('99',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k2_relset_1 @ X31 @ X30 @ X32 )
       != X30 )
      | ~ ( v2_funct_1 @ X32 )
      | ( ( k2_tops_2 @ X31 @ X30 @ X32 )
        = ( k2_funct_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('101',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('103',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k2_relset_1 @ X27 @ X26 @ X25 )
       != X26 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('104',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('107',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('108',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['104','105','106','107','108'])).

thf('110',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('112',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k2_relset_1 @ X27 @ X26 @ X25 )
       != X26 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X25 ) @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('113',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('116',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('117',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['113','114','115','116','117'])).

thf('119',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('121',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('122',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['101','110','119','122'])).

thf('124',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X9 ) )
        = X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('125',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X8 ) @ X8 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('126',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('127',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('128',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_relat_1 @ X7 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t53_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ? [B: $i] :
            ( ( ( k5_relat_1 @ A @ B )
              = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
            & ( v1_funct_1 @ B )
            & ( v1_relat_1 @ B ) )
       => ( v2_funct_1 @ A ) ) ) )).

thf('129',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ( ( k5_relat_1 @ X6 @ X5 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X6 ) ) )
      | ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t53_funct_1])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['127','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['126','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k2_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['125','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('139',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('141',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X9 ) )
        = X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('144',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('145',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('146',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X9 ) )
        = X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('148',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('149',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('150',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X9 ) )
        = X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('151',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k5_relat_1 @ X8 @ ( k2_funct_1 @ X8 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['149','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['148','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['147','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['146','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['145','159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['144','161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['143','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['142','165'])).

thf('167',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['141','166'])).

thf('168',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['109'])).

thf('169',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('172',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['167','168','169','170','171'])).

thf('173',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['136','172'])).

thf('174',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('175',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference(demod,[status(thm)],['173','174','175','176'])).

thf('178',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['124','177'])).

thf('179',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_relat_1 @ X7 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('180',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('182',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_relat_1 @ X7 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('186',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k1_relat_1 @ X20 )
       != X19 )
      | ( v1_partfun1 @ X20 @ X19 )
      | ~ ( v4_relat_1 @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('187',plain,(
    ! [X20: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v4_relat_1 @ X20 @ ( k1_relat_1 @ X20 ) )
      | ( v1_partfun1 @ X20 @ ( k1_relat_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['186'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['185','187'])).

thf('189',plain,
    ( ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['184','188'])).

thf('190',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('193',plain,
    ( ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['189','190','191','192'])).

thf('194',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('195',plain,
    ( ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['193','194'])).

thf('196',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('197',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v4_relat_1 @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('198',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['195','198'])).

thf('200',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['179','199'])).

thf('201',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['182','183'])).

thf('202',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('203',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['200','201','202','203','204'])).

thf('206',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_partfun1 @ X20 @ X19 )
      | ( ( k1_relat_1 @ X20 )
        = X19 )
      | ~ ( v4_relat_1 @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('207',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('209',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('210',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['207','208','209'])).

thf('211',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('212',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['178','210','211','212','213'])).

thf('215',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ( ( k5_relat_1 @ X6 @ X5 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X6 ) ) )
      | ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t53_funct_1])).

thf('216',plain,
    ( ( ( k6_relat_1 @ ( k2_struct_0 @ sk_B ) )
     != ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['207','208','209'])).

thf('218',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('219',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['109'])).

thf('220',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('222',plain,
    ( ( ( k6_relat_1 @ ( k2_struct_0 @ sk_B ) )
     != ( k6_relat_1 @ ( k2_struct_0 @ sk_B ) ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['216','217','218','219','220','221'])).

thf('223',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['222'])).

thf('224',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['123','223'])).

thf('225',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['90','224'])).

thf('226',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('227',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('228',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['225','226','227','228','229'])).

thf('231',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['230'])).

thf('232',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['89','231'])).

thf('233',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','232'])).

thf('234',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

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

thf('235',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X22 @ X23 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( r2_funct_2 @ X22 @ X23 @ X21 @ X24 )
      | ( X21 != X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('236',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_funct_2 @ X22 @ X23 @ X24 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(simplify,[status(thm)],['235'])).

thf('237',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['234','236'])).

thf('238',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('239',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['237','238','239'])).

thf('241',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('242',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    $false ),
    inference(demod,[status(thm)],['233','240','241','242','243'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gougTQMXGY
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:26:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.40/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.61  % Solved by: fo/fo7.sh
% 0.40/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.61  % done 481 iterations in 0.163s
% 0.40/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.61  % SZS output start Refutation
% 0.40/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.61  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.40/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.40/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.40/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.61  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.40/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.61  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.40/0.61  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.40/0.61  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.40/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.40/0.61  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.40/0.61  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.40/0.61  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.40/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.40/0.61  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.40/0.61  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.40/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.61  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.40/0.61  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.40/0.61  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.40/0.61  thf(t65_funct_1, axiom,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.40/0.61       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.40/0.61  thf('0', plain,
% 0.40/0.61      (![X9 : $i]:
% 0.40/0.61         (~ (v2_funct_1 @ X9)
% 0.40/0.61          | ((k2_funct_1 @ (k2_funct_1 @ X9)) = (X9))
% 0.40/0.61          | ~ (v1_funct_1 @ X9)
% 0.40/0.61          | ~ (v1_relat_1 @ X9))),
% 0.40/0.61      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.40/0.61  thf(d3_struct_0, axiom,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.40/0.61  thf('1', plain,
% 0.40/0.61      (![X28 : $i]:
% 0.40/0.61         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 0.40/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.61  thf('2', plain,
% 0.40/0.61      (![X28 : $i]:
% 0.40/0.61         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 0.40/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.61  thf(t64_tops_2, conjecture,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ( l1_struct_0 @ A ) =>
% 0.40/0.61       ( ![B:$i]:
% 0.40/0.61         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.40/0.61           ( ![C:$i]:
% 0.40/0.61             ( ( ( v1_funct_1 @ C ) & 
% 0.40/0.61                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.40/0.61                 ( m1_subset_1 @
% 0.40/0.61                   C @ 
% 0.40/0.61                   ( k1_zfmisc_1 @
% 0.40/0.61                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.40/0.61               ( ( ( ( k2_relset_1 @
% 0.40/0.61                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.40/0.61                     ( k2_struct_0 @ B ) ) & 
% 0.40/0.61                   ( v2_funct_1 @ C ) ) =>
% 0.40/0.61                 ( r2_funct_2 @
% 0.40/0.61                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.40/0.61                   ( k2_tops_2 @
% 0.40/0.61                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.40/0.61                     ( k2_tops_2 @
% 0.40/0.61                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.40/0.61                   C ) ) ) ) ) ) ))).
% 0.40/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.61    (~( ![A:$i]:
% 0.40/0.61        ( ( l1_struct_0 @ A ) =>
% 0.40/0.61          ( ![B:$i]:
% 0.40/0.61            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.40/0.61              ( ![C:$i]:
% 0.40/0.61                ( ( ( v1_funct_1 @ C ) & 
% 0.40/0.61                    ( v1_funct_2 @
% 0.40/0.61                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.40/0.61                    ( m1_subset_1 @
% 0.40/0.61                      C @ 
% 0.40/0.61                      ( k1_zfmisc_1 @
% 0.40/0.61                        ( k2_zfmisc_1 @
% 0.40/0.61                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.40/0.61                  ( ( ( ( k2_relset_1 @
% 0.40/0.61                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.40/0.61                        ( k2_struct_0 @ B ) ) & 
% 0.40/0.61                      ( v2_funct_1 @ C ) ) =>
% 0.40/0.61                    ( r2_funct_2 @
% 0.40/0.61                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.40/0.61                      ( k2_tops_2 @
% 0.40/0.61                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.40/0.61                        ( k2_tops_2 @
% 0.40/0.61                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.40/0.61                      C ) ) ) ) ) ) ) )),
% 0.40/0.61    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.40/0.61  thf('3', plain,
% 0.40/0.61      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.61          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.61           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.40/0.61          sk_C)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('4', plain,
% 0.40/0.61      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.61           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.61            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.40/0.61           sk_C)
% 0.40/0.61        | ~ (l1_struct_0 @ sk_B))),
% 0.40/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.40/0.61  thf('5', plain, ((l1_struct_0 @ sk_B)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('6', plain,
% 0.40/0.61      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.61          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.61           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.40/0.61          sk_C)),
% 0.40/0.61      inference('demod', [status(thm)], ['4', '5'])).
% 0.40/0.61  thf('7', plain,
% 0.40/0.61      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.61           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.61            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.40/0.61           sk_C)
% 0.40/0.61        | ~ (l1_struct_0 @ sk_B))),
% 0.40/0.61      inference('sup-', [status(thm)], ['1', '6'])).
% 0.40/0.61  thf('8', plain, ((l1_struct_0 @ sk_B)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('9', plain,
% 0.40/0.61      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.61          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.40/0.61           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.40/0.61          sk_C)),
% 0.40/0.61      inference('demod', [status(thm)], ['7', '8'])).
% 0.40/0.61  thf('10', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_C @ 
% 0.40/0.61        (k1_zfmisc_1 @ 
% 0.40/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf(cc5_funct_2, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.40/0.61       ( ![C:$i]:
% 0.40/0.61         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.61           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.40/0.61             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.40/0.61  thf('11', plain,
% 0.40/0.61      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.40/0.61         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.40/0.61          | (v1_partfun1 @ X16 @ X17)
% 0.40/0.61          | ~ (v1_funct_2 @ X16 @ X17 @ X18)
% 0.40/0.61          | ~ (v1_funct_1 @ X16)
% 0.40/0.61          | (v1_xboole_0 @ X18))),
% 0.40/0.61      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.40/0.61  thf('12', plain,
% 0.40/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.40/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.61        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.40/0.61        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['10', '11'])).
% 0.40/0.61  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('14', plain,
% 0.40/0.61      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('15', plain,
% 0.40/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.40/0.61        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.40/0.61      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.40/0.61  thf(d4_partfun1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.40/0.61       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.40/0.61  thf('16', plain,
% 0.40/0.61      (![X19 : $i, X20 : $i]:
% 0.40/0.61         (~ (v1_partfun1 @ X20 @ X19)
% 0.40/0.61          | ((k1_relat_1 @ X20) = (X19))
% 0.40/0.61          | ~ (v4_relat_1 @ X20 @ X19)
% 0.40/0.61          | ~ (v1_relat_1 @ X20))),
% 0.40/0.61      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.40/0.61  thf('17', plain,
% 0.40/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.40/0.61        | ~ (v1_relat_1 @ sk_C)
% 0.40/0.61        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.40/0.61        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['15', '16'])).
% 0.40/0.61  thf('18', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_C @ 
% 0.40/0.61        (k1_zfmisc_1 @ 
% 0.40/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf(cc2_relat_1, axiom,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ( v1_relat_1 @ A ) =>
% 0.40/0.61       ( ![B:$i]:
% 0.40/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.40/0.61  thf('19', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.40/0.61          | (v1_relat_1 @ X0)
% 0.40/0.61          | ~ (v1_relat_1 @ X1))),
% 0.40/0.61      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.40/0.61  thf('20', plain,
% 0.40/0.61      ((~ (v1_relat_1 @ 
% 0.40/0.61           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.40/0.61        | (v1_relat_1 @ sk_C))),
% 0.40/0.61      inference('sup-', [status(thm)], ['18', '19'])).
% 0.40/0.61  thf(fc6_relat_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.40/0.61  thf('21', plain,
% 0.40/0.61      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.40/0.61      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.40/0.61  thf('22', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.61      inference('demod', [status(thm)], ['20', '21'])).
% 0.40/0.61  thf('23', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_C @ 
% 0.40/0.61        (k1_zfmisc_1 @ 
% 0.40/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf(cc2_relset_1, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.61       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.40/0.61  thf('24', plain,
% 0.40/0.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.40/0.61         ((v4_relat_1 @ X10 @ X11)
% 0.40/0.61          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.40/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.40/0.61  thf('25', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.40/0.61      inference('sup-', [status(thm)], ['23', '24'])).
% 0.40/0.61  thf('26', plain,
% 0.40/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.40/0.61        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.40/0.61      inference('demod', [status(thm)], ['17', '22', '25'])).
% 0.40/0.61  thf('27', plain,
% 0.40/0.61      (![X28 : $i]:
% 0.40/0.61         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 0.40/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.61  thf('28', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_C @ 
% 0.40/0.61        (k1_zfmisc_1 @ 
% 0.40/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('29', plain,
% 0.40/0.61      (((m1_subset_1 @ sk_C @ 
% 0.40/0.61         (k1_zfmisc_1 @ 
% 0.40/0.61          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.40/0.61        | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.61      inference('sup+', [status(thm)], ['27', '28'])).
% 0.40/0.61  thf('30', plain, ((l1_struct_0 @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('31', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_C @ 
% 0.40/0.61        (k1_zfmisc_1 @ 
% 0.40/0.61         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.61      inference('demod', [status(thm)], ['29', '30'])).
% 0.40/0.61  thf('32', plain,
% 0.40/0.61      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.40/0.61         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.40/0.61          | (v1_partfun1 @ X16 @ X17)
% 0.40/0.61          | ~ (v1_funct_2 @ X16 @ X17 @ X18)
% 0.40/0.61          | ~ (v1_funct_1 @ X16)
% 0.40/0.61          | (v1_xboole_0 @ X18))),
% 0.40/0.61      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.40/0.61  thf('33', plain,
% 0.40/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.40/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.61        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.40/0.61        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['31', '32'])).
% 0.40/0.61  thf('34', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('35', plain,
% 0.40/0.61      (![X28 : $i]:
% 0.40/0.61         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 0.40/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.61  thf('36', plain,
% 0.40/0.61      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('37', plain,
% 0.40/0.61      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.40/0.61        | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.61      inference('sup+', [status(thm)], ['35', '36'])).
% 0.40/0.61  thf('38', plain, ((l1_struct_0 @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('39', plain,
% 0.40/0.61      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.61      inference('demod', [status(thm)], ['37', '38'])).
% 0.40/0.61  thf('40', plain,
% 0.40/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.40/0.61        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.40/0.61      inference('demod', [status(thm)], ['33', '34', '39'])).
% 0.40/0.61  thf('41', plain,
% 0.40/0.61      (![X19 : $i, X20 : $i]:
% 0.40/0.61         (~ (v1_partfun1 @ X20 @ X19)
% 0.40/0.61          | ((k1_relat_1 @ X20) = (X19))
% 0.40/0.61          | ~ (v4_relat_1 @ X20 @ X19)
% 0.40/0.61          | ~ (v1_relat_1 @ X20))),
% 0.40/0.61      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.40/0.61  thf('42', plain,
% 0.40/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.40/0.61        | ~ (v1_relat_1 @ sk_C)
% 0.40/0.61        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.40/0.61        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['40', '41'])).
% 0.40/0.61  thf('43', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.61      inference('demod', [status(thm)], ['20', '21'])).
% 0.40/0.61  thf('44', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_C @ 
% 0.40/0.61        (k1_zfmisc_1 @ 
% 0.40/0.61         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.61      inference('demod', [status(thm)], ['29', '30'])).
% 0.40/0.61  thf('45', plain,
% 0.40/0.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.40/0.61         ((v4_relat_1 @ X10 @ X11)
% 0.40/0.61          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.40/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.40/0.61  thf('46', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.40/0.61      inference('sup-', [status(thm)], ['44', '45'])).
% 0.40/0.61  thf('47', plain,
% 0.40/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.40/0.61        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.40/0.61      inference('demod', [status(thm)], ['42', '43', '46'])).
% 0.40/0.61  thf(fc2_struct_0, axiom,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.40/0.61       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.40/0.61  thf('48', plain,
% 0.40/0.61      (![X29 : $i]:
% 0.40/0.61         (~ (v1_xboole_0 @ (u1_struct_0 @ X29))
% 0.40/0.61          | ~ (l1_struct_0 @ X29)
% 0.40/0.61          | (v2_struct_0 @ X29))),
% 0.40/0.61      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.40/0.61  thf('49', plain,
% 0.40/0.61      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 0.40/0.61        | (v2_struct_0 @ sk_B)
% 0.40/0.61        | ~ (l1_struct_0 @ sk_B))),
% 0.40/0.61      inference('sup-', [status(thm)], ['47', '48'])).
% 0.40/0.61  thf('50', plain, ((l1_struct_0 @ sk_B)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('51', plain,
% 0.40/0.61      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.40/0.61      inference('demod', [status(thm)], ['49', '50'])).
% 0.40/0.61  thf('52', plain, (~ (v2_struct_0 @ sk_B)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('53', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.40/0.61      inference('clc', [status(thm)], ['51', '52'])).
% 0.40/0.61  thf('54', plain,
% 0.40/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.40/0.61        | ((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))),
% 0.40/0.61      inference('demod', [status(thm)], ['26', '53'])).
% 0.40/0.61  thf('55', plain,
% 0.40/0.61      (![X29 : $i]:
% 0.40/0.61         (~ (v1_xboole_0 @ (u1_struct_0 @ X29))
% 0.40/0.61          | ~ (l1_struct_0 @ X29)
% 0.40/0.61          | (v2_struct_0 @ X29))),
% 0.40/0.61      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.40/0.61  thf('56', plain,
% 0.40/0.61      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))
% 0.40/0.61        | (v2_struct_0 @ sk_B)
% 0.40/0.61        | ~ (l1_struct_0 @ sk_B))),
% 0.40/0.61      inference('sup-', [status(thm)], ['54', '55'])).
% 0.40/0.61  thf('57', plain, ((l1_struct_0 @ sk_B)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('58', plain,
% 0.40/0.61      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.40/0.61      inference('demod', [status(thm)], ['56', '57'])).
% 0.40/0.61  thf('59', plain, (~ (v2_struct_0 @ sk_B)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('60', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.40/0.61      inference('clc', [status(thm)], ['58', '59'])).
% 0.40/0.61  thf('61', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.40/0.61      inference('clc', [status(thm)], ['58', '59'])).
% 0.40/0.61  thf('62', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.40/0.61      inference('clc', [status(thm)], ['58', '59'])).
% 0.40/0.61  thf('63', plain,
% 0.40/0.61      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.61          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.40/0.61           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.40/0.61          sk_C)),
% 0.40/0.61      inference('demod', [status(thm)], ['9', '60', '61', '62'])).
% 0.40/0.61  thf('64', plain,
% 0.40/0.61      (![X28 : $i]:
% 0.40/0.61         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 0.40/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.61  thf('65', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_C @ 
% 0.40/0.61        (k1_zfmisc_1 @ 
% 0.40/0.61         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.61      inference('demod', [status(thm)], ['29', '30'])).
% 0.40/0.61  thf('66', plain,
% 0.40/0.61      (((m1_subset_1 @ sk_C @ 
% 0.40/0.61         (k1_zfmisc_1 @ 
% 0.40/0.61          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.40/0.61        | ~ (l1_struct_0 @ sk_B))),
% 0.40/0.61      inference('sup+', [status(thm)], ['64', '65'])).
% 0.40/0.61  thf('67', plain, ((l1_struct_0 @ sk_B)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('68', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_C @ 
% 0.40/0.61        (k1_zfmisc_1 @ 
% 0.40/0.61         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.40/0.61      inference('demod', [status(thm)], ['66', '67'])).
% 0.40/0.61  thf(d4_tops_2, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.40/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.61       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.40/0.61         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.40/0.61  thf('69', plain,
% 0.40/0.61      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.40/0.61         (((k2_relset_1 @ X31 @ X30 @ X32) != (X30))
% 0.40/0.61          | ~ (v2_funct_1 @ X32)
% 0.40/0.61          | ((k2_tops_2 @ X31 @ X30 @ X32) = (k2_funct_1 @ X32))
% 0.40/0.61          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 0.40/0.61          | ~ (v1_funct_2 @ X32 @ X31 @ X30)
% 0.40/0.61          | ~ (v1_funct_1 @ X32))),
% 0.40/0.61      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.40/0.61  thf('70', plain,
% 0.40/0.61      ((~ (v1_funct_1 @ sk_C)
% 0.40/0.61        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.40/0.61        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.40/0.61            = (k2_funct_1 @ sk_C))
% 0.40/0.61        | ~ (v2_funct_1 @ sk_C)
% 0.40/0.61        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.40/0.61            != (k2_struct_0 @ sk_B)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['68', '69'])).
% 0.40/0.61  thf('71', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('72', plain,
% 0.40/0.61      (![X28 : $i]:
% 0.40/0.61         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 0.40/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.61  thf('73', plain,
% 0.40/0.61      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.61      inference('demod', [status(thm)], ['37', '38'])).
% 0.40/0.61  thf('74', plain,
% 0.40/0.61      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.40/0.61        | ~ (l1_struct_0 @ sk_B))),
% 0.40/0.61      inference('sup+', [status(thm)], ['72', '73'])).
% 0.40/0.61  thf('75', plain, ((l1_struct_0 @ sk_B)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('76', plain,
% 0.40/0.61      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.40/0.61      inference('demod', [status(thm)], ['74', '75'])).
% 0.40/0.61  thf('77', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('78', plain,
% 0.40/0.61      (![X28 : $i]:
% 0.40/0.61         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 0.40/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.61  thf('79', plain,
% 0.40/0.61      (![X28 : $i]:
% 0.40/0.61         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 0.40/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.40/0.61  thf('80', plain,
% 0.40/0.61      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.61         = (k2_struct_0 @ sk_B))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('81', plain,
% 0.40/0.61      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.61          = (k2_struct_0 @ sk_B))
% 0.40/0.61        | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.61      inference('sup+', [status(thm)], ['79', '80'])).
% 0.40/0.61  thf('82', plain, ((l1_struct_0 @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('83', plain,
% 0.40/0.61      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.61         = (k2_struct_0 @ sk_B))),
% 0.40/0.61      inference('demod', [status(thm)], ['81', '82'])).
% 0.40/0.61  thf('84', plain,
% 0.40/0.61      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.40/0.61          = (k2_struct_0 @ sk_B))
% 0.40/0.61        | ~ (l1_struct_0 @ sk_B))),
% 0.40/0.61      inference('sup+', [status(thm)], ['78', '83'])).
% 0.40/0.61  thf('85', plain, ((l1_struct_0 @ sk_B)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('86', plain,
% 0.40/0.61      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.40/0.61         = (k2_struct_0 @ sk_B))),
% 0.40/0.61      inference('demod', [status(thm)], ['84', '85'])).
% 0.40/0.61  thf('87', plain,
% 0.40/0.61      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.40/0.61          = (k2_funct_1 @ sk_C))
% 0.40/0.61        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.40/0.61      inference('demod', [status(thm)], ['70', '71', '76', '77', '86'])).
% 0.40/0.61  thf('88', plain,
% 0.40/0.61      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.40/0.61         = (k2_funct_1 @ sk_C))),
% 0.40/0.61      inference('simplify', [status(thm)], ['87'])).
% 0.40/0.61  thf('89', plain,
% 0.40/0.61      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.61          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.40/0.61           (k2_funct_1 @ sk_C)) @ 
% 0.40/0.61          sk_C)),
% 0.40/0.61      inference('demod', [status(thm)], ['63', '88'])).
% 0.40/0.61  thf(t55_funct_1, axiom,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.40/0.61       ( ( v2_funct_1 @ A ) =>
% 0.40/0.61         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.40/0.61           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.40/0.61  thf('90', plain,
% 0.40/0.61      (![X7 : $i]:
% 0.40/0.61         (~ (v2_funct_1 @ X7)
% 0.40/0.61          | ((k1_relat_1 @ X7) = (k2_relat_1 @ (k2_funct_1 @ X7)))
% 0.40/0.61          | ~ (v1_funct_1 @ X7)
% 0.40/0.61          | ~ (v1_relat_1 @ X7))),
% 0.40/0.61      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.40/0.61  thf('91', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_C @ 
% 0.40/0.61        (k1_zfmisc_1 @ 
% 0.40/0.61         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.40/0.61      inference('demod', [status(thm)], ['66', '67'])).
% 0.40/0.61  thf(t31_funct_2, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.40/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.61       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.40/0.61         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.40/0.61           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.40/0.61           ( m1_subset_1 @
% 0.40/0.61             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.40/0.61  thf('92', plain,
% 0.40/0.61      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.40/0.61         (~ (v2_funct_1 @ X25)
% 0.40/0.61          | ((k2_relset_1 @ X27 @ X26 @ X25) != (X26))
% 0.40/0.61          | (m1_subset_1 @ (k2_funct_1 @ X25) @ 
% 0.40/0.61             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.40/0.61          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 0.40/0.61          | ~ (v1_funct_2 @ X25 @ X27 @ X26)
% 0.40/0.61          | ~ (v1_funct_1 @ X25))),
% 0.40/0.61      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.40/0.61  thf('93', plain,
% 0.40/0.61      ((~ (v1_funct_1 @ sk_C)
% 0.40/0.61        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.40/0.61        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.40/0.61           (k1_zfmisc_1 @ 
% 0.40/0.61            (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.40/0.61        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.40/0.61            != (k2_struct_0 @ sk_B))
% 0.40/0.61        | ~ (v2_funct_1 @ sk_C))),
% 0.40/0.61      inference('sup-', [status(thm)], ['91', '92'])).
% 0.40/0.61  thf('94', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('95', plain,
% 0.40/0.61      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.40/0.61      inference('demod', [status(thm)], ['74', '75'])).
% 0.40/0.61  thf('96', plain,
% 0.40/0.61      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.40/0.61         = (k2_struct_0 @ sk_B))),
% 0.40/0.61      inference('demod', [status(thm)], ['84', '85'])).
% 0.40/0.61  thf('97', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('98', plain,
% 0.40/0.61      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.40/0.61         (k1_zfmisc_1 @ 
% 0.40/0.61          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.40/0.61        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.40/0.61      inference('demod', [status(thm)], ['93', '94', '95', '96', '97'])).
% 0.40/0.61  thf('99', plain,
% 0.40/0.61      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.40/0.61        (k1_zfmisc_1 @ 
% 0.40/0.61         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.40/0.61      inference('simplify', [status(thm)], ['98'])).
% 0.40/0.61  thf('100', plain,
% 0.40/0.61      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.40/0.61         (((k2_relset_1 @ X31 @ X30 @ X32) != (X30))
% 0.40/0.61          | ~ (v2_funct_1 @ X32)
% 0.40/0.61          | ((k2_tops_2 @ X31 @ X30 @ X32) = (k2_funct_1 @ X32))
% 0.40/0.61          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 0.40/0.61          | ~ (v1_funct_2 @ X32 @ X31 @ X30)
% 0.40/0.61          | ~ (v1_funct_1 @ X32))),
% 0.40/0.61      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.40/0.61  thf('101', plain,
% 0.40/0.61      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.61        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.40/0.61             (k2_struct_0 @ sk_A))
% 0.40/0.61        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.40/0.61            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.40/0.61        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.61        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.40/0.61            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['99', '100'])).
% 0.40/0.61  thf('102', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_C @ 
% 0.40/0.61        (k1_zfmisc_1 @ 
% 0.40/0.61         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.40/0.61      inference('demod', [status(thm)], ['66', '67'])).
% 0.40/0.61  thf('103', plain,
% 0.40/0.61      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.40/0.61         (~ (v2_funct_1 @ X25)
% 0.40/0.61          | ((k2_relset_1 @ X27 @ X26 @ X25) != (X26))
% 0.40/0.61          | (v1_funct_1 @ (k2_funct_1 @ X25))
% 0.40/0.61          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 0.40/0.61          | ~ (v1_funct_2 @ X25 @ X27 @ X26)
% 0.40/0.61          | ~ (v1_funct_1 @ X25))),
% 0.40/0.61      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.40/0.61  thf('104', plain,
% 0.40/0.61      ((~ (v1_funct_1 @ sk_C)
% 0.40/0.61        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.40/0.61        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.61        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.40/0.61            != (k2_struct_0 @ sk_B))
% 0.40/0.61        | ~ (v2_funct_1 @ sk_C))),
% 0.40/0.61      inference('sup-', [status(thm)], ['102', '103'])).
% 0.40/0.61  thf('105', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('106', plain,
% 0.40/0.61      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.40/0.61      inference('demod', [status(thm)], ['74', '75'])).
% 0.40/0.61  thf('107', plain,
% 0.40/0.61      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.40/0.61         = (k2_struct_0 @ sk_B))),
% 0.40/0.61      inference('demod', [status(thm)], ['84', '85'])).
% 0.40/0.61  thf('108', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('109', plain,
% 0.40/0.61      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.61        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.40/0.61      inference('demod', [status(thm)], ['104', '105', '106', '107', '108'])).
% 0.40/0.61  thf('110', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.40/0.61      inference('simplify', [status(thm)], ['109'])).
% 0.40/0.61  thf('111', plain,
% 0.40/0.61      ((m1_subset_1 @ sk_C @ 
% 0.40/0.61        (k1_zfmisc_1 @ 
% 0.40/0.61         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.40/0.61      inference('demod', [status(thm)], ['66', '67'])).
% 0.40/0.61  thf('112', plain,
% 0.40/0.61      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.40/0.61         (~ (v2_funct_1 @ X25)
% 0.40/0.61          | ((k2_relset_1 @ X27 @ X26 @ X25) != (X26))
% 0.40/0.61          | (v1_funct_2 @ (k2_funct_1 @ X25) @ X26 @ X27)
% 0.40/0.61          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 0.40/0.61          | ~ (v1_funct_2 @ X25 @ X27 @ X26)
% 0.40/0.61          | ~ (v1_funct_1 @ X25))),
% 0.40/0.61      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.40/0.61  thf('113', plain,
% 0.40/0.61      ((~ (v1_funct_1 @ sk_C)
% 0.40/0.61        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.40/0.61        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.40/0.61           (k2_struct_0 @ sk_A))
% 0.40/0.61        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.40/0.61            != (k2_struct_0 @ sk_B))
% 0.40/0.61        | ~ (v2_funct_1 @ sk_C))),
% 0.40/0.61      inference('sup-', [status(thm)], ['111', '112'])).
% 0.40/0.61  thf('114', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('115', plain,
% 0.40/0.61      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.40/0.61      inference('demod', [status(thm)], ['74', '75'])).
% 0.40/0.61  thf('116', plain,
% 0.40/0.61      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.40/0.61         = (k2_struct_0 @ sk_B))),
% 0.40/0.61      inference('demod', [status(thm)], ['84', '85'])).
% 0.40/0.61  thf('117', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('118', plain,
% 0.40/0.61      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.40/0.61         (k2_struct_0 @ sk_A))
% 0.40/0.61        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.40/0.61      inference('demod', [status(thm)], ['113', '114', '115', '116', '117'])).
% 0.40/0.61  thf('119', plain,
% 0.40/0.61      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.40/0.61        (k2_struct_0 @ sk_A))),
% 0.40/0.61      inference('simplify', [status(thm)], ['118'])).
% 0.40/0.61  thf('120', plain,
% 0.40/0.61      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.40/0.61        (k1_zfmisc_1 @ 
% 0.40/0.61         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.40/0.61      inference('simplify', [status(thm)], ['98'])).
% 0.40/0.61  thf(redefinition_k2_relset_1, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.61       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.40/0.61  thf('121', plain,
% 0.40/0.61      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.40/0.61         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 0.40/0.61          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.40/0.61      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.40/0.61  thf('122', plain,
% 0.40/0.61      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.40/0.61         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['120', '121'])).
% 0.40/0.61  thf('123', plain,
% 0.40/0.61      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.40/0.61          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.40/0.61        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.61        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.40/0.61      inference('demod', [status(thm)], ['101', '110', '119', '122'])).
% 0.40/0.61  thf('124', plain,
% 0.40/0.61      (![X9 : $i]:
% 0.40/0.61         (~ (v2_funct_1 @ X9)
% 0.40/0.61          | ((k2_funct_1 @ (k2_funct_1 @ X9)) = (X9))
% 0.40/0.61          | ~ (v1_funct_1 @ X9)
% 0.40/0.61          | ~ (v1_relat_1 @ X9))),
% 0.40/0.61      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.40/0.61  thf(t61_funct_1, axiom,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.40/0.61       ( ( v2_funct_1 @ A ) =>
% 0.40/0.61         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.40/0.61             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.40/0.61           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.40/0.61             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.40/0.61  thf('125', plain,
% 0.40/0.61      (![X8 : $i]:
% 0.40/0.61         (~ (v2_funct_1 @ X8)
% 0.40/0.61          | ((k5_relat_1 @ (k2_funct_1 @ X8) @ X8)
% 0.40/0.61              = (k6_relat_1 @ (k2_relat_1 @ X8)))
% 0.40/0.61          | ~ (v1_funct_1 @ X8)
% 0.40/0.61          | ~ (v1_relat_1 @ X8))),
% 0.40/0.61      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.40/0.61  thf(dt_k2_funct_1, axiom,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.40/0.61       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.40/0.61         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.40/0.61  thf('126', plain,
% 0.40/0.62      (![X4 : $i]:
% 0.40/0.62         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.40/0.62          | ~ (v1_funct_1 @ X4)
% 0.40/0.62          | ~ (v1_relat_1 @ X4))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.40/0.62  thf('127', plain,
% 0.40/0.62      (![X4 : $i]:
% 0.40/0.62         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.40/0.62          | ~ (v1_funct_1 @ X4)
% 0.40/0.62          | ~ (v1_relat_1 @ X4))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.40/0.62  thf('128', plain,
% 0.40/0.62      (![X7 : $i]:
% 0.40/0.62         (~ (v2_funct_1 @ X7)
% 0.40/0.62          | ((k2_relat_1 @ X7) = (k1_relat_1 @ (k2_funct_1 @ X7)))
% 0.40/0.62          | ~ (v1_funct_1 @ X7)
% 0.40/0.62          | ~ (v1_relat_1 @ X7))),
% 0.40/0.62      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.40/0.62  thf(t53_funct_1, axiom,
% 0.40/0.62    (![A:$i]:
% 0.40/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.40/0.62       ( ( ?[B:$i]:
% 0.40/0.62           ( ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.40/0.62             ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) ) =>
% 0.40/0.62         ( v2_funct_1 @ A ) ) ))).
% 0.40/0.62  thf('129', plain,
% 0.40/0.62      (![X5 : $i, X6 : $i]:
% 0.40/0.62         (~ (v1_relat_1 @ X5)
% 0.40/0.62          | ~ (v1_funct_1 @ X5)
% 0.40/0.62          | ((k5_relat_1 @ X6 @ X5) != (k6_relat_1 @ (k1_relat_1 @ X6)))
% 0.40/0.62          | (v2_funct_1 @ X6)
% 0.40/0.62          | ~ (v1_funct_1 @ X6)
% 0.40/0.62          | ~ (v1_relat_1 @ X6))),
% 0.40/0.62      inference('cnf', [status(esa)], [t53_funct_1])).
% 0.40/0.62  thf('130', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X1)
% 0.40/0.62            != (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.40/0.62          | ~ (v1_relat_1 @ X0)
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v2_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.40/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.40/0.62          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.40/0.62          | ~ (v1_funct_1 @ X1)
% 0.40/0.62          | ~ (v1_relat_1 @ X1))),
% 0.40/0.62      inference('sup-', [status(thm)], ['128', '129'])).
% 0.40/0.62  thf('131', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         (~ (v1_relat_1 @ X0)
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ X1)
% 0.40/0.62          | ~ (v1_funct_1 @ X1)
% 0.40/0.62          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.40/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.40/0.62          | ~ (v2_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ X0)
% 0.40/0.62          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X1)
% 0.40/0.62              != (k6_relat_1 @ (k2_relat_1 @ X0))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['127', '130'])).
% 0.40/0.62  thf('132', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X1)
% 0.40/0.62            != (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.40/0.62          | ~ (v2_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.40/0.62          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.40/0.62          | ~ (v1_funct_1 @ X1)
% 0.40/0.62          | ~ (v1_relat_1 @ X1)
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ X0))),
% 0.40/0.62      inference('simplify', [status(thm)], ['131'])).
% 0.40/0.62  thf('133', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         (~ (v1_relat_1 @ X0)
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ X0)
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ X1)
% 0.40/0.62          | ~ (v1_funct_1 @ X1)
% 0.40/0.62          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.40/0.62          | ~ (v2_funct_1 @ X0)
% 0.40/0.62          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X1)
% 0.40/0.62              != (k6_relat_1 @ (k2_relat_1 @ X0))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['126', '132'])).
% 0.40/0.62  thf('134', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X1)
% 0.40/0.62            != (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.40/0.62          | ~ (v2_funct_1 @ X0)
% 0.40/0.62          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.40/0.62          | ~ (v1_funct_1 @ X1)
% 0.40/0.62          | ~ (v1_relat_1 @ X1)
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ X0))),
% 0.40/0.62      inference('simplify', [status(thm)], ['133'])).
% 0.40/0.62  thf('135', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (((k6_relat_1 @ (k2_relat_1 @ X0)) != (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.40/0.62          | ~ (v1_relat_1 @ X0)
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v2_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ X0)
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ X0)
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.40/0.62          | ~ (v2_funct_1 @ X0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['125', '134'])).
% 0.40/0.62  thf('136', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.40/0.62          | ~ (v2_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ X0))),
% 0.40/0.62      inference('simplify', [status(thm)], ['135'])).
% 0.40/0.62  thf('137', plain,
% 0.40/0.62      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.40/0.62        (k1_zfmisc_1 @ 
% 0.40/0.62         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.40/0.62      inference('simplify', [status(thm)], ['98'])).
% 0.40/0.62  thf('138', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.40/0.62          | (v1_relat_1 @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ X1))),
% 0.40/0.62      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.40/0.62  thf('139', plain,
% 0.40/0.62      ((~ (v1_relat_1 @ 
% 0.40/0.62           (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))
% 0.40/0.62        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['137', '138'])).
% 0.40/0.62  thf('140', plain,
% 0.40/0.62      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.40/0.62      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.40/0.62  thf('141', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.40/0.62      inference('demod', [status(thm)], ['139', '140'])).
% 0.40/0.62  thf('142', plain,
% 0.40/0.62      (![X9 : $i]:
% 0.40/0.62         (~ (v2_funct_1 @ X9)
% 0.40/0.62          | ((k2_funct_1 @ (k2_funct_1 @ X9)) = (X9))
% 0.40/0.62          | ~ (v1_funct_1 @ X9)
% 0.40/0.62          | ~ (v1_relat_1 @ X9))),
% 0.40/0.62      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.40/0.62  thf('143', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.40/0.62          | ~ (v2_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ X0))),
% 0.40/0.62      inference('simplify', [status(thm)], ['135'])).
% 0.40/0.62  thf('144', plain,
% 0.40/0.62      (![X4 : $i]:
% 0.40/0.62         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.40/0.62          | ~ (v1_funct_1 @ X4)
% 0.40/0.62          | ~ (v1_relat_1 @ X4))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.40/0.62  thf('145', plain,
% 0.40/0.62      (![X4 : $i]:
% 0.40/0.62         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.40/0.62          | ~ (v1_funct_1 @ X4)
% 0.40/0.62          | ~ (v1_relat_1 @ X4))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.40/0.62  thf('146', plain,
% 0.40/0.62      (![X9 : $i]:
% 0.40/0.62         (~ (v2_funct_1 @ X9)
% 0.40/0.62          | ((k2_funct_1 @ (k2_funct_1 @ X9)) = (X9))
% 0.40/0.62          | ~ (v1_funct_1 @ X9)
% 0.40/0.62          | ~ (v1_relat_1 @ X9))),
% 0.40/0.62      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.40/0.62  thf('147', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.40/0.62          | ~ (v2_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ X0))),
% 0.40/0.62      inference('simplify', [status(thm)], ['135'])).
% 0.40/0.62  thf('148', plain,
% 0.40/0.62      (![X4 : $i]:
% 0.40/0.62         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.40/0.62          | ~ (v1_funct_1 @ X4)
% 0.40/0.62          | ~ (v1_relat_1 @ X4))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.40/0.62  thf('149', plain,
% 0.40/0.62      (![X4 : $i]:
% 0.40/0.62         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.40/0.62          | ~ (v1_funct_1 @ X4)
% 0.40/0.62          | ~ (v1_relat_1 @ X4))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.40/0.62  thf('150', plain,
% 0.40/0.62      (![X9 : $i]:
% 0.40/0.62         (~ (v2_funct_1 @ X9)
% 0.40/0.62          | ((k2_funct_1 @ (k2_funct_1 @ X9)) = (X9))
% 0.40/0.62          | ~ (v1_funct_1 @ X9)
% 0.40/0.62          | ~ (v1_relat_1 @ X9))),
% 0.40/0.62      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.40/0.62  thf('151', plain,
% 0.40/0.62      (![X8 : $i]:
% 0.40/0.62         (~ (v2_funct_1 @ X8)
% 0.40/0.62          | ((k5_relat_1 @ X8 @ (k2_funct_1 @ X8))
% 0.40/0.62              = (k6_relat_1 @ (k1_relat_1 @ X8)))
% 0.40/0.62          | ~ (v1_funct_1 @ X8)
% 0.40/0.62          | ~ (v1_relat_1 @ X8))),
% 0.40/0.62      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.40/0.62  thf('152', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.40/0.62            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.40/0.62          | ~ (v1_relat_1 @ X0)
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v2_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.40/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.40/0.62          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.40/0.62      inference('sup+', [status(thm)], ['150', '151'])).
% 0.40/0.62  thf('153', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (v1_relat_1 @ X0)
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.40/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.40/0.62          | ~ (v2_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ X0)
% 0.40/0.62          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.40/0.62              = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['149', '152'])).
% 0.40/0.62  thf('154', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.40/0.62            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.40/0.62          | ~ (v2_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.40/0.62          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ X0))),
% 0.40/0.62      inference('simplify', [status(thm)], ['153'])).
% 0.40/0.62  thf('155', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (v1_relat_1 @ X0)
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ X0)
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.40/0.62          | ~ (v2_funct_1 @ X0)
% 0.40/0.62          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.40/0.62              = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['148', '154'])).
% 0.40/0.62  thf('156', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.40/0.62            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.40/0.62          | ~ (v2_funct_1 @ X0)
% 0.40/0.62          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ X0))),
% 0.40/0.62      inference('simplify', [status(thm)], ['155'])).
% 0.40/0.62  thf('157', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (v1_relat_1 @ X0)
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v2_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ X0)
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v2_funct_1 @ X0)
% 0.40/0.62          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.40/0.62              = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['147', '156'])).
% 0.40/0.62  thf('158', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.40/0.62            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.40/0.62          | ~ (v2_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ X0))),
% 0.40/0.62      inference('simplify', [status(thm)], ['157'])).
% 0.40/0.62  thf('159', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.40/0.62            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 0.40/0.62          | ~ (v1_relat_1 @ X0)
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v2_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.40/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.40/0.62          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.40/0.62      inference('sup+', [status(thm)], ['146', '158'])).
% 0.40/0.62  thf('160', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (v1_relat_1 @ X0)
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.40/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.40/0.62          | ~ (v2_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ X0)
% 0.40/0.62          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.40/0.62              = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['145', '159'])).
% 0.40/0.62  thf('161', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.40/0.62            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 0.40/0.62          | ~ (v2_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.40/0.62          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ X0))),
% 0.40/0.62      inference('simplify', [status(thm)], ['160'])).
% 0.40/0.62  thf('162', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (v1_relat_1 @ X0)
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ X0)
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.40/0.62          | ~ (v2_funct_1 @ X0)
% 0.40/0.62          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.40/0.62              = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['144', '161'])).
% 0.40/0.62  thf('163', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.40/0.62            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 0.40/0.62          | ~ (v2_funct_1 @ X0)
% 0.40/0.62          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ X0))),
% 0.40/0.62      inference('simplify', [status(thm)], ['162'])).
% 0.40/0.62  thf('164', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (v1_relat_1 @ X0)
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v2_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ X0)
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v2_funct_1 @ X0)
% 0.40/0.62          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.40/0.62              = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['143', '163'])).
% 0.40/0.62  thf('165', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.40/0.62            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 0.40/0.62          | ~ (v2_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ X0))),
% 0.40/0.62      inference('simplify', [status(thm)], ['164'])).
% 0.40/0.62  thf('166', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.40/0.62            = (k6_relat_1 @ 
% 0.40/0.62               (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))
% 0.40/0.62          | ~ (v1_relat_1 @ X0)
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v2_funct_1 @ X0)
% 0.40/0.62          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.40/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.40/0.62          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.40/0.62      inference('sup+', [status(thm)], ['142', '165'])).
% 0.40/0.62  thf('167', plain,
% 0.40/0.62      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.62        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.40/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.40/0.62        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.40/0.62            = (k6_relat_1 @ 
% 0.40/0.62               (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['141', '166'])).
% 0.40/0.62  thf('168', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.40/0.62      inference('simplify', [status(thm)], ['109'])).
% 0.40/0.62  thf('169', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('170', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('171', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.62      inference('demod', [status(thm)], ['20', '21'])).
% 0.40/0.62  thf('172', plain,
% 0.40/0.62      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.62        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.40/0.62            = (k6_relat_1 @ 
% 0.40/0.62               (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))))),
% 0.40/0.62      inference('demod', [status(thm)], ['167', '168', '169', '170', '171'])).
% 0.40/0.62  thf('173', plain,
% 0.40/0.62      ((~ (v1_relat_1 @ sk_C)
% 0.40/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.40/0.62        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.40/0.62            = (k6_relat_1 @ 
% 0.40/0.62               (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['136', '172'])).
% 0.40/0.62  thf('174', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.62      inference('demod', [status(thm)], ['20', '21'])).
% 0.40/0.62  thf('175', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('176', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('177', plain,
% 0.40/0.62      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.40/0.62         = (k6_relat_1 @ 
% 0.40/0.62            (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))))),
% 0.40/0.62      inference('demod', [status(thm)], ['173', '174', '175', '176'])).
% 0.40/0.62  thf('178', plain,
% 0.40/0.62      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.40/0.62          = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 0.40/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.40/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.40/0.62      inference('sup+', [status(thm)], ['124', '177'])).
% 0.40/0.62  thf('179', plain,
% 0.40/0.62      (![X7 : $i]:
% 0.40/0.62         (~ (v2_funct_1 @ X7)
% 0.40/0.62          | ((k2_relat_1 @ X7) = (k1_relat_1 @ (k2_funct_1 @ X7)))
% 0.40/0.62          | ~ (v1_funct_1 @ X7)
% 0.40/0.62          | ~ (v1_relat_1 @ X7))),
% 0.40/0.62      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.40/0.62  thf('180', plain,
% 0.40/0.62      ((m1_subset_1 @ sk_C @ 
% 0.40/0.62        (k1_zfmisc_1 @ 
% 0.40/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('181', plain,
% 0.40/0.62      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.40/0.62         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 0.40/0.62          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.40/0.62      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.40/0.62  thf('182', plain,
% 0.40/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.62         = (k2_relat_1 @ sk_C))),
% 0.40/0.62      inference('sup-', [status(thm)], ['180', '181'])).
% 0.40/0.62  thf('183', plain,
% 0.40/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.40/0.62         = (k2_struct_0 @ sk_B))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('184', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.40/0.62      inference('sup+', [status(thm)], ['182', '183'])).
% 0.40/0.62  thf('185', plain,
% 0.40/0.62      (![X7 : $i]:
% 0.40/0.62         (~ (v2_funct_1 @ X7)
% 0.40/0.62          | ((k2_relat_1 @ X7) = (k1_relat_1 @ (k2_funct_1 @ X7)))
% 0.40/0.62          | ~ (v1_funct_1 @ X7)
% 0.40/0.62          | ~ (v1_relat_1 @ X7))),
% 0.40/0.62      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.40/0.62  thf('186', plain,
% 0.40/0.62      (![X19 : $i, X20 : $i]:
% 0.40/0.62         (((k1_relat_1 @ X20) != (X19))
% 0.40/0.62          | (v1_partfun1 @ X20 @ X19)
% 0.40/0.62          | ~ (v4_relat_1 @ X20 @ X19)
% 0.40/0.62          | ~ (v1_relat_1 @ X20))),
% 0.40/0.62      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.40/0.62  thf('187', plain,
% 0.40/0.62      (![X20 : $i]:
% 0.40/0.62         (~ (v1_relat_1 @ X20)
% 0.40/0.62          | ~ (v4_relat_1 @ X20 @ (k1_relat_1 @ X20))
% 0.40/0.62          | (v1_partfun1 @ X20 @ (k1_relat_1 @ X20)))),
% 0.40/0.62      inference('simplify', [status(thm)], ['186'])).
% 0.40/0.62  thf('188', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.40/0.62          | ~ (v1_relat_1 @ X0)
% 0.40/0.62          | ~ (v1_funct_1 @ X0)
% 0.40/0.62          | ~ (v2_funct_1 @ X0)
% 0.40/0.62          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.40/0.62          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['185', '187'])).
% 0.40/0.62  thf('189', plain,
% 0.40/0.62      ((~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 0.40/0.62        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.62        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ 
% 0.40/0.62           (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.40/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.40/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.62        | ~ (v1_relat_1 @ sk_C))),
% 0.40/0.62      inference('sup-', [status(thm)], ['184', '188'])).
% 0.40/0.62  thf('190', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('191', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('192', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.62      inference('demod', [status(thm)], ['20', '21'])).
% 0.40/0.62  thf('193', plain,
% 0.40/0.62      ((~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 0.40/0.62        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.62        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ 
% 0.40/0.62           (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.40/0.62      inference('demod', [status(thm)], ['189', '190', '191', '192'])).
% 0.40/0.62  thf('194', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.40/0.62      inference('demod', [status(thm)], ['139', '140'])).
% 0.40/0.62  thf('195', plain,
% 0.40/0.62      ((~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 0.40/0.62        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ 
% 0.40/0.62           (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.40/0.62      inference('demod', [status(thm)], ['193', '194'])).
% 0.40/0.62  thf('196', plain,
% 0.40/0.62      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.40/0.62        (k1_zfmisc_1 @ 
% 0.40/0.62         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.40/0.62      inference('simplify', [status(thm)], ['98'])).
% 0.40/0.62  thf('197', plain,
% 0.40/0.62      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.40/0.62         ((v4_relat_1 @ X10 @ X11)
% 0.40/0.62          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.40/0.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.40/0.62  thf('198', plain,
% 0.40/0.62      ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))),
% 0.40/0.62      inference('sup-', [status(thm)], ['196', '197'])).
% 0.40/0.62  thf('199', plain,
% 0.40/0.62      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.40/0.62      inference('demod', [status(thm)], ['195', '198'])).
% 0.40/0.62  thf('200', plain,
% 0.40/0.62      (((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.40/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.40/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.40/0.62      inference('sup+', [status(thm)], ['179', '199'])).
% 0.40/0.62  thf('201', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.40/0.62      inference('sup+', [status(thm)], ['182', '183'])).
% 0.40/0.62  thf('202', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.62      inference('demod', [status(thm)], ['20', '21'])).
% 0.40/0.62  thf('203', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('204', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('205', plain,
% 0.40/0.62      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))),
% 0.40/0.62      inference('demod', [status(thm)], ['200', '201', '202', '203', '204'])).
% 0.40/0.62  thf('206', plain,
% 0.40/0.62      (![X19 : $i, X20 : $i]:
% 0.40/0.62         (~ (v1_partfun1 @ X20 @ X19)
% 0.40/0.62          | ((k1_relat_1 @ X20) = (X19))
% 0.40/0.62          | ~ (v4_relat_1 @ X20 @ X19)
% 0.40/0.62          | ~ (v1_relat_1 @ X20))),
% 0.40/0.62      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.40/0.62  thf('207', plain,
% 0.40/0.62      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.62        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 0.40/0.62        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['205', '206'])).
% 0.40/0.62  thf('208', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.40/0.62      inference('demod', [status(thm)], ['139', '140'])).
% 0.40/0.62  thf('209', plain,
% 0.40/0.62      ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))),
% 0.40/0.62      inference('sup-', [status(thm)], ['196', '197'])).
% 0.40/0.62  thf('210', plain,
% 0.40/0.62      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B))),
% 0.40/0.62      inference('demod', [status(thm)], ['207', '208', '209'])).
% 0.40/0.62  thf('211', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.62      inference('demod', [status(thm)], ['20', '21'])).
% 0.40/0.62  thf('212', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('213', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('214', plain,
% 0.40/0.62      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.40/0.62         = (k6_relat_1 @ (k2_struct_0 @ sk_B)))),
% 0.40/0.62      inference('demod', [status(thm)], ['178', '210', '211', '212', '213'])).
% 0.40/0.62  thf('215', plain,
% 0.40/0.62      (![X5 : $i, X6 : $i]:
% 0.40/0.62         (~ (v1_relat_1 @ X5)
% 0.40/0.62          | ~ (v1_funct_1 @ X5)
% 0.40/0.62          | ((k5_relat_1 @ X6 @ X5) != (k6_relat_1 @ (k1_relat_1 @ X6)))
% 0.40/0.62          | (v2_funct_1 @ X6)
% 0.40/0.62          | ~ (v1_funct_1 @ X6)
% 0.40/0.62          | ~ (v1_relat_1 @ X6))),
% 0.40/0.62      inference('cnf', [status(esa)], [t53_funct_1])).
% 0.40/0.62  thf('216', plain,
% 0.40/0.62      ((((k6_relat_1 @ (k2_struct_0 @ sk_B))
% 0.40/0.62          != (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 0.40/0.62        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.62        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.62        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.40/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.62        | ~ (v1_relat_1 @ sk_C))),
% 0.40/0.62      inference('sup-', [status(thm)], ['214', '215'])).
% 0.40/0.62  thf('217', plain,
% 0.40/0.62      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B))),
% 0.40/0.62      inference('demod', [status(thm)], ['207', '208', '209'])).
% 0.40/0.62  thf('218', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.40/0.62      inference('demod', [status(thm)], ['139', '140'])).
% 0.40/0.62  thf('219', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.40/0.62      inference('simplify', [status(thm)], ['109'])).
% 0.40/0.62  thf('220', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('221', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.62      inference('demod', [status(thm)], ['20', '21'])).
% 0.40/0.62  thf('222', plain,
% 0.40/0.62      ((((k6_relat_1 @ (k2_struct_0 @ sk_B))
% 0.40/0.62          != (k6_relat_1 @ (k2_struct_0 @ sk_B)))
% 0.40/0.62        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.40/0.62      inference('demod', [status(thm)],
% 0.40/0.62                ['216', '217', '218', '219', '220', '221'])).
% 0.40/0.62  thf('223', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.40/0.62      inference('simplify', [status(thm)], ['222'])).
% 0.40/0.62  thf('224', plain,
% 0.40/0.62      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.40/0.62          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.40/0.62        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.40/0.62      inference('demod', [status(thm)], ['123', '223'])).
% 0.40/0.62  thf('225', plain,
% 0.40/0.62      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 0.40/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.40/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.40/0.62        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.40/0.62            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.40/0.62      inference('sup-', [status(thm)], ['90', '224'])).
% 0.40/0.62  thf('226', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.40/0.62      inference('clc', [status(thm)], ['51', '52'])).
% 0.40/0.62  thf('227', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.62      inference('demod', [status(thm)], ['20', '21'])).
% 0.40/0.62  thf('228', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('229', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('230', plain,
% 0.40/0.62      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.40/0.62        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.40/0.62            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.40/0.62      inference('demod', [status(thm)], ['225', '226', '227', '228', '229'])).
% 0.40/0.62  thf('231', plain,
% 0.40/0.62      (((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.40/0.62         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.40/0.62      inference('simplify', [status(thm)], ['230'])).
% 0.40/0.62  thf('232', plain,
% 0.40/0.62      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.62          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 0.40/0.62      inference('demod', [status(thm)], ['89', '231'])).
% 0.40/0.62  thf('233', plain,
% 0.40/0.62      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.40/0.62           sk_C)
% 0.40/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.40/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.40/0.62      inference('sup-', [status(thm)], ['0', '232'])).
% 0.40/0.62  thf('234', plain,
% 0.40/0.62      ((m1_subset_1 @ sk_C @ 
% 0.40/0.62        (k1_zfmisc_1 @ 
% 0.40/0.62         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.62      inference('demod', [status(thm)], ['29', '30'])).
% 0.40/0.62  thf(redefinition_r2_funct_2, axiom,
% 0.40/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.40/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.40/0.62         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.40/0.62         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.62       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.40/0.62  thf('235', plain,
% 0.40/0.62      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.40/0.62         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.40/0.62          | ~ (v1_funct_2 @ X21 @ X22 @ X23)
% 0.40/0.62          | ~ (v1_funct_1 @ X21)
% 0.40/0.62          | ~ (v1_funct_1 @ X24)
% 0.40/0.62          | ~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.40/0.62          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.40/0.62          | (r2_funct_2 @ X22 @ X23 @ X21 @ X24)
% 0.40/0.62          | ((X21) != (X24)))),
% 0.40/0.62      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.40/0.62  thf('236', plain,
% 0.40/0.62      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.40/0.62         ((r2_funct_2 @ X22 @ X23 @ X24 @ X24)
% 0.40/0.62          | ~ (v1_funct_1 @ X24)
% 0.40/0.62          | ~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.40/0.62          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.40/0.62      inference('simplify', [status(thm)], ['235'])).
% 0.40/0.62  thf('237', plain,
% 0.40/0.62      ((~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.40/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.62        | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.40/0.62           sk_C))),
% 0.40/0.62      inference('sup-', [status(thm)], ['234', '236'])).
% 0.40/0.62  thf('238', plain,
% 0.40/0.62      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.62      inference('demod', [status(thm)], ['37', '38'])).
% 0.40/0.62  thf('239', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('240', plain,
% 0.40/0.62      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.40/0.62      inference('demod', [status(thm)], ['237', '238', '239'])).
% 0.40/0.62  thf('241', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.62      inference('demod', [status(thm)], ['20', '21'])).
% 0.40/0.62  thf('242', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('243', plain, ((v2_funct_1 @ sk_C)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('244', plain, ($false),
% 0.40/0.62      inference('demod', [status(thm)], ['233', '240', '241', '242', '243'])).
% 0.40/0.62  
% 0.40/0.62  % SZS output end Refutation
% 0.40/0.62  
% 0.40/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
