%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jBwEhuze19

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:18 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  266 (1902 expanded)
%              Number of leaves         :   45 ( 579 expanded)
%              Depth                    :   30
%              Number of atoms          : 2472 (40896 expanded)
%              Number of equality atoms :  105 (1156 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('0',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
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
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 ) ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 ) ) @ sk_C_1 )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 ) ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 ) ) @ sk_C_1 )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 ) ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( v1_partfun1 @ X17 @ X18 )
      | ~ ( v1_funct_2 @ X17 @ X18 @ X19 )
      | ~ ( v1_funct_1 @ X17 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('16',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_partfun1 @ X21 @ X20 )
      | ( ( k1_relat_1 @ X21 )
        = X20 )
      | ~ ( v4_relat_1 @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v4_relat_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('22',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('24',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v4_relat_1 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('25',plain,(
    v4_relat_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','22','25'])).

thf('27',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('28',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( v1_partfun1 @ X17 @ X18 )
      | ~ ( v1_funct_2 @ X17 @ X18 @ X19 )
      | ~ ( v1_funct_1 @ X17 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('36',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34','39'])).

thf('41',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_partfun1 @ X21 @ X20 )
      | ( ( k1_relat_1 @ X21 )
        = X20 )
      | ~ ( v4_relat_1 @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v4_relat_1 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('44',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('45',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v4_relat_1 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('46',plain,(
    v4_relat_1 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43','46'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('48',plain,(
    ! [X32: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('49',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','53'])).

thf('55',plain,(
    ! [X32: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
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
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 ) ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['9','60','61','62'])).

thf('64',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('65',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('66',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k2_relset_1 @ X34 @ X33 @ X35 )
       != X33 )
      | ~ ( v2_funct_1 @ X35 )
      | ( ( k2_tops_2 @ X34 @ X33 @ X35 )
        = ( k2_funct_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('70',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 )
      = ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('73',plain,(
    v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('74',plain,
    ( ( v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('79',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('80',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['78','83'])).

thf('85',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 )
      = ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['70','71','76','77','86'])).

thf('88',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 )
    = ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C_1 ) ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['63','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
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

thf('91',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_relset_1 @ X30 @ X29 @ X28 )
       != X29 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('92',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('95',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('96',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['92','93','94','95','96'])).

thf('98',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k2_relset_1 @ X34 @ X33 @ X35 )
       != X33 )
      | ~ ( v2_funct_1 @ X35 )
      | ( ( k2_tops_2 @ X34 @ X33 @ X35 )
        = ( k2_funct_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('100',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C_1 ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('102',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_relset_1 @ X30 @ X29 @ X28 )
       != X29 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('103',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('106',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('107',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['103','104','105','106','107'])).

thf('109',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('111',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_relset_1 @ X30 @ X29 @ X28 )
       != X29 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X28 ) @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('112',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('115',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('116',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['112','113','114','115','116'])).

thf('118',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['117'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('119',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_relat_1 @ X8 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('120',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['108'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('121',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k5_relat_1 @ X9 @ ( k2_funct_1 @ X9 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(t48_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) ) )
           => ( ( v2_funct_1 @ B )
              & ( v2_funct_1 @ A ) ) ) ) ) )).

thf('122',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( v2_funct_1 @ X7 )
      | ( ( k2_relat_1 @ X6 )
       != ( k1_relat_1 @ X7 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X6 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('124',plain,(
    ! [X5: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k2_relat_1 @ sk_C_1 )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['120','126'])).

thf('128',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('129',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('132',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('133',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['127','128','129','130','135'])).

thf('137',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('139',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('141',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['136','141'])).

thf('143',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['119','142'])).

thf('144',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('145',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('146',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['143','144','145','146','147'])).

thf('149',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('151',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('152',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C_1 ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['100','109','118','149','152'])).

thf('154',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k1_relat_1 @ X8 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('155',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_relat_1 @ X8 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('156',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('157',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['148'])).

thf('158',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('159',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k1_relat_1 @ X8 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('160',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('161',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_relat_1 @ X8 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('162',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k1_relat_1 @ X21 )
       != X20 )
      | ( v1_partfun1 @ X21 @ X20 )
      | ~ ( v4_relat_1 @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('163',plain,(
    ! [X21: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v4_relat_1 @ X21 @ ( k1_relat_1 @ X21 ) )
      | ( v1_partfun1 @ X21 @ ( k1_relat_1 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['161','163'])).

thf('165',plain,(
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
    inference('sup-',[status(thm)],['160','164'])).

thf('166',plain,(
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
    inference('sup-',[status(thm)],['159','165'])).

thf('167',plain,(
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
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,(
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
    inference('sup-',[status(thm)],['158','167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( v4_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['157','169'])).

thf('171',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('172',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('175',plain,(
    v4_relat_1 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('176',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('177',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['108'])).

thf('178',plain,(
    v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['170','171','172','173','174','175','176','177'])).

thf('179',plain,
    ( ( v1_partfun1 @ sk_C_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['156','178'])).

thf('180',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('181',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    v1_partfun1 @ sk_C_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['179','180','181','182'])).

thf('184',plain,
    ( ( v1_partfun1 @ sk_C_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['155','183'])).

thf('185',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('186',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['108'])).

thf('187',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['148'])).

thf('188',plain,(
    v1_partfun1 @ sk_C_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['184','185','186','187'])).

thf('189',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_partfun1 @ X21 @ X20 )
      | ( ( k1_relat_1 @ X21 )
        = X20 )
      | ~ ( v4_relat_1 @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('190',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v4_relat_1 @ sk_C_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('192',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('193',plain,
    ( ~ ( v4_relat_1 @ sk_C_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['190','191','192'])).

thf('194',plain,
    ( ~ ( v4_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ( ( k2_struct_0 @ sk_A )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['154','193'])).

thf('195',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('196',plain,(
    v4_relat_1 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('197',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('198',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['194','195','196','197','198','199'])).

thf('201',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C_1 ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['153','200'])).

thf('202',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['201'])).

thf('203',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['89','202'])).

thf('204',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','203'])).

thf(rc1_funct_2,axiom,(
    ! [A: $i,B: $i] :
    ? [C: $i] :
      ( ( v1_funct_2 @ C @ A @ B )
      & ( v1_funct_1 @ C )
      & ( v5_relat_1 @ C @ B )
      & ( v4_relat_1 @ C @ A )
      & ( v1_relat_1 @ C )
      & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) )).

thf('205',plain,(
    ! [X22: $i,X23: $i] :
      ( m1_subset_1 @ ( sk_C @ X22 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('206',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(reflexivity_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_funct_2 @ A @ B @ C @ C ) ) )).

thf('207',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( r2_funct_2 @ X24 @ X25 @ X26 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('208',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('211',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['208','209','210'])).

thf('212',plain,
    ( ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ ( sk_C @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( sk_C @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['205','211'])).

thf('213',plain,(
    ! [X22: $i,X23: $i] :
      ( v1_funct_1 @ ( sk_C @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('214',plain,(
    ! [X22: $i,X23: $i] :
      ( v1_funct_2 @ ( sk_C @ X22 @ X23 ) @ X23 @ X22 ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('215',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['212','213','214'])).

thf('216',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('217',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    $false ),
    inference(demod,[status(thm)],['204','215','216','217','218'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jBwEhuze19
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:41:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.58/0.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.58/0.77  % Solved by: fo/fo7.sh
% 0.58/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.77  % done 551 iterations in 0.304s
% 0.58/0.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.58/0.77  % SZS output start Refutation
% 0.58/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.77  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.58/0.77  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.58/0.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.77  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.58/0.77  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.58/0.77  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.58/0.77  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.58/0.77  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.58/0.77  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.58/0.77  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.58/0.77  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.58/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.77  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.58/0.77  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.58/0.77  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.58/0.77  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.58/0.77  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.58/0.77  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.58/0.77  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.58/0.77  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.58/0.77  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.58/0.77  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.58/0.77  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.58/0.77  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.58/0.77  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.58/0.77  thf(t65_funct_1, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.58/0.77       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.58/0.77  thf('0', plain,
% 0.58/0.77      (![X10 : $i]:
% 0.58/0.77         (~ (v2_funct_1 @ X10)
% 0.58/0.77          | ((k2_funct_1 @ (k2_funct_1 @ X10)) = (X10))
% 0.58/0.77          | ~ (v1_funct_1 @ X10)
% 0.58/0.77          | ~ (v1_relat_1 @ X10))),
% 0.58/0.77      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.58/0.77  thf(d3_struct_0, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.58/0.77  thf('1', plain,
% 0.58/0.77      (![X31 : $i]:
% 0.58/0.77         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.58/0.77      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.58/0.77  thf('2', plain,
% 0.58/0.77      (![X31 : $i]:
% 0.58/0.77         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.58/0.77      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.58/0.77  thf(t64_tops_2, conjecture,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( l1_struct_0 @ A ) =>
% 0.58/0.77       ( ![B:$i]:
% 0.58/0.77         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.58/0.77           ( ![C:$i]:
% 0.58/0.77             ( ( ( v1_funct_1 @ C ) & 
% 0.58/0.77                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.58/0.77                 ( m1_subset_1 @
% 0.58/0.77                   C @ 
% 0.58/0.77                   ( k1_zfmisc_1 @
% 0.58/0.77                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.58/0.77               ( ( ( ( k2_relset_1 @
% 0.58/0.77                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.58/0.77                     ( k2_struct_0 @ B ) ) & 
% 0.58/0.77                   ( v2_funct_1 @ C ) ) =>
% 0.58/0.77                 ( r2_funct_2 @
% 0.58/0.77                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.58/0.77                   ( k2_tops_2 @
% 0.58/0.77                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.58/0.77                     ( k2_tops_2 @
% 0.58/0.77                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.58/0.77                   C ) ) ) ) ) ) ))).
% 0.58/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.77    (~( ![A:$i]:
% 0.58/0.77        ( ( l1_struct_0 @ A ) =>
% 0.58/0.77          ( ![B:$i]:
% 0.58/0.77            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.58/0.77              ( ![C:$i]:
% 0.58/0.77                ( ( ( v1_funct_1 @ C ) & 
% 0.58/0.77                    ( v1_funct_2 @
% 0.58/0.77                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.58/0.77                    ( m1_subset_1 @
% 0.58/0.77                      C @ 
% 0.58/0.77                      ( k1_zfmisc_1 @
% 0.58/0.77                        ( k2_zfmisc_1 @
% 0.58/0.77                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.58/0.77                  ( ( ( ( k2_relset_1 @
% 0.58/0.77                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.58/0.77                        ( k2_struct_0 @ B ) ) & 
% 0.58/0.77                      ( v2_funct_1 @ C ) ) =>
% 0.58/0.77                    ( r2_funct_2 @
% 0.58/0.77                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.58/0.77                      ( k2_tops_2 @
% 0.58/0.77                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.58/0.77                        ( k2_tops_2 @
% 0.58/0.77                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.58/0.77                      C ) ) ) ) ) ) ) )),
% 0.58/0.77    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.58/0.77  thf('3', plain,
% 0.58/0.77      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.58/0.77           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1)) @ 
% 0.58/0.77          sk_C_1)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('4', plain,
% 0.58/0.77      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.58/0.77            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)) @ 
% 0.58/0.77           sk_C_1)
% 0.58/0.77        | ~ (l1_struct_0 @ sk_B))),
% 0.58/0.77      inference('sup-', [status(thm)], ['2', '3'])).
% 0.58/0.77  thf('5', plain, ((l1_struct_0 @ sk_B)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('6', plain,
% 0.58/0.77      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.58/0.77           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)) @ 
% 0.58/0.77          sk_C_1)),
% 0.58/0.77      inference('demod', [status(thm)], ['4', '5'])).
% 0.58/0.77  thf('7', plain,
% 0.58/0.77      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.58/0.77            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)) @ 
% 0.58/0.77           sk_C_1)
% 0.58/0.77        | ~ (l1_struct_0 @ sk_B))),
% 0.58/0.77      inference('sup-', [status(thm)], ['1', '6'])).
% 0.58/0.77  thf('8', plain, ((l1_struct_0 @ sk_B)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('9', plain,
% 0.58/0.77      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.58/0.77           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)) @ 
% 0.58/0.77          sk_C_1)),
% 0.58/0.77      inference('demod', [status(thm)], ['7', '8'])).
% 0.58/0.77  thf('10', plain,
% 0.58/0.77      ((m1_subset_1 @ sk_C_1 @ 
% 0.58/0.77        (k1_zfmisc_1 @ 
% 0.58/0.77         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf(cc5_funct_2, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.58/0.77       ( ![C:$i]:
% 0.58/0.77         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.77           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.58/0.77             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.58/0.77  thf('11', plain,
% 0.58/0.77      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.58/0.77         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.58/0.77          | (v1_partfun1 @ X17 @ X18)
% 0.58/0.77          | ~ (v1_funct_2 @ X17 @ X18 @ X19)
% 0.58/0.77          | ~ (v1_funct_1 @ X17)
% 0.58/0.77          | (v1_xboole_0 @ X19))),
% 0.58/0.77      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.58/0.77  thf('12', plain,
% 0.58/0.77      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.58/0.77        | ~ (v1_funct_1 @ sk_C_1)
% 0.58/0.77        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.58/0.77        | (v1_partfun1 @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['10', '11'])).
% 0.58/0.77  thf('13', plain, ((v1_funct_1 @ sk_C_1)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('14', plain,
% 0.58/0.77      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('15', plain,
% 0.58/0.77      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.58/0.77        | (v1_partfun1 @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.77      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.58/0.77  thf(d4_partfun1, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.58/0.77       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.58/0.77  thf('16', plain,
% 0.58/0.77      (![X20 : $i, X21 : $i]:
% 0.58/0.77         (~ (v1_partfun1 @ X21 @ X20)
% 0.58/0.77          | ((k1_relat_1 @ X21) = (X20))
% 0.58/0.77          | ~ (v4_relat_1 @ X21 @ X20)
% 0.58/0.77          | ~ (v1_relat_1 @ X21))),
% 0.58/0.77      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.58/0.77  thf('17', plain,
% 0.58/0.77      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.58/0.77        | ~ (v1_relat_1 @ sk_C_1)
% 0.58/0.77        | ~ (v4_relat_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 0.58/0.77        | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['15', '16'])).
% 0.58/0.77  thf('18', plain,
% 0.58/0.77      ((m1_subset_1 @ sk_C_1 @ 
% 0.58/0.77        (k1_zfmisc_1 @ 
% 0.58/0.77         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf(cc2_relat_1, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( v1_relat_1 @ A ) =>
% 0.58/0.77       ( ![B:$i]:
% 0.58/0.77         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.58/0.77  thf('19', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.58/0.77          | (v1_relat_1 @ X0)
% 0.58/0.77          | ~ (v1_relat_1 @ X1))),
% 0.58/0.77      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.58/0.77  thf('20', plain,
% 0.58/0.77      ((~ (v1_relat_1 @ 
% 0.58/0.77           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.58/0.77        | (v1_relat_1 @ sk_C_1))),
% 0.58/0.77      inference('sup-', [status(thm)], ['18', '19'])).
% 0.58/0.77  thf(fc6_relat_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.58/0.77  thf('21', plain,
% 0.58/0.77      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.58/0.77      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.58/0.77  thf('22', plain, ((v1_relat_1 @ sk_C_1)),
% 0.58/0.77      inference('demod', [status(thm)], ['20', '21'])).
% 0.58/0.77  thf('23', plain,
% 0.58/0.77      ((m1_subset_1 @ sk_C_1 @ 
% 0.58/0.77        (k1_zfmisc_1 @ 
% 0.58/0.77         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf(cc2_relset_1, axiom,
% 0.58/0.77    (![A:$i,B:$i,C:$i]:
% 0.58/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.77       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.58/0.77  thf('24', plain,
% 0.58/0.77      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.58/0.77         ((v4_relat_1 @ X11 @ X12)
% 0.58/0.77          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.58/0.77      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.58/0.77  thf('25', plain, ((v4_relat_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.58/0.77      inference('sup-', [status(thm)], ['23', '24'])).
% 0.58/0.77  thf('26', plain,
% 0.58/0.77      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.58/0.77        | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 0.58/0.77      inference('demod', [status(thm)], ['17', '22', '25'])).
% 0.58/0.77  thf('27', plain,
% 0.58/0.77      (![X31 : $i]:
% 0.58/0.77         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.58/0.77      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.58/0.77  thf('28', plain,
% 0.58/0.77      ((m1_subset_1 @ sk_C_1 @ 
% 0.58/0.77        (k1_zfmisc_1 @ 
% 0.58/0.77         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('29', plain,
% 0.58/0.77      (((m1_subset_1 @ sk_C_1 @ 
% 0.58/0.77         (k1_zfmisc_1 @ 
% 0.58/0.77          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.58/0.77        | ~ (l1_struct_0 @ sk_A))),
% 0.58/0.77      inference('sup+', [status(thm)], ['27', '28'])).
% 0.58/0.77  thf('30', plain, ((l1_struct_0 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('31', plain,
% 0.58/0.77      ((m1_subset_1 @ sk_C_1 @ 
% 0.58/0.77        (k1_zfmisc_1 @ 
% 0.58/0.77         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.58/0.77      inference('demod', [status(thm)], ['29', '30'])).
% 0.58/0.77  thf('32', plain,
% 0.58/0.77      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.58/0.77         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.58/0.77          | (v1_partfun1 @ X17 @ X18)
% 0.58/0.77          | ~ (v1_funct_2 @ X17 @ X18 @ X19)
% 0.58/0.77          | ~ (v1_funct_1 @ X17)
% 0.58/0.77          | (v1_xboole_0 @ X19))),
% 0.58/0.77      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.58/0.77  thf('33', plain,
% 0.58/0.77      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.58/0.77        | ~ (v1_funct_1 @ sk_C_1)
% 0.58/0.77        | ~ (v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.58/0.77        | (v1_partfun1 @ sk_C_1 @ (k2_struct_0 @ sk_A)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['31', '32'])).
% 0.58/0.77  thf('34', plain, ((v1_funct_1 @ sk_C_1)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('35', plain,
% 0.58/0.77      (![X31 : $i]:
% 0.58/0.77         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.58/0.77      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.58/0.77  thf('36', plain,
% 0.58/0.77      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('37', plain,
% 0.58/0.77      (((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.58/0.77        | ~ (l1_struct_0 @ sk_A))),
% 0.58/0.77      inference('sup+', [status(thm)], ['35', '36'])).
% 0.58/0.77  thf('38', plain, ((l1_struct_0 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('39', plain,
% 0.58/0.77      ((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.58/0.77      inference('demod', [status(thm)], ['37', '38'])).
% 0.58/0.77  thf('40', plain,
% 0.58/0.77      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.58/0.77        | (v1_partfun1 @ sk_C_1 @ (k2_struct_0 @ sk_A)))),
% 0.58/0.77      inference('demod', [status(thm)], ['33', '34', '39'])).
% 0.58/0.77  thf('41', plain,
% 0.58/0.77      (![X20 : $i, X21 : $i]:
% 0.58/0.77         (~ (v1_partfun1 @ X21 @ X20)
% 0.58/0.77          | ((k1_relat_1 @ X21) = (X20))
% 0.58/0.77          | ~ (v4_relat_1 @ X21 @ X20)
% 0.58/0.77          | ~ (v1_relat_1 @ X21))),
% 0.58/0.77      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.58/0.77  thf('42', plain,
% 0.58/0.77      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.58/0.77        | ~ (v1_relat_1 @ sk_C_1)
% 0.58/0.77        | ~ (v4_relat_1 @ sk_C_1 @ (k2_struct_0 @ sk_A))
% 0.58/0.77        | ((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['40', '41'])).
% 0.58/0.77  thf('43', plain, ((v1_relat_1 @ sk_C_1)),
% 0.58/0.77      inference('demod', [status(thm)], ['20', '21'])).
% 0.58/0.77  thf('44', plain,
% 0.58/0.77      ((m1_subset_1 @ sk_C_1 @ 
% 0.58/0.77        (k1_zfmisc_1 @ 
% 0.58/0.77         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.58/0.77      inference('demod', [status(thm)], ['29', '30'])).
% 0.58/0.77  thf('45', plain,
% 0.58/0.77      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.58/0.77         ((v4_relat_1 @ X11 @ X12)
% 0.58/0.77          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.58/0.77      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.58/0.77  thf('46', plain, ((v4_relat_1 @ sk_C_1 @ (k2_struct_0 @ sk_A))),
% 0.58/0.77      inference('sup-', [status(thm)], ['44', '45'])).
% 0.58/0.77  thf('47', plain,
% 0.58/0.77      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.58/0.77        | ((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A)))),
% 0.58/0.77      inference('demod', [status(thm)], ['42', '43', '46'])).
% 0.58/0.77  thf(fc2_struct_0, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.58/0.77       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.58/0.77  thf('48', plain,
% 0.58/0.77      (![X32 : $i]:
% 0.58/0.77         (~ (v1_xboole_0 @ (u1_struct_0 @ X32))
% 0.58/0.77          | ~ (l1_struct_0 @ X32)
% 0.58/0.77          | (v2_struct_0 @ X32))),
% 0.58/0.77      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.58/0.77  thf('49', plain,
% 0.58/0.77      ((((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A))
% 0.58/0.77        | (v2_struct_0 @ sk_B)
% 0.58/0.77        | ~ (l1_struct_0 @ sk_B))),
% 0.58/0.77      inference('sup-', [status(thm)], ['47', '48'])).
% 0.58/0.77  thf('50', plain, ((l1_struct_0 @ sk_B)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('51', plain,
% 0.58/0.77      ((((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.58/0.77      inference('demod', [status(thm)], ['49', '50'])).
% 0.58/0.77  thf('52', plain, (~ (v2_struct_0 @ sk_B)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('53', plain, (((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A))),
% 0.58/0.77      inference('clc', [status(thm)], ['51', '52'])).
% 0.58/0.77  thf('54', plain,
% 0.58/0.77      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.58/0.77        | ((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))),
% 0.58/0.77      inference('demod', [status(thm)], ['26', '53'])).
% 0.58/0.77  thf('55', plain,
% 0.58/0.77      (![X32 : $i]:
% 0.58/0.77         (~ (v1_xboole_0 @ (u1_struct_0 @ X32))
% 0.58/0.77          | ~ (l1_struct_0 @ X32)
% 0.58/0.77          | (v2_struct_0 @ X32))),
% 0.58/0.77      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.58/0.77  thf('56', plain,
% 0.58/0.77      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))
% 0.58/0.77        | (v2_struct_0 @ sk_B)
% 0.58/0.77        | ~ (l1_struct_0 @ sk_B))),
% 0.58/0.77      inference('sup-', [status(thm)], ['54', '55'])).
% 0.58/0.77  thf('57', plain, ((l1_struct_0 @ sk_B)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('58', plain,
% 0.58/0.77      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.58/0.77      inference('demod', [status(thm)], ['56', '57'])).
% 0.58/0.77  thf('59', plain, (~ (v2_struct_0 @ sk_B)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('60', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.58/0.77      inference('clc', [status(thm)], ['58', '59'])).
% 0.58/0.77  thf('61', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.58/0.77      inference('clc', [status(thm)], ['58', '59'])).
% 0.58/0.77  thf('62', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.58/0.77      inference('clc', [status(thm)], ['58', '59'])).
% 0.58/0.77  thf('63', plain,
% 0.58/0.77      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.58/0.77           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)) @ 
% 0.58/0.77          sk_C_1)),
% 0.58/0.77      inference('demod', [status(thm)], ['9', '60', '61', '62'])).
% 0.58/0.77  thf('64', plain,
% 0.58/0.77      (![X31 : $i]:
% 0.58/0.77         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.58/0.77      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.58/0.77  thf('65', plain,
% 0.58/0.77      ((m1_subset_1 @ sk_C_1 @ 
% 0.58/0.77        (k1_zfmisc_1 @ 
% 0.58/0.77         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.58/0.77      inference('demod', [status(thm)], ['29', '30'])).
% 0.58/0.77  thf('66', plain,
% 0.58/0.77      (((m1_subset_1 @ sk_C_1 @ 
% 0.58/0.77         (k1_zfmisc_1 @ 
% 0.58/0.77          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.58/0.77        | ~ (l1_struct_0 @ sk_B))),
% 0.58/0.77      inference('sup+', [status(thm)], ['64', '65'])).
% 0.58/0.77  thf('67', plain, ((l1_struct_0 @ sk_B)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('68', plain,
% 0.58/0.77      ((m1_subset_1 @ sk_C_1 @ 
% 0.58/0.77        (k1_zfmisc_1 @ 
% 0.58/0.77         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.58/0.77      inference('demod', [status(thm)], ['66', '67'])).
% 0.58/0.77  thf(d4_tops_2, axiom,
% 0.58/0.77    (![A:$i,B:$i,C:$i]:
% 0.58/0.77     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.58/0.77         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.77       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.58/0.77         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.58/0.77  thf('69', plain,
% 0.58/0.77      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.58/0.77         (((k2_relset_1 @ X34 @ X33 @ X35) != (X33))
% 0.58/0.77          | ~ (v2_funct_1 @ X35)
% 0.58/0.77          | ((k2_tops_2 @ X34 @ X33 @ X35) = (k2_funct_1 @ X35))
% 0.58/0.77          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.58/0.77          | ~ (v1_funct_2 @ X35 @ X34 @ X33)
% 0.58/0.77          | ~ (v1_funct_1 @ X35))),
% 0.58/0.77      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.58/0.77  thf('70', plain,
% 0.58/0.77      ((~ (v1_funct_1 @ sk_C_1)
% 0.58/0.77        | ~ (v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.58/0.77        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)
% 0.58/0.77            = (k2_funct_1 @ sk_C_1))
% 0.58/0.77        | ~ (v2_funct_1 @ sk_C_1)
% 0.58/0.77        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)
% 0.58/0.77            != (k2_struct_0 @ sk_B)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['68', '69'])).
% 0.58/0.77  thf('71', plain, ((v1_funct_1 @ sk_C_1)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('72', plain,
% 0.58/0.77      (![X31 : $i]:
% 0.58/0.77         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.58/0.77      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.58/0.77  thf('73', plain,
% 0.58/0.77      ((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.58/0.77      inference('demod', [status(thm)], ['37', '38'])).
% 0.58/0.77  thf('74', plain,
% 0.58/0.77      (((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.58/0.77        | ~ (l1_struct_0 @ sk_B))),
% 0.58/0.77      inference('sup+', [status(thm)], ['72', '73'])).
% 0.58/0.77  thf('75', plain, ((l1_struct_0 @ sk_B)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('76', plain,
% 0.58/0.77      ((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.58/0.77      inference('demod', [status(thm)], ['74', '75'])).
% 0.58/0.77  thf('77', plain, ((v2_funct_1 @ sk_C_1)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('78', plain,
% 0.58/0.77      (![X31 : $i]:
% 0.58/0.77         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.58/0.77      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.58/0.77  thf('79', plain,
% 0.58/0.77      (![X31 : $i]:
% 0.58/0.77         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.58/0.77      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.58/0.77  thf('80', plain,
% 0.58/0.77      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1)
% 0.58/0.77         = (k2_struct_0 @ sk_B))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('81', plain,
% 0.58/0.77      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1)
% 0.58/0.77          = (k2_struct_0 @ sk_B))
% 0.58/0.77        | ~ (l1_struct_0 @ sk_A))),
% 0.58/0.77      inference('sup+', [status(thm)], ['79', '80'])).
% 0.58/0.77  thf('82', plain, ((l1_struct_0 @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('83', plain,
% 0.58/0.77      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1)
% 0.58/0.77         = (k2_struct_0 @ sk_B))),
% 0.58/0.77      inference('demod', [status(thm)], ['81', '82'])).
% 0.58/0.77  thf('84', plain,
% 0.58/0.77      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)
% 0.58/0.77          = (k2_struct_0 @ sk_B))
% 0.58/0.77        | ~ (l1_struct_0 @ sk_B))),
% 0.58/0.77      inference('sup+', [status(thm)], ['78', '83'])).
% 0.58/0.77  thf('85', plain, ((l1_struct_0 @ sk_B)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('86', plain,
% 0.58/0.77      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)
% 0.58/0.77         = (k2_struct_0 @ sk_B))),
% 0.58/0.77      inference('demod', [status(thm)], ['84', '85'])).
% 0.58/0.77  thf('87', plain,
% 0.58/0.77      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)
% 0.58/0.77          = (k2_funct_1 @ sk_C_1))
% 0.58/0.77        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.58/0.77      inference('demod', [status(thm)], ['70', '71', '76', '77', '86'])).
% 0.58/0.77  thf('88', plain,
% 0.58/0.77      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)
% 0.58/0.77         = (k2_funct_1 @ sk_C_1))),
% 0.58/0.77      inference('simplify', [status(thm)], ['87'])).
% 0.58/0.77  thf('89', plain,
% 0.58/0.77      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.58/0.77           (k2_funct_1 @ sk_C_1)) @ 
% 0.58/0.77          sk_C_1)),
% 0.58/0.77      inference('demod', [status(thm)], ['63', '88'])).
% 0.58/0.77  thf('90', plain,
% 0.58/0.77      ((m1_subset_1 @ sk_C_1 @ 
% 0.58/0.77        (k1_zfmisc_1 @ 
% 0.58/0.77         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.58/0.77      inference('demod', [status(thm)], ['66', '67'])).
% 0.58/0.77  thf(t31_funct_2, axiom,
% 0.58/0.77    (![A:$i,B:$i,C:$i]:
% 0.58/0.77     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.58/0.77         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.77       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.58/0.77         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.58/0.77           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.58/0.77           ( m1_subset_1 @
% 0.58/0.77             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.58/0.77  thf('91', plain,
% 0.58/0.77      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.58/0.77         (~ (v2_funct_1 @ X28)
% 0.58/0.77          | ((k2_relset_1 @ X30 @ X29 @ X28) != (X29))
% 0.58/0.77          | (m1_subset_1 @ (k2_funct_1 @ X28) @ 
% 0.58/0.77             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.58/0.77          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 0.58/0.77          | ~ (v1_funct_2 @ X28 @ X30 @ X29)
% 0.58/0.77          | ~ (v1_funct_1 @ X28))),
% 0.58/0.77      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.58/0.77  thf('92', plain,
% 0.58/0.77      ((~ (v1_funct_1 @ sk_C_1)
% 0.58/0.77        | ~ (v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.58/0.77        | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.58/0.77           (k1_zfmisc_1 @ 
% 0.58/0.77            (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.58/0.77        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)
% 0.58/0.77            != (k2_struct_0 @ sk_B))
% 0.58/0.77        | ~ (v2_funct_1 @ sk_C_1))),
% 0.58/0.77      inference('sup-', [status(thm)], ['90', '91'])).
% 0.58/0.77  thf('93', plain, ((v1_funct_1 @ sk_C_1)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('94', plain,
% 0.58/0.77      ((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.58/0.77      inference('demod', [status(thm)], ['74', '75'])).
% 0.58/0.77  thf('95', plain,
% 0.58/0.77      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)
% 0.58/0.77         = (k2_struct_0 @ sk_B))),
% 0.58/0.77      inference('demod', [status(thm)], ['84', '85'])).
% 0.58/0.77  thf('96', plain, ((v2_funct_1 @ sk_C_1)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('97', plain,
% 0.58/0.77      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.58/0.77         (k1_zfmisc_1 @ 
% 0.58/0.77          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.58/0.77        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.58/0.77      inference('demod', [status(thm)], ['92', '93', '94', '95', '96'])).
% 0.58/0.77  thf('98', plain,
% 0.58/0.77      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.58/0.77        (k1_zfmisc_1 @ 
% 0.58/0.77         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.58/0.77      inference('simplify', [status(thm)], ['97'])).
% 0.58/0.77  thf('99', plain,
% 0.58/0.77      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.58/0.77         (((k2_relset_1 @ X34 @ X33 @ X35) != (X33))
% 0.58/0.77          | ~ (v2_funct_1 @ X35)
% 0.58/0.77          | ((k2_tops_2 @ X34 @ X33 @ X35) = (k2_funct_1 @ X35))
% 0.58/0.77          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.58/0.77          | ~ (v1_funct_2 @ X35 @ X34 @ X33)
% 0.58/0.77          | ~ (v1_funct_1 @ X35))),
% 0.58/0.77      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.58/0.77  thf('100', plain,
% 0.58/0.77      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.58/0.77        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ (k2_struct_0 @ sk_B) @ 
% 0.58/0.77             (k2_struct_0 @ sk_A))
% 0.58/0.77        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.58/0.77            (k2_funct_1 @ sk_C_1)) = (k2_funct_1 @ (k2_funct_1 @ sk_C_1)))
% 0.58/0.77        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.58/0.77        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.58/0.77            (k2_funct_1 @ sk_C_1)) != (k2_struct_0 @ sk_A)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['98', '99'])).
% 0.58/0.77  thf('101', plain,
% 0.58/0.77      ((m1_subset_1 @ sk_C_1 @ 
% 0.58/0.77        (k1_zfmisc_1 @ 
% 0.58/0.77         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.58/0.77      inference('demod', [status(thm)], ['66', '67'])).
% 0.58/0.77  thf('102', plain,
% 0.58/0.77      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.58/0.77         (~ (v2_funct_1 @ X28)
% 0.58/0.77          | ((k2_relset_1 @ X30 @ X29 @ X28) != (X29))
% 0.58/0.77          | (v1_funct_1 @ (k2_funct_1 @ X28))
% 0.58/0.77          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 0.58/0.77          | ~ (v1_funct_2 @ X28 @ X30 @ X29)
% 0.58/0.77          | ~ (v1_funct_1 @ X28))),
% 0.58/0.77      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.58/0.77  thf('103', plain,
% 0.58/0.77      ((~ (v1_funct_1 @ sk_C_1)
% 0.58/0.77        | ~ (v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.58/0.77        | (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.58/0.77        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)
% 0.58/0.77            != (k2_struct_0 @ sk_B))
% 0.58/0.77        | ~ (v2_funct_1 @ sk_C_1))),
% 0.58/0.77      inference('sup-', [status(thm)], ['101', '102'])).
% 0.58/0.77  thf('104', plain, ((v1_funct_1 @ sk_C_1)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('105', plain,
% 0.58/0.77      ((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.58/0.77      inference('demod', [status(thm)], ['74', '75'])).
% 0.58/0.77  thf('106', plain,
% 0.58/0.77      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)
% 0.58/0.77         = (k2_struct_0 @ sk_B))),
% 0.58/0.77      inference('demod', [status(thm)], ['84', '85'])).
% 0.58/0.77  thf('107', plain, ((v2_funct_1 @ sk_C_1)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('108', plain,
% 0.58/0.77      (((v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.58/0.77        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.58/0.77      inference('demod', [status(thm)], ['103', '104', '105', '106', '107'])).
% 0.58/0.77  thf('109', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))),
% 0.58/0.77      inference('simplify', [status(thm)], ['108'])).
% 0.58/0.77  thf('110', plain,
% 0.58/0.77      ((m1_subset_1 @ sk_C_1 @ 
% 0.58/0.77        (k1_zfmisc_1 @ 
% 0.58/0.77         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.58/0.77      inference('demod', [status(thm)], ['66', '67'])).
% 0.58/0.77  thf('111', plain,
% 0.58/0.77      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.58/0.77         (~ (v2_funct_1 @ X28)
% 0.58/0.77          | ((k2_relset_1 @ X30 @ X29 @ X28) != (X29))
% 0.58/0.77          | (v1_funct_2 @ (k2_funct_1 @ X28) @ X29 @ X30)
% 0.58/0.77          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 0.58/0.77          | ~ (v1_funct_2 @ X28 @ X30 @ X29)
% 0.58/0.77          | ~ (v1_funct_1 @ X28))),
% 0.58/0.77      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.58/0.77  thf('112', plain,
% 0.58/0.77      ((~ (v1_funct_1 @ sk_C_1)
% 0.58/0.77        | ~ (v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.58/0.77        | (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ (k2_struct_0 @ sk_B) @ 
% 0.58/0.77           (k2_struct_0 @ sk_A))
% 0.58/0.77        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)
% 0.58/0.77            != (k2_struct_0 @ sk_B))
% 0.58/0.77        | ~ (v2_funct_1 @ sk_C_1))),
% 0.58/0.77      inference('sup-', [status(thm)], ['110', '111'])).
% 0.58/0.77  thf('113', plain, ((v1_funct_1 @ sk_C_1)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('114', plain,
% 0.58/0.77      ((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.58/0.77      inference('demod', [status(thm)], ['74', '75'])).
% 0.58/0.77  thf('115', plain,
% 0.58/0.77      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)
% 0.58/0.77         = (k2_struct_0 @ sk_B))),
% 0.58/0.77      inference('demod', [status(thm)], ['84', '85'])).
% 0.58/0.77  thf('116', plain, ((v2_funct_1 @ sk_C_1)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('117', plain,
% 0.58/0.77      (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ (k2_struct_0 @ sk_B) @ 
% 0.58/0.77         (k2_struct_0 @ sk_A))
% 0.58/0.77        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.58/0.77      inference('demod', [status(thm)], ['112', '113', '114', '115', '116'])).
% 0.58/0.77  thf('118', plain,
% 0.58/0.77      ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ (k2_struct_0 @ sk_B) @ 
% 0.58/0.77        (k2_struct_0 @ sk_A))),
% 0.58/0.77      inference('simplify', [status(thm)], ['117'])).
% 0.58/0.77  thf(t55_funct_1, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.58/0.77       ( ( v2_funct_1 @ A ) =>
% 0.58/0.77         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.58/0.77           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.58/0.77  thf('119', plain,
% 0.58/0.77      (![X8 : $i]:
% 0.58/0.77         (~ (v2_funct_1 @ X8)
% 0.58/0.77          | ((k2_relat_1 @ X8) = (k1_relat_1 @ (k2_funct_1 @ X8)))
% 0.58/0.77          | ~ (v1_funct_1 @ X8)
% 0.58/0.77          | ~ (v1_relat_1 @ X8))),
% 0.58/0.77      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.58/0.77  thf('120', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))),
% 0.58/0.77      inference('simplify', [status(thm)], ['108'])).
% 0.58/0.77  thf(t61_funct_1, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.58/0.77       ( ( v2_funct_1 @ A ) =>
% 0.58/0.77         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.58/0.77             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.58/0.77           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.58/0.77             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.58/0.77  thf('121', plain,
% 0.58/0.77      (![X9 : $i]:
% 0.58/0.77         (~ (v2_funct_1 @ X9)
% 0.58/0.77          | ((k5_relat_1 @ X9 @ (k2_funct_1 @ X9))
% 0.58/0.77              = (k6_relat_1 @ (k1_relat_1 @ X9)))
% 0.58/0.77          | ~ (v1_funct_1 @ X9)
% 0.58/0.77          | ~ (v1_relat_1 @ X9))),
% 0.58/0.77      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.58/0.77  thf(t48_funct_1, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.58/0.77       ( ![B:$i]:
% 0.58/0.77         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.58/0.77           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.58/0.77               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.58/0.77             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.58/0.77  thf('122', plain,
% 0.58/0.77      (![X6 : $i, X7 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X6)
% 0.58/0.77          | ~ (v1_funct_1 @ X6)
% 0.58/0.77          | (v2_funct_1 @ X7)
% 0.58/0.77          | ((k2_relat_1 @ X6) != (k1_relat_1 @ X7))
% 0.58/0.77          | ~ (v2_funct_1 @ (k5_relat_1 @ X6 @ X7))
% 0.58/0.77          | ~ (v1_funct_1 @ X7)
% 0.58/0.77          | ~ (v1_relat_1 @ X7))),
% 0.58/0.77      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.58/0.77  thf('123', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (v2_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.58/0.77          | ~ (v1_relat_1 @ X0)
% 0.58/0.77          | ~ (v1_funct_1 @ X0)
% 0.58/0.77          | ~ (v2_funct_1 @ X0)
% 0.58/0.77          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.58/0.77          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.58/0.77          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.58/0.77          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.58/0.77          | ~ (v1_funct_1 @ X0)
% 0.58/0.77          | ~ (v1_relat_1 @ X0))),
% 0.58/0.77      inference('sup-', [status(thm)], ['121', '122'])).
% 0.58/0.77  thf(fc4_funct_1, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.58/0.77       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.58/0.77  thf('124', plain, (![X5 : $i]: (v2_funct_1 @ (k6_relat_1 @ X5))),
% 0.58/0.77      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.58/0.77  thf('125', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X0)
% 0.58/0.77          | ~ (v1_funct_1 @ X0)
% 0.58/0.77          | ~ (v2_funct_1 @ X0)
% 0.58/0.77          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.58/0.77          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.58/0.77          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.58/0.77          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.58/0.77          | ~ (v1_funct_1 @ X0)
% 0.58/0.77          | ~ (v1_relat_1 @ X0))),
% 0.58/0.77      inference('demod', [status(thm)], ['123', '124'])).
% 0.58/0.77  thf('126', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.58/0.77          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.58/0.77          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.58/0.77          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.58/0.77          | ~ (v2_funct_1 @ X0)
% 0.58/0.77          | ~ (v1_funct_1 @ X0)
% 0.58/0.77          | ~ (v1_relat_1 @ X0))),
% 0.58/0.77      inference('simplify', [status(thm)], ['125'])).
% 0.58/0.77  thf('127', plain,
% 0.58/0.77      ((~ (v1_relat_1 @ sk_C_1)
% 0.58/0.77        | ~ (v1_funct_1 @ sk_C_1)
% 0.58/0.77        | ~ (v2_funct_1 @ sk_C_1)
% 0.58/0.77        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 0.58/0.77        | ((k2_relat_1 @ sk_C_1) != (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 0.58/0.77        | (v2_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['120', '126'])).
% 0.58/0.77  thf('128', plain, ((v1_relat_1 @ sk_C_1)),
% 0.58/0.77      inference('demod', [status(thm)], ['20', '21'])).
% 0.58/0.77  thf('129', plain, ((v1_funct_1 @ sk_C_1)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('130', plain, ((v2_funct_1 @ sk_C_1)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('131', plain,
% 0.58/0.77      ((m1_subset_1 @ sk_C_1 @ 
% 0.58/0.77        (k1_zfmisc_1 @ 
% 0.58/0.77         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf(redefinition_k2_relset_1, axiom,
% 0.58/0.77    (![A:$i,B:$i,C:$i]:
% 0.58/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.77       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.58/0.77  thf('132', plain,
% 0.58/0.77      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.58/0.77         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.58/0.77          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.58/0.77      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.58/0.77  thf('133', plain,
% 0.58/0.77      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1)
% 0.58/0.77         = (k2_relat_1 @ sk_C_1))),
% 0.58/0.77      inference('sup-', [status(thm)], ['131', '132'])).
% 0.58/0.77  thf('134', plain,
% 0.58/0.77      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1)
% 0.58/0.77         = (k2_struct_0 @ sk_B))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('135', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B))),
% 0.58/0.77      inference('sup+', [status(thm)], ['133', '134'])).
% 0.58/0.77  thf('136', plain,
% 0.58/0.77      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 0.58/0.77        | ((k2_struct_0 @ sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 0.58/0.77        | (v2_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.58/0.77      inference('demod', [status(thm)], ['127', '128', '129', '130', '135'])).
% 0.58/0.77  thf('137', plain,
% 0.58/0.77      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.58/0.77        (k1_zfmisc_1 @ 
% 0.58/0.77         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.58/0.77      inference('simplify', [status(thm)], ['97'])).
% 0.58/0.77  thf('138', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.58/0.77          | (v1_relat_1 @ X0)
% 0.58/0.77          | ~ (v1_relat_1 @ X1))),
% 0.58/0.77      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.58/0.77  thf('139', plain,
% 0.58/0.77      ((~ (v1_relat_1 @ 
% 0.58/0.77           (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))
% 0.58/0.77        | (v1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['137', '138'])).
% 0.58/0.77  thf('140', plain,
% 0.58/0.77      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.58/0.77      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.58/0.77  thf('141', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C_1))),
% 0.58/0.77      inference('demod', [status(thm)], ['139', '140'])).
% 0.58/0.77  thf('142', plain,
% 0.58/0.77      ((((k2_struct_0 @ sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 0.58/0.77        | (v2_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.58/0.77      inference('demod', [status(thm)], ['136', '141'])).
% 0.58/0.77  thf('143', plain,
% 0.58/0.77      ((((k2_struct_0 @ sk_B) != (k2_relat_1 @ sk_C_1))
% 0.58/0.77        | ~ (v1_relat_1 @ sk_C_1)
% 0.58/0.77        | ~ (v1_funct_1 @ sk_C_1)
% 0.58/0.77        | ~ (v2_funct_1 @ sk_C_1)
% 0.58/0.77        | (v2_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['119', '142'])).
% 0.58/0.77  thf('144', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B))),
% 0.58/0.77      inference('sup+', [status(thm)], ['133', '134'])).
% 0.58/0.77  thf('145', plain, ((v1_relat_1 @ sk_C_1)),
% 0.58/0.77      inference('demod', [status(thm)], ['20', '21'])).
% 0.58/0.77  thf('146', plain, ((v1_funct_1 @ sk_C_1)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('147', plain, ((v2_funct_1 @ sk_C_1)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('148', plain,
% 0.58/0.77      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.58/0.77        | (v2_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.58/0.77      inference('demod', [status(thm)], ['143', '144', '145', '146', '147'])).
% 0.58/0.77  thf('149', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C_1))),
% 0.58/0.77      inference('simplify', [status(thm)], ['148'])).
% 0.58/0.77  thf('150', plain,
% 0.58/0.77      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.58/0.77        (k1_zfmisc_1 @ 
% 0.58/0.77         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.58/0.77      inference('simplify', [status(thm)], ['97'])).
% 0.58/0.77  thf('151', plain,
% 0.58/0.77      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.58/0.77         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.58/0.77          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.58/0.77      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.58/0.77  thf('152', plain,
% 0.58/0.77      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.58/0.77         (k2_funct_1 @ sk_C_1)) = (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['150', '151'])).
% 0.58/0.77  thf('153', plain,
% 0.58/0.77      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.58/0.77          (k2_funct_1 @ sk_C_1)) = (k2_funct_1 @ (k2_funct_1 @ sk_C_1)))
% 0.58/0.77        | ((k2_relat_1 @ (k2_funct_1 @ sk_C_1)) != (k2_struct_0 @ sk_A)))),
% 0.58/0.77      inference('demod', [status(thm)], ['100', '109', '118', '149', '152'])).
% 0.58/0.77  thf('154', plain,
% 0.58/0.77      (![X8 : $i]:
% 0.58/0.77         (~ (v2_funct_1 @ X8)
% 0.58/0.77          | ((k1_relat_1 @ X8) = (k2_relat_1 @ (k2_funct_1 @ X8)))
% 0.58/0.77          | ~ (v1_funct_1 @ X8)
% 0.58/0.77          | ~ (v1_relat_1 @ X8))),
% 0.58/0.77      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.58/0.77  thf('155', plain,
% 0.58/0.77      (![X8 : $i]:
% 0.58/0.77         (~ (v2_funct_1 @ X8)
% 0.58/0.77          | ((k2_relat_1 @ X8) = (k1_relat_1 @ (k2_funct_1 @ X8)))
% 0.58/0.77          | ~ (v1_funct_1 @ X8)
% 0.58/0.77          | ~ (v1_relat_1 @ X8))),
% 0.58/0.77      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.58/0.77  thf('156', plain,
% 0.58/0.77      (![X10 : $i]:
% 0.58/0.77         (~ (v2_funct_1 @ X10)
% 0.58/0.77          | ((k2_funct_1 @ (k2_funct_1 @ X10)) = (X10))
% 0.58/0.77          | ~ (v1_funct_1 @ X10)
% 0.58/0.77          | ~ (v1_relat_1 @ X10))),
% 0.58/0.77      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.58/0.77  thf('157', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C_1))),
% 0.58/0.77      inference('simplify', [status(thm)], ['148'])).
% 0.58/0.77  thf('158', plain,
% 0.58/0.77      (![X10 : $i]:
% 0.58/0.77         (~ (v2_funct_1 @ X10)
% 0.58/0.77          | ((k2_funct_1 @ (k2_funct_1 @ X10)) = (X10))
% 0.58/0.77          | ~ (v1_funct_1 @ X10)
% 0.58/0.77          | ~ (v1_relat_1 @ X10))),
% 0.58/0.77      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.58/0.77  thf('159', plain,
% 0.58/0.77      (![X8 : $i]:
% 0.58/0.77         (~ (v2_funct_1 @ X8)
% 0.58/0.77          | ((k1_relat_1 @ X8) = (k2_relat_1 @ (k2_funct_1 @ X8)))
% 0.58/0.77          | ~ (v1_funct_1 @ X8)
% 0.58/0.77          | ~ (v1_relat_1 @ X8))),
% 0.58/0.77      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.58/0.77  thf('160', plain,
% 0.58/0.77      (![X10 : $i]:
% 0.58/0.77         (~ (v2_funct_1 @ X10)
% 0.58/0.77          | ((k2_funct_1 @ (k2_funct_1 @ X10)) = (X10))
% 0.58/0.77          | ~ (v1_funct_1 @ X10)
% 0.58/0.77          | ~ (v1_relat_1 @ X10))),
% 0.58/0.77      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.58/0.77  thf('161', plain,
% 0.58/0.77      (![X8 : $i]:
% 0.58/0.77         (~ (v2_funct_1 @ X8)
% 0.58/0.77          | ((k2_relat_1 @ X8) = (k1_relat_1 @ (k2_funct_1 @ X8)))
% 0.58/0.77          | ~ (v1_funct_1 @ X8)
% 0.58/0.77          | ~ (v1_relat_1 @ X8))),
% 0.58/0.77      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.58/0.77  thf('162', plain,
% 0.58/0.77      (![X20 : $i, X21 : $i]:
% 0.58/0.77         (((k1_relat_1 @ X21) != (X20))
% 0.58/0.77          | (v1_partfun1 @ X21 @ X20)
% 0.58/0.77          | ~ (v4_relat_1 @ X21 @ X20)
% 0.58/0.77          | ~ (v1_relat_1 @ X21))),
% 0.58/0.77      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.58/0.77  thf('163', plain,
% 0.58/0.77      (![X21 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X21)
% 0.58/0.77          | ~ (v4_relat_1 @ X21 @ (k1_relat_1 @ X21))
% 0.58/0.77          | (v1_partfun1 @ X21 @ (k1_relat_1 @ X21)))),
% 0.58/0.77      inference('simplify', [status(thm)], ['162'])).
% 0.58/0.77  thf('164', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.58/0.77          | ~ (v1_relat_1 @ X0)
% 0.58/0.77          | ~ (v1_funct_1 @ X0)
% 0.58/0.77          | ~ (v2_funct_1 @ X0)
% 0.58/0.77          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.58/0.77          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['161', '163'])).
% 0.58/0.77  thf('165', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.58/0.77          | ~ (v1_relat_1 @ X0)
% 0.58/0.77          | ~ (v1_funct_1 @ X0)
% 0.58/0.77          | ~ (v2_funct_1 @ X0)
% 0.58/0.77          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.58/0.77          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.58/0.77             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.58/0.77          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.58/0.77          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.58/0.77          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['160', '164'])).
% 0.58/0.77  thf('166', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.58/0.77          | ~ (v1_relat_1 @ X0)
% 0.58/0.77          | ~ (v1_funct_1 @ X0)
% 0.58/0.77          | ~ (v2_funct_1 @ X0)
% 0.58/0.77          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.58/0.77          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.58/0.77          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.58/0.77          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.58/0.77             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.58/0.77          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.58/0.77          | ~ (v2_funct_1 @ X0)
% 0.58/0.77          | ~ (v1_funct_1 @ X0)
% 0.58/0.77          | ~ (v1_relat_1 @ X0))),
% 0.58/0.77      inference('sup-', [status(thm)], ['159', '165'])).
% 0.58/0.77  thf('167', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.58/0.77          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.58/0.77             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.58/0.77          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.58/0.77          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.58/0.77          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.58/0.77          | ~ (v2_funct_1 @ X0)
% 0.58/0.77          | ~ (v1_funct_1 @ X0)
% 0.58/0.77          | ~ (v1_relat_1 @ X0)
% 0.58/0.77          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.58/0.77      inference('simplify', [status(thm)], ['166'])).
% 0.58/0.77  thf('168', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (v1_relat_1 @ X0)
% 0.58/0.77          | ~ (v1_relat_1 @ X0)
% 0.58/0.77          | ~ (v1_funct_1 @ X0)
% 0.58/0.77          | ~ (v2_funct_1 @ X0)
% 0.58/0.77          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.58/0.77          | ~ (v1_relat_1 @ X0)
% 0.58/0.77          | ~ (v1_funct_1 @ X0)
% 0.58/0.77          | ~ (v2_funct_1 @ X0)
% 0.58/0.77          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.58/0.77          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.58/0.77          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.58/0.77          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.58/0.77             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.58/0.77      inference('sup-', [status(thm)], ['158', '167'])).
% 0.58/0.77  thf('169', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.58/0.77           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.58/0.77          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.58/0.77          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.58/0.77          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.58/0.77          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.58/0.77          | ~ (v2_funct_1 @ X0)
% 0.58/0.77          | ~ (v1_funct_1 @ X0)
% 0.58/0.77          | ~ (v1_relat_1 @ X0))),
% 0.58/0.77      inference('simplify', [status(thm)], ['168'])).
% 0.58/0.77  thf('170', plain,
% 0.58/0.77      ((~ (v1_relat_1 @ sk_C_1)
% 0.58/0.77        | ~ (v1_funct_1 @ sk_C_1)
% 0.58/0.77        | ~ (v2_funct_1 @ sk_C_1)
% 0.58/0.77        | ~ (v4_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1))
% 0.58/0.77        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 0.58/0.77        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.58/0.77        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C_1)) @ 
% 0.58/0.77           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C_1)))))),
% 0.58/0.77      inference('sup-', [status(thm)], ['157', '169'])).
% 0.58/0.77  thf('171', plain, ((v1_relat_1 @ sk_C_1)),
% 0.58/0.77      inference('demod', [status(thm)], ['20', '21'])).
% 0.58/0.77  thf('172', plain, ((v1_funct_1 @ sk_C_1)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('173', plain, ((v2_funct_1 @ sk_C_1)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('174', plain, (((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A))),
% 0.58/0.77      inference('clc', [status(thm)], ['51', '52'])).
% 0.58/0.77  thf('175', plain, ((v4_relat_1 @ sk_C_1 @ (k2_struct_0 @ sk_A))),
% 0.58/0.77      inference('sup-', [status(thm)], ['44', '45'])).
% 0.58/0.77  thf('176', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C_1))),
% 0.58/0.77      inference('demod', [status(thm)], ['139', '140'])).
% 0.58/0.77  thf('177', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))),
% 0.58/0.77      inference('simplify', [status(thm)], ['108'])).
% 0.58/0.77  thf('178', plain,
% 0.58/0.77      ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C_1)) @ 
% 0.58/0.77        (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.58/0.77      inference('demod', [status(thm)],
% 0.58/0.77                ['170', '171', '172', '173', '174', '175', '176', '177'])).
% 0.58/0.77  thf('179', plain,
% 0.58/0.77      (((v1_partfun1 @ sk_C_1 @ 
% 0.58/0.77         (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C_1))))
% 0.58/0.77        | ~ (v1_relat_1 @ sk_C_1)
% 0.58/0.77        | ~ (v1_funct_1 @ sk_C_1)
% 0.58/0.77        | ~ (v2_funct_1 @ sk_C_1))),
% 0.58/0.77      inference('sup+', [status(thm)], ['156', '178'])).
% 0.58/0.77  thf('180', plain, ((v1_relat_1 @ sk_C_1)),
% 0.58/0.77      inference('demod', [status(thm)], ['20', '21'])).
% 0.58/0.77  thf('181', plain, ((v1_funct_1 @ sk_C_1)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('182', plain, ((v2_funct_1 @ sk_C_1)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('183', plain,
% 0.58/0.77      ((v1_partfun1 @ sk_C_1 @ 
% 0.58/0.77        (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.58/0.77      inference('demod', [status(thm)], ['179', '180', '181', '182'])).
% 0.58/0.77  thf('184', plain,
% 0.58/0.77      (((v1_partfun1 @ sk_C_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 0.58/0.77        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 0.58/0.77        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.58/0.77        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.58/0.77      inference('sup+', [status(thm)], ['155', '183'])).
% 0.58/0.77  thf('185', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C_1))),
% 0.58/0.77      inference('demod', [status(thm)], ['139', '140'])).
% 0.58/0.77  thf('186', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))),
% 0.58/0.77      inference('simplify', [status(thm)], ['108'])).
% 0.58/0.77  thf('187', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C_1))),
% 0.58/0.77      inference('simplify', [status(thm)], ['148'])).
% 0.58/0.77  thf('188', plain,
% 0.58/0.77      ((v1_partfun1 @ sk_C_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.58/0.77      inference('demod', [status(thm)], ['184', '185', '186', '187'])).
% 0.58/0.77  thf('189', plain,
% 0.58/0.77      (![X20 : $i, X21 : $i]:
% 0.58/0.77         (~ (v1_partfun1 @ X21 @ X20)
% 0.58/0.77          | ((k1_relat_1 @ X21) = (X20))
% 0.58/0.77          | ~ (v4_relat_1 @ X21 @ X20)
% 0.58/0.77          | ~ (v1_relat_1 @ X21))),
% 0.58/0.77      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.58/0.77  thf('190', plain,
% 0.58/0.77      ((~ (v1_relat_1 @ sk_C_1)
% 0.58/0.77        | ~ (v4_relat_1 @ sk_C_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 0.58/0.77        | ((k1_relat_1 @ sk_C_1) = (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.58/0.77      inference('sup-', [status(thm)], ['188', '189'])).
% 0.58/0.77  thf('191', plain, ((v1_relat_1 @ sk_C_1)),
% 0.58/0.77      inference('demod', [status(thm)], ['20', '21'])).
% 0.58/0.77  thf('192', plain, (((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A))),
% 0.58/0.77      inference('clc', [status(thm)], ['51', '52'])).
% 0.58/0.77  thf('193', plain,
% 0.58/0.77      ((~ (v4_relat_1 @ sk_C_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 0.58/0.77        | ((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.58/0.77      inference('demod', [status(thm)], ['190', '191', '192'])).
% 0.58/0.77  thf('194', plain,
% 0.58/0.77      ((~ (v4_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1))
% 0.58/0.77        | ~ (v1_relat_1 @ sk_C_1)
% 0.58/0.77        | ~ (v1_funct_1 @ sk_C_1)
% 0.58/0.77        | ~ (v2_funct_1 @ sk_C_1)
% 0.58/0.77        | ((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.58/0.77      inference('sup-', [status(thm)], ['154', '193'])).
% 0.58/0.77  thf('195', plain, (((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A))),
% 0.58/0.77      inference('clc', [status(thm)], ['51', '52'])).
% 0.58/0.77  thf('196', plain, ((v4_relat_1 @ sk_C_1 @ (k2_struct_0 @ sk_A))),
% 0.58/0.77      inference('sup-', [status(thm)], ['44', '45'])).
% 0.58/0.77  thf('197', plain, ((v1_relat_1 @ sk_C_1)),
% 0.58/0.77      inference('demod', [status(thm)], ['20', '21'])).
% 0.58/0.77  thf('198', plain, ((v1_funct_1 @ sk_C_1)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('199', plain, ((v2_funct_1 @ sk_C_1)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('200', plain,
% 0.58/0.77      (((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.58/0.77      inference('demod', [status(thm)],
% 0.58/0.77                ['194', '195', '196', '197', '198', '199'])).
% 0.58/0.77  thf('201', plain,
% 0.58/0.77      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.58/0.77          (k2_funct_1 @ sk_C_1)) = (k2_funct_1 @ (k2_funct_1 @ sk_C_1)))
% 0.58/0.77        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))),
% 0.58/0.77      inference('demod', [status(thm)], ['153', '200'])).
% 0.58/0.77  thf('202', plain,
% 0.58/0.77      (((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.58/0.77         (k2_funct_1 @ sk_C_1)) = (k2_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.58/0.77      inference('simplify', [status(thm)], ['201'])).
% 0.58/0.77  thf('203', plain,
% 0.58/0.77      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77          (k2_funct_1 @ (k2_funct_1 @ sk_C_1)) @ sk_C_1)),
% 0.58/0.77      inference('demod', [status(thm)], ['89', '202'])).
% 0.58/0.77  thf('204', plain,
% 0.58/0.77      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1 @ 
% 0.58/0.77           sk_C_1)
% 0.58/0.77        | ~ (v1_relat_1 @ sk_C_1)
% 0.58/0.77        | ~ (v1_funct_1 @ sk_C_1)
% 0.58/0.77        | ~ (v2_funct_1 @ sk_C_1))),
% 0.58/0.77      inference('sup-', [status(thm)], ['0', '203'])).
% 0.58/0.77  thf(rc1_funct_2, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ?[C:$i]:
% 0.58/0.77       ( ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) & 
% 0.58/0.77         ( v5_relat_1 @ C @ B ) & ( v4_relat_1 @ C @ A ) & 
% 0.58/0.77         ( v1_relat_1 @ C ) & 
% 0.58/0.77         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.58/0.77  thf('205', plain,
% 0.58/0.77      (![X22 : $i, X23 : $i]:
% 0.58/0.77         (m1_subset_1 @ (sk_C @ X22 @ X23) @ 
% 0.58/0.77          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))),
% 0.58/0.77      inference('cnf', [status(esa)], [rc1_funct_2])).
% 0.58/0.77  thf('206', plain,
% 0.58/0.77      ((m1_subset_1 @ sk_C_1 @ 
% 0.58/0.77        (k1_zfmisc_1 @ 
% 0.58/0.77         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.58/0.77      inference('demod', [status(thm)], ['29', '30'])).
% 0.58/0.77  thf(reflexivity_r2_funct_2, axiom,
% 0.58/0.77    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.77     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.58/0.77         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.58/0.77         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.58/0.77         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.77       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.58/0.77  thf('207', plain,
% 0.58/0.77      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.58/0.77         ((r2_funct_2 @ X24 @ X25 @ X26 @ X26)
% 0.58/0.77          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.58/0.77          | ~ (v1_funct_2 @ X26 @ X24 @ X25)
% 0.58/0.77          | ~ (v1_funct_1 @ X26)
% 0.58/0.77          | ~ (v1_funct_1 @ X27)
% 0.58/0.77          | ~ (v1_funct_2 @ X27 @ X24 @ X25)
% 0.58/0.77          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.58/0.77      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.58/0.77  thf('208', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (m1_subset_1 @ X0 @ 
% 0.58/0.77             (k1_zfmisc_1 @ 
% 0.58/0.77              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.58/0.77          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.58/0.77          | ~ (v1_funct_1 @ X0)
% 0.58/0.77          | ~ (v1_funct_1 @ sk_C_1)
% 0.58/0.77          | ~ (v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ 
% 0.58/0.77               (u1_struct_0 @ sk_B))
% 0.58/0.77          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77             sk_C_1 @ sk_C_1))),
% 0.58/0.77      inference('sup-', [status(thm)], ['206', '207'])).
% 0.58/0.77  thf('209', plain, ((v1_funct_1 @ sk_C_1)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('210', plain,
% 0.58/0.77      ((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.58/0.77      inference('demod', [status(thm)], ['37', '38'])).
% 0.58/0.77  thf('211', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (m1_subset_1 @ X0 @ 
% 0.58/0.77             (k1_zfmisc_1 @ 
% 0.58/0.77              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.58/0.77          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.58/0.77          | ~ (v1_funct_1 @ X0)
% 0.58/0.77          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.58/0.77             sk_C_1 @ sk_C_1))),
% 0.58/0.77      inference('demod', [status(thm)], ['208', '209', '210'])).
% 0.58/0.77  thf('212', plain,
% 0.58/0.77      (((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1 @ 
% 0.58/0.77         sk_C_1)
% 0.58/0.77        | ~ (v1_funct_1 @ (sk_C @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))
% 0.58/0.77        | ~ (v1_funct_2 @ 
% 0.58/0.77             (sk_C @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)) @ 
% 0.58/0.77             (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['205', '211'])).
% 0.58/0.77  thf('213', plain, (![X22 : $i, X23 : $i]: (v1_funct_1 @ (sk_C @ X22 @ X23))),
% 0.58/0.77      inference('cnf', [status(esa)], [rc1_funct_2])).
% 0.58/0.77  thf('214', plain,
% 0.58/0.77      (![X22 : $i, X23 : $i]: (v1_funct_2 @ (sk_C @ X22 @ X23) @ X23 @ X22)),
% 0.58/0.77      inference('cnf', [status(esa)], [rc1_funct_2])).
% 0.58/0.77  thf('215', plain,
% 0.58/0.77      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1 @ 
% 0.58/0.77        sk_C_1)),
% 0.58/0.77      inference('demod', [status(thm)], ['212', '213', '214'])).
% 0.58/0.77  thf('216', plain, ((v1_relat_1 @ sk_C_1)),
% 0.58/0.77      inference('demod', [status(thm)], ['20', '21'])).
% 0.58/0.77  thf('217', plain, ((v1_funct_1 @ sk_C_1)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('218', plain, ((v2_funct_1 @ sk_C_1)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('219', plain, ($false),
% 0.58/0.77      inference('demod', [status(thm)], ['204', '215', '216', '217', '218'])).
% 0.58/0.77  
% 0.58/0.77  % SZS output end Refutation
% 0.58/0.77  
% 0.58/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
