%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.imIcQP6T97

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:49 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  249 (4026 expanded)
%              Number of leaves         :   40 (1166 expanded)
%              Depth                    :   22
%              Number of atoms          : 2439 (104150 expanded)
%              Number of equality atoms :  167 (5366 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t62_tops_2,conjecture,(
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
               => ( ( ( k1_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                    = ( k2_struct_0 @ B ) )
                  & ( ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                    = ( k2_struct_0 @ A ) ) ) ) ) ) ) )).

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
                 => ( ( ( k1_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                      = ( k2_struct_0 @ B ) )
                    & ( ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                      = ( k2_struct_0 @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_tops_2])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k1_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k2_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X14 @ ( k3_relset_1 @ X14 @ X15 @ X16 ) )
        = ( k1_relset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[t24_relset_1])).

thf('4',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k3_relset_1 @ A @ B @ C )
        = ( k4_relat_1 @ C ) ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k3_relset_1 @ X12 @ X13 @ X11 )
        = ( k4_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('7',plain,
    ( ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('9',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('12',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['9','14','15'])).

thf('17',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','16'])).

thf('18',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('19',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('28',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( v1_partfun1 @ X17 @ X18 )
      | ~ ( v1_funct_2 @ X17 @ X18 @ X19 )
      | ~ ( v1_funct_1 @ X17 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('32',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('37',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30','37'])).

thf('39',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('40',plain,(
    ! [X23: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('41',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['38','45'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('47',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_partfun1 @ X21 @ X20 )
      | ( ( k1_relat_1 @ X21 )
        = X20 )
      | ~ ( v4_relat_1 @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('50',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('53',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('54',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('56',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('57',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['49','50'])).

thf('61',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = ( k4_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('64',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['49','50'])).

thf('68',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['61','68'])).

thf('70',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','51','54','69'])).

thf('71',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','51','54','69'])).

thf('72',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relset_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['20','70','71'])).

thf('73',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('74',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['73','78'])).

thf('80',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('83',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('85',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['38','45'])).

thf('86',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_partfun1 @ X21 @ X20 )
      | ( ( k1_relat_1 @ X21 )
        = X20 )
      | ~ ( v4_relat_1 @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('90',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['49','50'])).

thf('92',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('93',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('94',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['61','68'])).

thf('96',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['90','91','94','95'])).

thf('97',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['83','96'])).

thf(dt_k2_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) )
        & ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A )
        & ( m1_subset_1 @ ( k2_tops_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) )).

thf('98',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X27 @ X28 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('99',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('102',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('103',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['101','106'])).

thf('108',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('111',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['90','91','94','95'])).

thf('113',plain,(
    v1_funct_2 @ sk_C @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['83','96'])).

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

thf('115',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X24 @ X26 )
       != X24 )
      | ~ ( v2_funct_1 @ X26 )
      | ( ( k2_tops_2 @ X25 @ X24 @ X26 )
        = ( k2_funct_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X25 @ X24 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('116',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_funct_2 @ sk_C @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('119',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('120',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('122',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('123',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['121','126'])).

thf('128',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('131',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('132',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['90','91','94','95'])).

thf('134',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['116','117','118','119','120','134'])).

thf('136',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['99','100','113','136'])).

thf('138',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('139',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['72','139'])).

thf('141',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['90','91','94','95'])).

thf('142',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('143',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('144',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('145',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['145'])).

thf('147',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['144','146'])).

thf('148',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['143','149'])).

thf('151',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['142','152'])).

thf('154',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['141','153'])).

thf('155',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['90','91','94','95'])).

thf('156',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','51','54','69'])).

thf('158',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['135'])).

thf('159',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('160',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['9','14','15'])).

thf('161',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','51','54','69'])).

thf('163',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','51','54','69'])).

thf('164',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relset_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['20','70','71'])).

thf('165',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relset_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['161','162','163','164'])).

thf('166',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['156','157','158','165'])).

thf('167',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('168',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['90','91','94','95'])).

thf('169',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X14 @ ( k3_relset_1 @ X14 @ X15 @ X16 ) )
        = ( k2_relset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[t24_relset_1])).

thf('171',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k3_relset_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_relset_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('173',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k3_relset_1 @ X12 @ X13 @ X11 )
        = ( k4_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('174',plain,
    ( ( k3_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['90','91','94','95'])).

thf('176',plain,
    ( ( k3_relset_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('178',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('179',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['90','91','94','95'])).

thf('181',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['179','180'])).

thf('182',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['171','176','181'])).

thf('183',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['135'])).

thf('184',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['90','91','94','95'])).

thf('185',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('186',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('187',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('188',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['145'])).

thf('189',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['189','190'])).

thf('192',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['186','191'])).

thf('193',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('195',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['185','194'])).

thf('196',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('197',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('198',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['184','197'])).

thf('199',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','51','54','69'])).

thf('200',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_tops_2 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['198','199'])).

thf('201',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k4_relat_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['183','200'])).

thf('202',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['182','201'])).

thf('203',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['202'])).

thf('204',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['145'])).

thf('205',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['203','204'])).

thf('206',plain,(
    ( k1_relset_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
 != ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['166','205'])).

thf('207',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['140','206'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.imIcQP6T97
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:45:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.38/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.57  % Solved by: fo/fo7.sh
% 0.38/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.57  % done 370 iterations in 0.099s
% 0.38/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.57  % SZS output start Refutation
% 0.38/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.57  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.38/0.57  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.38/0.57  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.38/0.57  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.38/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.57  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.38/0.57  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.38/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.57  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.38/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.57  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.38/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.57  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.38/0.57  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 0.38/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.57  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.38/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.57  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.38/0.57  thf(d3_struct_0, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.38/0.57  thf('0', plain,
% 0.38/0.57      (![X22 : $i]:
% 0.38/0.57         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.57  thf('1', plain,
% 0.38/0.57      (![X22 : $i]:
% 0.38/0.57         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.57  thf(t62_tops_2, conjecture,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( l1_struct_0 @ A ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.38/0.57           ( ![C:$i]:
% 0.38/0.57             ( ( ( v1_funct_1 @ C ) & 
% 0.38/0.57                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.57                 ( m1_subset_1 @
% 0.38/0.57                   C @ 
% 0.38/0.57                   ( k1_zfmisc_1 @
% 0.38/0.57                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.57               ( ( ( ( k2_relset_1 @
% 0.38/0.57                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.38/0.57                     ( k2_struct_0 @ B ) ) & 
% 0.38/0.57                   ( v2_funct_1 @ C ) ) =>
% 0.38/0.57                 ( ( ( k1_relset_1 @
% 0.38/0.57                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.38/0.57                       ( k2_tops_2 @
% 0.38/0.57                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.38/0.57                     ( k2_struct_0 @ B ) ) & 
% 0.38/0.57                   ( ( k2_relset_1 @
% 0.38/0.57                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.38/0.57                       ( k2_tops_2 @
% 0.38/0.57                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.38/0.57                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.38/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.57    (~( ![A:$i]:
% 0.38/0.57        ( ( l1_struct_0 @ A ) =>
% 0.38/0.57          ( ![B:$i]:
% 0.38/0.57            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.38/0.57              ( ![C:$i]:
% 0.38/0.57                ( ( ( v1_funct_1 @ C ) & 
% 0.38/0.57                    ( v1_funct_2 @
% 0.38/0.57                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.57                    ( m1_subset_1 @
% 0.38/0.57                      C @ 
% 0.38/0.57                      ( k1_zfmisc_1 @
% 0.38/0.57                        ( k2_zfmisc_1 @
% 0.38/0.57                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.57                  ( ( ( ( k2_relset_1 @
% 0.38/0.57                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.38/0.57                        ( k2_struct_0 @ B ) ) & 
% 0.38/0.57                      ( v2_funct_1 @ C ) ) =>
% 0.38/0.57                    ( ( ( k1_relset_1 @
% 0.38/0.57                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.38/0.57                          ( k2_tops_2 @
% 0.38/0.57                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.38/0.57                        ( k2_struct_0 @ B ) ) & 
% 0.38/0.57                      ( ( k2_relset_1 @
% 0.38/0.57                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.38/0.57                          ( k2_tops_2 @
% 0.38/0.57                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.38/0.57                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.38/0.57    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.38/0.57  thf('2', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C @ 
% 0.38/0.57        (k1_zfmisc_1 @ 
% 0.38/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(t24_relset_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.57       ( ( ( k1_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) ) =
% 0.38/0.57           ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.38/0.57         ( ( k2_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) ) =
% 0.38/0.57           ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.38/0.57  thf('3', plain,
% 0.38/0.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.38/0.57         (((k2_relset_1 @ X15 @ X14 @ (k3_relset_1 @ X14 @ X15 @ X16))
% 0.38/0.57            = (k1_relset_1 @ X14 @ X15 @ X16))
% 0.38/0.57          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.38/0.57      inference('cnf', [status(esa)], [t24_relset_1])).
% 0.38/0.57  thf('4', plain,
% 0.38/0.57      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57         (k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.38/0.57         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.38/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.57  thf('5', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C @ 
% 0.38/0.57        (k1_zfmisc_1 @ 
% 0.38/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(redefinition_k3_relset_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.57       ( ( k3_relset_1 @ A @ B @ C ) = ( k4_relat_1 @ C ) ) ))).
% 0.38/0.57  thf('6', plain,
% 0.38/0.57      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.38/0.57         (((k3_relset_1 @ X12 @ X13 @ X11) = (k4_relat_1 @ X11))
% 0.38/0.57          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.38/0.57      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 0.38/0.57  thf('7', plain,
% 0.38/0.57      (((k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.38/0.57         = (k4_relat_1 @ sk_C))),
% 0.38/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.57  thf('8', plain,
% 0.38/0.57      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57         (k4_relat_1 @ sk_C))
% 0.38/0.57         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.38/0.57      inference('demod', [status(thm)], ['4', '7'])).
% 0.38/0.57  thf('9', plain,
% 0.38/0.57      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57          (k4_relat_1 @ sk_C))
% 0.38/0.57          = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.38/0.57        | ~ (l1_struct_0 @ sk_B))),
% 0.38/0.57      inference('sup+', [status(thm)], ['1', '8'])).
% 0.38/0.57  thf('10', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C @ 
% 0.38/0.57        (k1_zfmisc_1 @ 
% 0.38/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(redefinition_k2_relset_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.57       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.38/0.57  thf('11', plain,
% 0.38/0.57      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.38/0.57         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 0.38/0.57          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.38/0.57      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.38/0.57  thf('12', plain,
% 0.38/0.57      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.38/0.57         = (k2_relat_1 @ sk_C))),
% 0.38/0.57      inference('sup-', [status(thm)], ['10', '11'])).
% 0.38/0.57  thf('13', plain,
% 0.38/0.57      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.38/0.57         = (k2_struct_0 @ sk_B))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('14', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.38/0.57      inference('sup+', [status(thm)], ['12', '13'])).
% 0.38/0.57  thf('15', plain, ((l1_struct_0 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('16', plain,
% 0.38/0.57      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57         (k4_relat_1 @ sk_C))
% 0.38/0.57         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.38/0.57      inference('demod', [status(thm)], ['9', '14', '15'])).
% 0.38/0.57  thf('17', plain,
% 0.38/0.57      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57          (k4_relat_1 @ sk_C))
% 0.38/0.57          = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.38/0.57        | ~ (l1_struct_0 @ sk_B))),
% 0.38/0.57      inference('sup+', [status(thm)], ['0', '16'])).
% 0.38/0.57  thf('18', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.38/0.57      inference('sup+', [status(thm)], ['12', '13'])).
% 0.38/0.57  thf('19', plain, ((l1_struct_0 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('20', plain,
% 0.38/0.57      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57         (k4_relat_1 @ sk_C))
% 0.38/0.57         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))),
% 0.38/0.57      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.38/0.57  thf('21', plain,
% 0.38/0.57      (![X22 : $i]:
% 0.38/0.57         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.57  thf('22', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C @ 
% 0.38/0.57        (k1_zfmisc_1 @ 
% 0.38/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('23', plain,
% 0.38/0.57      (((m1_subset_1 @ sk_C @ 
% 0.38/0.57         (k1_zfmisc_1 @ 
% 0.38/0.57          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.38/0.57        | ~ (l1_struct_0 @ sk_B))),
% 0.38/0.57      inference('sup+', [status(thm)], ['21', '22'])).
% 0.38/0.57  thf('24', plain, ((l1_struct_0 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('25', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C @ 
% 0.38/0.57        (k1_zfmisc_1 @ 
% 0.38/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.38/0.57      inference('demod', [status(thm)], ['23', '24'])).
% 0.38/0.57  thf('26', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.38/0.57      inference('sup+', [status(thm)], ['12', '13'])).
% 0.38/0.57  thf('27', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C @ 
% 0.38/0.57        (k1_zfmisc_1 @ 
% 0.38/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.38/0.57      inference('demod', [status(thm)], ['25', '26'])).
% 0.38/0.57  thf(cc5_funct_2, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.38/0.57       ( ![C:$i]:
% 0.38/0.57         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.57           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.38/0.57             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.38/0.57  thf('28', plain,
% 0.38/0.57      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.38/0.57          | (v1_partfun1 @ X17 @ X18)
% 0.38/0.57          | ~ (v1_funct_2 @ X17 @ X18 @ X19)
% 0.38/0.57          | ~ (v1_funct_1 @ X17)
% 0.38/0.57          | (v1_xboole_0 @ X19))),
% 0.38/0.57      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.38/0.57  thf('29', plain,
% 0.38/0.57      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.38/0.57        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.57        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.38/0.57        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['27', '28'])).
% 0.38/0.57  thf('30', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('31', plain,
% 0.38/0.57      (![X22 : $i]:
% 0.38/0.57         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.57  thf('32', plain,
% 0.38/0.57      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('33', plain,
% 0.38/0.57      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.38/0.57        | ~ (l1_struct_0 @ sk_B))),
% 0.38/0.57      inference('sup+', [status(thm)], ['31', '32'])).
% 0.38/0.57  thf('34', plain, ((l1_struct_0 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('35', plain,
% 0.38/0.57      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.38/0.57      inference('demod', [status(thm)], ['33', '34'])).
% 0.38/0.57  thf('36', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.38/0.57      inference('sup+', [status(thm)], ['12', '13'])).
% 0.38/0.57  thf('37', plain,
% 0.38/0.57      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.38/0.57      inference('demod', [status(thm)], ['35', '36'])).
% 0.38/0.57  thf('38', plain,
% 0.38/0.57      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.38/0.57        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('demod', [status(thm)], ['29', '30', '37'])).
% 0.38/0.57  thf('39', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.38/0.57      inference('sup+', [status(thm)], ['12', '13'])).
% 0.38/0.57  thf(fc5_struct_0, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.38/0.57       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.38/0.57  thf('40', plain,
% 0.38/0.57      (![X23 : $i]:
% 0.38/0.57         (~ (v1_xboole_0 @ (k2_struct_0 @ X23))
% 0.38/0.57          | ~ (l1_struct_0 @ X23)
% 0.38/0.57          | (v2_struct_0 @ X23))),
% 0.38/0.57      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.38/0.57  thf('41', plain,
% 0.38/0.57      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.38/0.57        | (v2_struct_0 @ sk_B)
% 0.38/0.57        | ~ (l1_struct_0 @ sk_B))),
% 0.38/0.57      inference('sup-', [status(thm)], ['39', '40'])).
% 0.38/0.57  thf('42', plain, ((l1_struct_0 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('43', plain,
% 0.38/0.57      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.38/0.57      inference('demod', [status(thm)], ['41', '42'])).
% 0.38/0.57  thf('44', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('45', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.38/0.57      inference('clc', [status(thm)], ['43', '44'])).
% 0.38/0.57  thf('46', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.38/0.57      inference('clc', [status(thm)], ['38', '45'])).
% 0.38/0.57  thf(d4_partfun1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.38/0.57       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.38/0.57  thf('47', plain,
% 0.38/0.57      (![X20 : $i, X21 : $i]:
% 0.38/0.57         (~ (v1_partfun1 @ X21 @ X20)
% 0.38/0.57          | ((k1_relat_1 @ X21) = (X20))
% 0.38/0.57          | ~ (v4_relat_1 @ X21 @ X20)
% 0.38/0.57          | ~ (v1_relat_1 @ X21))),
% 0.38/0.57      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.38/0.57  thf('48', plain,
% 0.38/0.57      ((~ (v1_relat_1 @ sk_C)
% 0.38/0.57        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.38/0.57        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['46', '47'])).
% 0.38/0.57  thf('49', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C @ 
% 0.38/0.57        (k1_zfmisc_1 @ 
% 0.38/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(cc1_relset_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.57       ( v1_relat_1 @ C ) ))).
% 0.38/0.57  thf('50', plain,
% 0.38/0.57      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.38/0.57         ((v1_relat_1 @ X2)
% 0.38/0.57          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.38/0.57      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.38/0.57  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.57      inference('sup-', [status(thm)], ['49', '50'])).
% 0.38/0.57  thf('52', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C @ 
% 0.38/0.57        (k1_zfmisc_1 @ 
% 0.38/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(cc2_relset_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.57       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.38/0.57  thf('53', plain,
% 0.38/0.57      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.38/0.57         ((v4_relat_1 @ X5 @ X6)
% 0.38/0.57          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.38/0.57      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.38/0.57  thf('54', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['52', '53'])).
% 0.38/0.57  thf('55', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(t55_funct_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.57       ( ( v2_funct_1 @ A ) =>
% 0.38/0.57         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.38/0.57           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.38/0.57  thf('56', plain,
% 0.38/0.57      (![X1 : $i]:
% 0.38/0.57         (~ (v2_funct_1 @ X1)
% 0.38/0.57          | ((k1_relat_1 @ X1) = (k2_relat_1 @ (k2_funct_1 @ X1)))
% 0.38/0.57          | ~ (v1_funct_1 @ X1)
% 0.38/0.57          | ~ (v1_relat_1 @ X1))),
% 0.38/0.57      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.38/0.57  thf('57', plain,
% 0.38/0.57      ((~ (v1_relat_1 @ sk_C)
% 0.38/0.57        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.38/0.57        | ~ (v2_funct_1 @ sk_C))),
% 0.38/0.57      inference('sup-', [status(thm)], ['55', '56'])).
% 0.38/0.57  thf('58', plain, ((v2_funct_1 @ sk_C)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('59', plain,
% 0.38/0.57      ((~ (v1_relat_1 @ sk_C)
% 0.38/0.57        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.38/0.57      inference('demod', [status(thm)], ['57', '58'])).
% 0.38/0.57  thf('60', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.57      inference('sup-', [status(thm)], ['49', '50'])).
% 0.38/0.57  thf('61', plain,
% 0.38/0.57      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.38/0.57      inference('demod', [status(thm)], ['59', '60'])).
% 0.38/0.57  thf('62', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(d9_funct_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.57       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.38/0.57  thf('63', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (v2_funct_1 @ X0)
% 0.38/0.57          | ((k2_funct_1 @ X0) = (k4_relat_1 @ X0))
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_relat_1 @ X0))),
% 0.38/0.57      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.38/0.57  thf('64', plain,
% 0.38/0.57      ((~ (v1_relat_1 @ sk_C)
% 0.38/0.57        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 0.38/0.57        | ~ (v2_funct_1 @ sk_C))),
% 0.38/0.57      inference('sup-', [status(thm)], ['62', '63'])).
% 0.38/0.57  thf('65', plain, ((v2_funct_1 @ sk_C)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('66', plain,
% 0.38/0.57      ((~ (v1_relat_1 @ sk_C) | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C)))),
% 0.38/0.57      inference('demod', [status(thm)], ['64', '65'])).
% 0.38/0.57  thf('67', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.57      inference('sup-', [status(thm)], ['49', '50'])).
% 0.38/0.57  thf('68', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.38/0.57      inference('demod', [status(thm)], ['66', '67'])).
% 0.38/0.57  thf('69', plain,
% 0.38/0.57      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.38/0.57      inference('demod', [status(thm)], ['61', '68'])).
% 0.38/0.57  thf('70', plain,
% 0.38/0.57      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (u1_struct_0 @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['48', '51', '54', '69'])).
% 0.38/0.57  thf('71', plain,
% 0.38/0.57      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (u1_struct_0 @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['48', '51', '54', '69'])).
% 0.38/0.57  thf('72', plain,
% 0.38/0.57      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ 
% 0.38/0.57         (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ (k4_relat_1 @ sk_C))
% 0.38/0.57         = (k1_relset_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 0.38/0.57            (k2_relat_1 @ sk_C) @ sk_C))),
% 0.38/0.57      inference('demod', [status(thm)], ['20', '70', '71'])).
% 0.38/0.57  thf('73', plain,
% 0.38/0.57      (![X22 : $i]:
% 0.38/0.57         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.57  thf('74', plain,
% 0.38/0.57      (![X22 : $i]:
% 0.38/0.57         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.57  thf('75', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C @ 
% 0.38/0.57        (k1_zfmisc_1 @ 
% 0.38/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('76', plain,
% 0.38/0.57      (((m1_subset_1 @ sk_C @ 
% 0.38/0.57         (k1_zfmisc_1 @ 
% 0.38/0.57          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.38/0.57        | ~ (l1_struct_0 @ sk_A))),
% 0.38/0.57      inference('sup+', [status(thm)], ['74', '75'])).
% 0.38/0.57  thf('77', plain, ((l1_struct_0 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('78', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C @ 
% 0.38/0.57        (k1_zfmisc_1 @ 
% 0.38/0.57         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.57      inference('demod', [status(thm)], ['76', '77'])).
% 0.38/0.57  thf('79', plain,
% 0.38/0.57      (((m1_subset_1 @ sk_C @ 
% 0.38/0.57         (k1_zfmisc_1 @ 
% 0.38/0.57          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.38/0.57        | ~ (l1_struct_0 @ sk_B))),
% 0.38/0.57      inference('sup+', [status(thm)], ['73', '78'])).
% 0.38/0.57  thf('80', plain, ((l1_struct_0 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('81', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C @ 
% 0.38/0.57        (k1_zfmisc_1 @ 
% 0.38/0.57         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.38/0.57      inference('demod', [status(thm)], ['79', '80'])).
% 0.38/0.57  thf('82', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.38/0.57      inference('sup+', [status(thm)], ['12', '13'])).
% 0.38/0.57  thf('83', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C @ 
% 0.38/0.57        (k1_zfmisc_1 @ 
% 0.38/0.57         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.38/0.57      inference('demod', [status(thm)], ['81', '82'])).
% 0.38/0.57  thf('84', plain,
% 0.38/0.57      (![X22 : $i]:
% 0.38/0.57         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.57  thf('85', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.38/0.57      inference('clc', [status(thm)], ['38', '45'])).
% 0.38/0.57  thf('86', plain,
% 0.38/0.57      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.38/0.57      inference('sup+', [status(thm)], ['84', '85'])).
% 0.38/0.57  thf('87', plain, ((l1_struct_0 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('88', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['86', '87'])).
% 0.38/0.57  thf('89', plain,
% 0.38/0.57      (![X20 : $i, X21 : $i]:
% 0.38/0.57         (~ (v1_partfun1 @ X21 @ X20)
% 0.38/0.57          | ((k1_relat_1 @ X21) = (X20))
% 0.38/0.57          | ~ (v4_relat_1 @ X21 @ X20)
% 0.38/0.57          | ~ (v1_relat_1 @ X21))),
% 0.38/0.57      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.38/0.57  thf('90', plain,
% 0.38/0.57      ((~ (v1_relat_1 @ sk_C)
% 0.38/0.57        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.38/0.57        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['88', '89'])).
% 0.38/0.57  thf('91', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.57      inference('sup-', [status(thm)], ['49', '50'])).
% 0.38/0.57  thf('92', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C @ 
% 0.38/0.57        (k1_zfmisc_1 @ 
% 0.38/0.57         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.57      inference('demod', [status(thm)], ['76', '77'])).
% 0.38/0.57  thf('93', plain,
% 0.38/0.57      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.38/0.57         ((v4_relat_1 @ X5 @ X6)
% 0.38/0.57          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.38/0.57      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.38/0.57  thf('94', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['92', '93'])).
% 0.38/0.57  thf('95', plain,
% 0.38/0.57      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.38/0.57      inference('demod', [status(thm)], ['61', '68'])).
% 0.38/0.57  thf('96', plain,
% 0.38/0.57      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['90', '91', '94', '95'])).
% 0.38/0.57  thf('97', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C @ 
% 0.38/0.57        (k1_zfmisc_1 @ 
% 0.38/0.57         (k2_zfmisc_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 0.38/0.57          (k2_relat_1 @ sk_C))))),
% 0.38/0.57      inference('demod', [status(thm)], ['83', '96'])).
% 0.38/0.57  thf(dt_k2_tops_2, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.38/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.57       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 0.38/0.57         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 0.38/0.57         ( m1_subset_1 @
% 0.38/0.57           ( k2_tops_2 @ A @ B @ C ) @ 
% 0.38/0.57           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 0.38/0.57  thf('98', plain,
% 0.38/0.57      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.38/0.57         ((m1_subset_1 @ (k2_tops_2 @ X27 @ X28 @ X29) @ 
% 0.38/0.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 0.38/0.57          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.38/0.57          | ~ (v1_funct_2 @ X29 @ X27 @ X28)
% 0.38/0.57          | ~ (v1_funct_1 @ X29))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.38/0.57  thf('99', plain,
% 0.38/0.57      ((~ (v1_funct_1 @ sk_C)
% 0.38/0.57        | ~ (v1_funct_2 @ sk_C @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 0.38/0.57             (k2_relat_1 @ sk_C))
% 0.38/0.57        | (m1_subset_1 @ 
% 0.38/0.57           (k2_tops_2 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 0.38/0.57            (k2_relat_1 @ sk_C) @ sk_C) @ 
% 0.38/0.57           (k1_zfmisc_1 @ 
% 0.38/0.57            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ 
% 0.38/0.57             (k2_relat_1 @ (k4_relat_1 @ sk_C))))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['97', '98'])).
% 0.38/0.57  thf('100', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('101', plain,
% 0.38/0.57      (![X22 : $i]:
% 0.38/0.57         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.57  thf('102', plain,
% 0.38/0.57      (![X22 : $i]:
% 0.38/0.57         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.57  thf('103', plain,
% 0.38/0.57      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('104', plain,
% 0.38/0.57      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.38/0.57        | ~ (l1_struct_0 @ sk_A))),
% 0.38/0.57      inference('sup+', [status(thm)], ['102', '103'])).
% 0.38/0.57  thf('105', plain, ((l1_struct_0 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('106', plain,
% 0.38/0.57      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.38/0.57      inference('demod', [status(thm)], ['104', '105'])).
% 0.38/0.57  thf('107', plain,
% 0.38/0.57      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.38/0.57        | ~ (l1_struct_0 @ sk_B))),
% 0.38/0.57      inference('sup+', [status(thm)], ['101', '106'])).
% 0.38/0.57  thf('108', plain, ((l1_struct_0 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('109', plain,
% 0.38/0.57      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.38/0.57      inference('demod', [status(thm)], ['107', '108'])).
% 0.38/0.57  thf('110', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.38/0.57      inference('sup+', [status(thm)], ['12', '13'])).
% 0.38/0.57  thf('111', plain,
% 0.38/0.57      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.38/0.57      inference('demod', [status(thm)], ['109', '110'])).
% 0.38/0.57  thf('112', plain,
% 0.38/0.57      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['90', '91', '94', '95'])).
% 0.38/0.57  thf('113', plain,
% 0.38/0.57      ((v1_funct_2 @ sk_C @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 0.38/0.57        (k2_relat_1 @ sk_C))),
% 0.38/0.57      inference('demod', [status(thm)], ['111', '112'])).
% 0.38/0.57  thf('114', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C @ 
% 0.38/0.57        (k1_zfmisc_1 @ 
% 0.38/0.57         (k2_zfmisc_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 0.38/0.57          (k2_relat_1 @ sk_C))))),
% 0.38/0.57      inference('demod', [status(thm)], ['83', '96'])).
% 0.38/0.57  thf(d4_tops_2, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.38/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.57       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.38/0.57         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.38/0.57  thf('115', plain,
% 0.38/0.57      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.38/0.57         (((k2_relset_1 @ X25 @ X24 @ X26) != (X24))
% 0.38/0.57          | ~ (v2_funct_1 @ X26)
% 0.38/0.57          | ((k2_tops_2 @ X25 @ X24 @ X26) = (k2_funct_1 @ X26))
% 0.38/0.57          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24)))
% 0.38/0.57          | ~ (v1_funct_2 @ X26 @ X25 @ X24)
% 0.38/0.57          | ~ (v1_funct_1 @ X26))),
% 0.38/0.57      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.38/0.57  thf('116', plain,
% 0.38/0.57      ((~ (v1_funct_1 @ sk_C)
% 0.38/0.57        | ~ (v1_funct_2 @ sk_C @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 0.38/0.57             (k2_relat_1 @ sk_C))
% 0.38/0.57        | ((k2_tops_2 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 0.38/0.57            (k2_relat_1 @ sk_C) @ sk_C) = (k2_funct_1 @ sk_C))
% 0.38/0.57        | ~ (v2_funct_1 @ sk_C)
% 0.38/0.57        | ((k2_relset_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 0.38/0.57            (k2_relat_1 @ sk_C) @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['114', '115'])).
% 0.38/0.57  thf('117', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('118', plain,
% 0.38/0.57      ((v1_funct_2 @ sk_C @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 0.38/0.57        (k2_relat_1 @ sk_C))),
% 0.38/0.57      inference('demod', [status(thm)], ['111', '112'])).
% 0.38/0.57  thf('119', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.38/0.57      inference('demod', [status(thm)], ['66', '67'])).
% 0.38/0.57  thf('120', plain, ((v2_funct_1 @ sk_C)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('121', plain,
% 0.38/0.57      (![X22 : $i]:
% 0.38/0.57         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.57  thf('122', plain,
% 0.38/0.57      (![X22 : $i]:
% 0.38/0.57         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.57  thf('123', plain,
% 0.38/0.57      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.38/0.57         = (k2_struct_0 @ sk_B))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('124', plain,
% 0.38/0.57      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.38/0.57          = (k2_struct_0 @ sk_B))
% 0.38/0.57        | ~ (l1_struct_0 @ sk_A))),
% 0.38/0.57      inference('sup+', [status(thm)], ['122', '123'])).
% 0.38/0.57  thf('125', plain, ((l1_struct_0 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('126', plain,
% 0.38/0.57      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.38/0.57         = (k2_struct_0 @ sk_B))),
% 0.38/0.57      inference('demod', [status(thm)], ['124', '125'])).
% 0.38/0.57  thf('127', plain,
% 0.38/0.57      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.38/0.57          = (k2_struct_0 @ sk_B))
% 0.38/0.57        | ~ (l1_struct_0 @ sk_B))),
% 0.38/0.57      inference('sup+', [status(thm)], ['121', '126'])).
% 0.38/0.57  thf('128', plain, ((l1_struct_0 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('129', plain,
% 0.38/0.57      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.38/0.57         = (k2_struct_0 @ sk_B))),
% 0.38/0.57      inference('demod', [status(thm)], ['127', '128'])).
% 0.38/0.57  thf('130', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.38/0.57      inference('sup+', [status(thm)], ['12', '13'])).
% 0.38/0.57  thf('131', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.38/0.57      inference('sup+', [status(thm)], ['12', '13'])).
% 0.38/0.57  thf('132', plain,
% 0.38/0.57      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.38/0.57         = (k2_relat_1 @ sk_C))),
% 0.38/0.57      inference('demod', [status(thm)], ['129', '130', '131'])).
% 0.38/0.57  thf('133', plain,
% 0.38/0.57      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['90', '91', '94', '95'])).
% 0.38/0.57  thf('134', plain,
% 0.38/0.57      (((k2_relset_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 0.38/0.57         (k2_relat_1 @ sk_C) @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.38/0.57      inference('demod', [status(thm)], ['132', '133'])).
% 0.38/0.57  thf('135', plain,
% 0.38/0.57      ((((k2_tops_2 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 0.38/0.57          (k2_relat_1 @ sk_C) @ sk_C) = (k4_relat_1 @ sk_C))
% 0.38/0.57        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.38/0.57      inference('demod', [status(thm)],
% 0.38/0.57                ['116', '117', '118', '119', '120', '134'])).
% 0.38/0.57  thf('136', plain,
% 0.38/0.57      (((k2_tops_2 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 0.38/0.57         (k2_relat_1 @ sk_C) @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.38/0.57      inference('simplify', [status(thm)], ['135'])).
% 0.38/0.57  thf('137', plain,
% 0.38/0.57      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.38/0.57        (k1_zfmisc_1 @ 
% 0.38/0.57         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ 
% 0.38/0.57          (k2_relat_1 @ (k4_relat_1 @ sk_C)))))),
% 0.38/0.57      inference('demod', [status(thm)], ['99', '100', '113', '136'])).
% 0.38/0.57  thf('138', plain,
% 0.38/0.57      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.38/0.57         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 0.38/0.57          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.38/0.57      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.38/0.57  thf('139', plain,
% 0.38/0.57      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ 
% 0.38/0.57         (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ (k4_relat_1 @ sk_C))
% 0.38/0.57         = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['137', '138'])).
% 0.38/0.57  thf('140', plain,
% 0.38/0.57      (((k1_relset_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 0.38/0.57         (k2_relat_1 @ sk_C) @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.38/0.57      inference('sup+', [status(thm)], ['72', '139'])).
% 0.38/0.57  thf('141', plain,
% 0.38/0.57      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['90', '91', '94', '95'])).
% 0.38/0.57  thf('142', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.38/0.57      inference('sup+', [status(thm)], ['12', '13'])).
% 0.38/0.57  thf('143', plain,
% 0.38/0.57      (![X22 : $i]:
% 0.38/0.57         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.57  thf('144', plain,
% 0.38/0.57      (![X22 : $i]:
% 0.38/0.57         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.57  thf('145', plain,
% 0.38/0.57      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.38/0.57          != (k2_struct_0 @ sk_B))
% 0.38/0.57        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.38/0.57            != (k2_struct_0 @ sk_A)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('146', plain,
% 0.38/0.57      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.38/0.57          != (k2_struct_0 @ sk_A)))
% 0.38/0.57         <= (~
% 0.38/0.57             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.38/0.57                = (k2_struct_0 @ sk_A))))),
% 0.38/0.57      inference('split', [status(esa)], ['145'])).
% 0.38/0.57  thf('147', plain,
% 0.38/0.57      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.38/0.57           != (k2_struct_0 @ sk_A))
% 0.38/0.57         | ~ (l1_struct_0 @ sk_A)))
% 0.38/0.57         <= (~
% 0.38/0.57             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.38/0.57                = (k2_struct_0 @ sk_A))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['144', '146'])).
% 0.38/0.57  thf('148', plain, ((l1_struct_0 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('149', plain,
% 0.38/0.57      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.38/0.57          != (k2_struct_0 @ sk_A)))
% 0.38/0.57         <= (~
% 0.38/0.57             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.38/0.57                = (k2_struct_0 @ sk_A))))),
% 0.38/0.57      inference('demod', [status(thm)], ['147', '148'])).
% 0.38/0.57  thf('150', plain,
% 0.38/0.57      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.38/0.57           != (k2_struct_0 @ sk_A))
% 0.38/0.57         | ~ (l1_struct_0 @ sk_B)))
% 0.38/0.57         <= (~
% 0.38/0.57             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.38/0.57                = (k2_struct_0 @ sk_A))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['143', '149'])).
% 0.38/0.57  thf('151', plain, ((l1_struct_0 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('152', plain,
% 0.38/0.57      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.38/0.57          != (k2_struct_0 @ sk_A)))
% 0.38/0.57         <= (~
% 0.38/0.57             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.38/0.57                = (k2_struct_0 @ sk_A))))),
% 0.38/0.57      inference('demod', [status(thm)], ['150', '151'])).
% 0.38/0.57  thf('153', plain,
% 0.38/0.57      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.38/0.57          != (k2_struct_0 @ sk_A)))
% 0.38/0.57         <= (~
% 0.38/0.57             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.38/0.57                = (k2_struct_0 @ sk_A))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['142', '152'])).
% 0.38/0.57  thf('154', plain,
% 0.38/0.57      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57          (k2_tops_2 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 0.38/0.57           (k2_relat_1 @ sk_C) @ sk_C))
% 0.38/0.57          != (k2_struct_0 @ sk_A)))
% 0.38/0.57         <= (~
% 0.38/0.57             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.38/0.57                = (k2_struct_0 @ sk_A))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['141', '153'])).
% 0.38/0.57  thf('155', plain,
% 0.38/0.57      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['90', '91', '94', '95'])).
% 0.38/0.57  thf('156', plain,
% 0.38/0.57      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57          (k2_tops_2 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 0.38/0.57           (k2_relat_1 @ sk_C) @ sk_C))
% 0.38/0.57          != (k2_relat_1 @ (k4_relat_1 @ sk_C))))
% 0.38/0.57         <= (~
% 0.38/0.57             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.38/0.57                = (k2_struct_0 @ sk_A))))),
% 0.38/0.57      inference('demod', [status(thm)], ['154', '155'])).
% 0.38/0.57  thf('157', plain,
% 0.38/0.57      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (u1_struct_0 @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['48', '51', '54', '69'])).
% 0.38/0.57  thf('158', plain,
% 0.38/0.57      (((k2_tops_2 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 0.38/0.57         (k2_relat_1 @ sk_C) @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.38/0.57      inference('simplify', [status(thm)], ['135'])).
% 0.38/0.57  thf('159', plain,
% 0.38/0.57      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57         (k4_relat_1 @ sk_C))
% 0.38/0.57         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.38/0.57      inference('demod', [status(thm)], ['4', '7'])).
% 0.38/0.57  thf('160', plain,
% 0.38/0.57      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57         (k4_relat_1 @ sk_C))
% 0.38/0.57         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.38/0.57      inference('demod', [status(thm)], ['9', '14', '15'])).
% 0.38/0.57  thf('161', plain,
% 0.38/0.57      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57         (k4_relat_1 @ sk_C))
% 0.38/0.57         = (k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57            (k4_relat_1 @ sk_C)))),
% 0.38/0.57      inference('demod', [status(thm)], ['159', '160'])).
% 0.38/0.57  thf('162', plain,
% 0.38/0.57      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (u1_struct_0 @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['48', '51', '54', '69'])).
% 0.38/0.57  thf('163', plain,
% 0.38/0.57      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (u1_struct_0 @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['48', '51', '54', '69'])).
% 0.38/0.57  thf('164', plain,
% 0.38/0.57      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ 
% 0.38/0.57         (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ (k4_relat_1 @ sk_C))
% 0.38/0.57         = (k1_relset_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 0.38/0.57            (k2_relat_1 @ sk_C) @ sk_C))),
% 0.38/0.57      inference('demod', [status(thm)], ['20', '70', '71'])).
% 0.38/0.57  thf('165', plain,
% 0.38/0.57      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.57         (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ (k4_relat_1 @ sk_C))
% 0.38/0.57         = (k1_relset_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 0.38/0.57            (k2_relat_1 @ sk_C) @ sk_C))),
% 0.38/0.57      inference('demod', [status(thm)], ['161', '162', '163', '164'])).
% 0.38/0.57  thf('166', plain,
% 0.38/0.57      ((((k1_relset_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 0.38/0.57          (k2_relat_1 @ sk_C) @ sk_C) != (k2_relat_1 @ (k4_relat_1 @ sk_C))))
% 0.38/0.57         <= (~
% 0.38/0.57             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.38/0.57                = (k2_struct_0 @ sk_A))))),
% 0.38/0.57      inference('demod', [status(thm)], ['156', '157', '158', '165'])).
% 0.38/0.57  thf('167', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C @ 
% 0.38/0.57        (k1_zfmisc_1 @ 
% 0.38/0.57         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.57      inference('demod', [status(thm)], ['76', '77'])).
% 0.38/0.57  thf('168', plain,
% 0.38/0.57      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['90', '91', '94', '95'])).
% 0.38/0.57  thf('169', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C @ 
% 0.38/0.57        (k1_zfmisc_1 @ 
% 0.38/0.57         (k2_zfmisc_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 0.38/0.57          (u1_struct_0 @ sk_B))))),
% 0.38/0.57      inference('demod', [status(thm)], ['167', '168'])).
% 0.38/0.57  thf('170', plain,
% 0.38/0.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.38/0.57         (((k1_relset_1 @ X15 @ X14 @ (k3_relset_1 @ X14 @ X15 @ X16))
% 0.38/0.57            = (k2_relset_1 @ X14 @ X15 @ X16))
% 0.38/0.57          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.38/0.57      inference('cnf', [status(esa)], [t24_relset_1])).
% 0.38/0.57  thf('171', plain,
% 0.38/0.57      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.57         (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 0.38/0.57         (k3_relset_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 0.38/0.57          (u1_struct_0 @ sk_B) @ sk_C))
% 0.38/0.57         = (k2_relset_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 0.38/0.57            (u1_struct_0 @ sk_B) @ sk_C))),
% 0.38/0.57      inference('sup-', [status(thm)], ['169', '170'])).
% 0.38/0.57  thf('172', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C @ 
% 0.38/0.57        (k1_zfmisc_1 @ 
% 0.38/0.57         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.57      inference('demod', [status(thm)], ['76', '77'])).
% 0.38/0.57  thf('173', plain,
% 0.38/0.57      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.38/0.57         (((k3_relset_1 @ X12 @ X13 @ X11) = (k4_relat_1 @ X11))
% 0.38/0.57          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.38/0.57      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 0.38/0.57  thf('174', plain,
% 0.38/0.57      (((k3_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.38/0.57         = (k4_relat_1 @ sk_C))),
% 0.38/0.57      inference('sup-', [status(thm)], ['172', '173'])).
% 0.38/0.57  thf('175', plain,
% 0.38/0.57      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['90', '91', '94', '95'])).
% 0.38/0.57  thf('176', plain,
% 0.38/0.57      (((k3_relset_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 0.38/0.57         (u1_struct_0 @ sk_B) @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.38/0.57      inference('demod', [status(thm)], ['174', '175'])).
% 0.38/0.57  thf('177', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C @ 
% 0.38/0.57        (k1_zfmisc_1 @ 
% 0.38/0.57         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.57      inference('demod', [status(thm)], ['76', '77'])).
% 0.38/0.57  thf('178', plain,
% 0.38/0.57      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.38/0.57         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 0.38/0.57          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.38/0.57      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.38/0.57  thf('179', plain,
% 0.38/0.57      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.38/0.57         = (k2_relat_1 @ sk_C))),
% 0.38/0.57      inference('sup-', [status(thm)], ['177', '178'])).
% 0.38/0.57  thf('180', plain,
% 0.38/0.57      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['90', '91', '94', '95'])).
% 0.38/0.57  thf('181', plain,
% 0.38/0.57      (((k2_relset_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 0.38/0.57         (u1_struct_0 @ sk_B) @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.38/0.57      inference('demod', [status(thm)], ['179', '180'])).
% 0.38/0.57  thf('182', plain,
% 0.38/0.57      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.57         (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ (k4_relat_1 @ sk_C))
% 0.38/0.57         = (k2_relat_1 @ sk_C))),
% 0.38/0.57      inference('demod', [status(thm)], ['171', '176', '181'])).
% 0.38/0.57  thf('183', plain,
% 0.38/0.57      (((k2_tops_2 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 0.38/0.57         (k2_relat_1 @ sk_C) @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.38/0.57      inference('simplify', [status(thm)], ['135'])).
% 0.38/0.57  thf('184', plain,
% 0.38/0.57      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['90', '91', '94', '95'])).
% 0.38/0.57  thf('185', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.38/0.57      inference('sup+', [status(thm)], ['12', '13'])).
% 0.38/0.57  thf('186', plain,
% 0.38/0.57      (![X22 : $i]:
% 0.38/0.57         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.57  thf('187', plain,
% 0.38/0.57      (![X22 : $i]:
% 0.38/0.57         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.57  thf('188', plain,
% 0.38/0.57      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.38/0.57          != (k2_struct_0 @ sk_B)))
% 0.38/0.57         <= (~
% 0.38/0.57             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.38/0.57                = (k2_struct_0 @ sk_B))))),
% 0.38/0.57      inference('split', [status(esa)], ['145'])).
% 0.38/0.57  thf('189', plain,
% 0.38/0.57      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.57           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.38/0.57           != (k2_struct_0 @ sk_B))
% 0.38/0.57         | ~ (l1_struct_0 @ sk_A)))
% 0.38/0.57         <= (~
% 0.38/0.57             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.38/0.57                = (k2_struct_0 @ sk_B))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['187', '188'])).
% 0.38/0.57  thf('190', plain, ((l1_struct_0 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('191', plain,
% 0.38/0.57      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.57          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.38/0.57          != (k2_struct_0 @ sk_B)))
% 0.38/0.57         <= (~
% 0.38/0.57             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.38/0.57                = (k2_struct_0 @ sk_B))))),
% 0.38/0.57      inference('demod', [status(thm)], ['189', '190'])).
% 0.38/0.57  thf('192', plain,
% 0.38/0.57      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.57           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.38/0.57           != (k2_struct_0 @ sk_B))
% 0.38/0.57         | ~ (l1_struct_0 @ sk_B)))
% 0.38/0.57         <= (~
% 0.38/0.57             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.38/0.57                = (k2_struct_0 @ sk_B))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['186', '191'])).
% 0.38/0.57  thf('193', plain, ((l1_struct_0 @ sk_B)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('194', plain,
% 0.38/0.57      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.57          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.38/0.57          != (k2_struct_0 @ sk_B)))
% 0.38/0.57         <= (~
% 0.38/0.57             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.38/0.57                = (k2_struct_0 @ sk_B))))),
% 0.38/0.57      inference('demod', [status(thm)], ['192', '193'])).
% 0.38/0.57  thf('195', plain,
% 0.38/0.57      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.57          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.38/0.57          != (k2_struct_0 @ sk_B)))
% 0.38/0.57         <= (~
% 0.38/0.57             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.38/0.57                = (k2_struct_0 @ sk_B))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['185', '194'])).
% 0.38/0.57  thf('196', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.38/0.57      inference('sup+', [status(thm)], ['12', '13'])).
% 0.38/0.57  thf('197', plain,
% 0.38/0.57      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.57          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.38/0.57          != (k2_relat_1 @ sk_C)))
% 0.38/0.57         <= (~
% 0.38/0.57             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.38/0.57                = (k2_struct_0 @ sk_B))))),
% 0.38/0.57      inference('demod', [status(thm)], ['195', '196'])).
% 0.38/0.57  thf('198', plain,
% 0.38/0.57      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.57          (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 0.38/0.57          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.38/0.57          != (k2_relat_1 @ sk_C)))
% 0.38/0.57         <= (~
% 0.38/0.57             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.38/0.57                = (k2_struct_0 @ sk_B))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['184', '197'])).
% 0.38/0.57  thf('199', plain,
% 0.38/0.57      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (u1_struct_0 @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['48', '51', '54', '69'])).
% 0.38/0.57  thf('200', plain,
% 0.38/0.57      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.57          (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 0.38/0.57          (k2_tops_2 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 0.38/0.57           (k2_relat_1 @ sk_C) @ sk_C))
% 0.38/0.57          != (k2_relat_1 @ sk_C)))
% 0.38/0.57         <= (~
% 0.38/0.57             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.38/0.57                = (k2_struct_0 @ sk_B))))),
% 0.38/0.57      inference('demod', [status(thm)], ['198', '199'])).
% 0.38/0.57  thf('201', plain,
% 0.38/0.57      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.57          (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ (k4_relat_1 @ sk_C))
% 0.38/0.57          != (k2_relat_1 @ sk_C)))
% 0.38/0.57         <= (~
% 0.38/0.57             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.38/0.57                = (k2_struct_0 @ sk_B))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['183', '200'])).
% 0.38/0.57  thf('202', plain,
% 0.38/0.57      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.38/0.57         <= (~
% 0.38/0.57             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.38/0.57                = (k2_struct_0 @ sk_B))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['182', '201'])).
% 0.38/0.57  thf('203', plain,
% 0.38/0.57      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.38/0.57          = (k2_struct_0 @ sk_B)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['202'])).
% 0.38/0.57  thf('204', plain,
% 0.38/0.57      (~
% 0.38/0.57       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.38/0.57          = (k2_struct_0 @ sk_A))) | 
% 0.38/0.57       ~
% 0.38/0.57       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.38/0.57          = (k2_struct_0 @ sk_B)))),
% 0.38/0.57      inference('split', [status(esa)], ['145'])).
% 0.38/0.57  thf('205', plain,
% 0.38/0.57      (~
% 0.38/0.57       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.57          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.38/0.57          = (k2_struct_0 @ sk_A)))),
% 0.38/0.57      inference('sat_resolution*', [status(thm)], ['203', '204'])).
% 0.38/0.57  thf('206', plain,
% 0.38/0.57      (((k1_relset_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 0.38/0.57         (k2_relat_1 @ sk_C) @ sk_C) != (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.38/0.57      inference('simpl_trail', [status(thm)], ['166', '205'])).
% 0.38/0.57  thf('207', plain, ($false),
% 0.38/0.57      inference('simplify_reflect-', [status(thm)], ['140', '206'])).
% 0.38/0.57  
% 0.38/0.57  % SZS output end Refutation
% 0.38/0.57  
% 0.38/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
