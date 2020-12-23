%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.b9IgCHi4cc

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:17 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  315 (3764 expanded)
%              Number of leaves         :   46 (1099 expanded)
%              Depth                    :   33
%              Number of atoms          : 2929 (78190 expanded)
%              Number of equality atoms :  149 (2211 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('0',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
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
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
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
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( v1_partfun1 @ X20 @ X21 )
      | ~ ( v1_funct_2 @ X20 @ X21 @ X22 )
      | ~ ( v1_funct_1 @ X20 )
      | ( v1_xboole_0 @ X22 ) ) ),
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
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
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

thf('31',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('32',plain,(
    ! [X33: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['30','34'])).

thf('36',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['29','39'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('41',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_partfun1 @ X24 @ X23 )
      | ( ( k1_relat_1 @ X24 )
        = X23 )
      | ~ ( v4_relat_1 @ X24 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('46',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('47',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('49',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v4_relat_1 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('50',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','47','50'])).

thf('52',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('53',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','47','50'])).

thf('54',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','47','50'])).

thf('55',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('56',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('57',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
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

thf('62',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['56','61'])).

thf('63',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('68',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['29','39'])).

thf('69',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_partfun1 @ X24 @ X23 )
      | ( ( k1_relat_1 @ X24 )
        = X23 )
      | ~ ( v4_relat_1 @ X24 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('73',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['45','46'])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('76',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v4_relat_1 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('77',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['73','74','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['66','78'])).

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

thf('80',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k2_relset_1 @ X35 @ X34 @ X36 )
       != X34 )
      | ~ ( v2_funct_1 @ X36 )
      | ( ( k2_tops_2 @ X35 @ X34 @ X36 )
        = ( k2_funct_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('81',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('84',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('85',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['83','88'])).

thf('90',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('93',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['73','74','77'])).

thf('95',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('98',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('99',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['97','102'])).

thf('104',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('107',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('108',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['73','74','77'])).

thf('110',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['81','82','95','96','110'])).

thf('112',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['9','51','52','53','54','55','112'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('114',plain,(
    ! [X10: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v2_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('115',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['66','78'])).

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

thf('116',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k2_relset_1 @ X31 @ X30 @ X29 )
       != X30 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('117',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('120',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('121',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['117','118','119','120','121'])).

thf('123',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k2_relset_1 @ X35 @ X34 @ X36 )
       != X34 )
      | ~ ( v2_funct_1 @ X36 )
      | ( ( k2_tops_2 @ X35 @ X34 @ X36 )
        = ( k2_funct_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('125',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('127',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('128',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['73','74','77'])).

thf('129',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k2_relset_1 @ X31 @ X30 @ X29 )
       != X30 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('131',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('134',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['73','74','77'])).

thf('135',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['131','132','135','136'])).

thf('138',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('139',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('140',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['73','74','77'])).

thf('142',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['137','142'])).

thf('144',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['126','143'])).

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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['66','78'])).

thf('150',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k2_relset_1 @ X31 @ X30 @ X29 )
       != X30 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X29 ) @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('151',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('154',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('155',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['151','152','153','154','155'])).

thf('157',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['125','148','157'])).

thf('159',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('160',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('161',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('163',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v4_relat_1 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('164',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('165',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7
        = ( k7_relat_1 @ X7 @ X8 ) )
      | ~ ( v4_relat_1 @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('166',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_funct_1 @ sk_C )
      = ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('169',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('171',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['169','170'])).

thf('172',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['166','171'])).

thf('173',plain,(
    ! [X10: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v2_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('174',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('175',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('176',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('177',plain,(
    ! [X10: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v2_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('178',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('179',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('180',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('181',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('182',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('183',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('184',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) )
        = ( k9_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) )
        = ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
        = ( k9_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['182','185'])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
        = ( k9_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['181','186'])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
        = ( k9_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['187'])).

thf('189',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
        = ( k9_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['180','188'])).

thf('190',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
        = ( k9_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['189'])).

thf('191',plain,(
    ! [X10: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v2_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('192',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('193',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('194',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(t154_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k9_relat_1 @ B @ A )
          = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('195',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k9_relat_1 @ X11 @ X12 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X11 ) @ X12 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['194','195'])).

thf('197',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['193','196'])).

thf('198',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['197'])).

thf('199',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['192','198'])).

thf('200',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['191','200'])).

thf('202',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['201'])).

thf('203',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k2_funct_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['190','202'])).

thf('204',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
        = ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['179','203'])).

thf('205',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
        = ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['204'])).

thf('206',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
        = ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['178','205'])).

thf('207',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
        = ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['206'])).

thf('208',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
        = ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['177','207'])).

thf('209',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
        = ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['208'])).

thf('210',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) )
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['176','209'])).

thf('211',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['175','210'])).

thf('212',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) )
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['211'])).

thf('213',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['174','212'])).

thf('214',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) )
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['213'])).

thf('215',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['173','214'])).

thf('216',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) )
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['215'])).

thf('217',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['172','216'])).

thf('218',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('219',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7
        = ( k7_relat_1 @ X7 @ X8 ) )
      | ~ ( v4_relat_1 @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('220',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['218','219'])).

thf('221',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['45','46'])).

thf('222',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['220','221'])).

thf('223',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) )
        = ( k9_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('224',plain,(
    ! [X6: $i] :
      ( ( ( k10_relat_1 @ X6 @ ( k2_relat_1 @ X6 ) )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('225',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['223','224'])).

thf('226',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) @ ( k9_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['222','225'])).

thf('227',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['45','46'])).

thf('228',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['45','46'])).

thf('229',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['220','221'])).

thf('230',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['220','221'])).

thf('231',plain,
    ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['226','227','228','229','230'])).

thf('232',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['220','221'])).

thf('233',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) )
        = ( k9_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('234',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['232','233'])).

thf('235',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['45','46'])).

thf('236',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['234','235'])).

thf('237',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['231','236'])).

thf('238',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['45','46'])).

thf('239',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['217','237','238','239','240'])).

thf('242',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['161','241'])).

thf('243',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['158','242'])).

thf('244',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['243'])).

thf('245',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['114','244'])).

thf('246',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['45','46'])).

thf('247',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['245','246','247','248'])).

thf('250',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['113','249'])).

thf('251',plain,
    ( ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','250'])).

thf('252',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['45','46'])).

thf('253',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['251','252','253','254'])).

thf('256',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('257',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf(reflexivity_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_funct_2 @ A @ B @ C @ C ) ) )).

thf('258',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( r2_funct_2 @ X25 @ X26 @ X27 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('259',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['257','258'])).

thf('260',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('262',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['259','260','261'])).

thf('263',plain,
    ( ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['256','262'])).

thf('264',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('266',plain,(
    r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['263','264','265'])).

thf('267',plain,(
    $false ),
    inference(demod,[status(thm)],['255','266'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.b9IgCHi4cc
% 0.14/0.33  % Computer   : n021.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:15:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.45/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.71  % Solved by: fo/fo7.sh
% 0.45/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.71  % done 552 iterations in 0.264s
% 0.45/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.71  % SZS output start Refutation
% 0.45/0.71  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.45/0.71  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.71  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.71  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.71  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.71  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.71  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.45/0.71  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.45/0.71  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.45/0.71  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.45/0.71  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.45/0.71  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.71  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.45/0.71  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.45/0.71  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.45/0.71  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.71  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.71  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.45/0.71  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.45/0.71  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.45/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.71  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.45/0.71  thf(t65_funct_1, axiom,
% 0.45/0.71    (![A:$i]:
% 0.45/0.71     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.71       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.45/0.71  thf('0', plain,
% 0.45/0.71      (![X13 : $i]:
% 0.45/0.71         (~ (v2_funct_1 @ X13)
% 0.45/0.71          | ((k2_funct_1 @ (k2_funct_1 @ X13)) = (X13))
% 0.45/0.71          | ~ (v1_funct_1 @ X13)
% 0.45/0.71          | ~ (v1_relat_1 @ X13))),
% 0.45/0.71      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.45/0.71  thf(d3_struct_0, axiom,
% 0.45/0.71    (![A:$i]:
% 0.45/0.71     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.45/0.71  thf('1', plain,
% 0.45/0.71      (![X32 : $i]:
% 0.45/0.71         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.45/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.71  thf('2', plain,
% 0.45/0.71      (![X32 : $i]:
% 0.45/0.71         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.45/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.71  thf(t64_tops_2, conjecture,
% 0.45/0.71    (![A:$i]:
% 0.45/0.71     ( ( l1_struct_0 @ A ) =>
% 0.45/0.71       ( ![B:$i]:
% 0.45/0.71         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.45/0.71           ( ![C:$i]:
% 0.45/0.71             ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.71                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.71                 ( m1_subset_1 @
% 0.45/0.71                   C @ 
% 0.45/0.71                   ( k1_zfmisc_1 @
% 0.45/0.71                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.71               ( ( ( ( k2_relset_1 @
% 0.45/0.71                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.45/0.71                     ( k2_struct_0 @ B ) ) & 
% 0.45/0.71                   ( v2_funct_1 @ C ) ) =>
% 0.45/0.71                 ( r2_funct_2 @
% 0.45/0.71                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.45/0.71                   ( k2_tops_2 @
% 0.45/0.71                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.45/0.71                     ( k2_tops_2 @
% 0.45/0.71                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.45/0.71                   C ) ) ) ) ) ) ))).
% 0.45/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.71    (~( ![A:$i]:
% 0.45/0.71        ( ( l1_struct_0 @ A ) =>
% 0.45/0.71          ( ![B:$i]:
% 0.45/0.71            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.45/0.71              ( ![C:$i]:
% 0.45/0.71                ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.71                    ( v1_funct_2 @
% 0.45/0.71                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.71                    ( m1_subset_1 @
% 0.45/0.71                      C @ 
% 0.45/0.71                      ( k1_zfmisc_1 @
% 0.45/0.71                        ( k2_zfmisc_1 @
% 0.45/0.71                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.71                  ( ( ( ( k2_relset_1 @
% 0.45/0.71                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.45/0.71                        ( k2_struct_0 @ B ) ) & 
% 0.45/0.71                      ( v2_funct_1 @ C ) ) =>
% 0.45/0.71                    ( r2_funct_2 @
% 0.45/0.71                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.45/0.71                      ( k2_tops_2 @
% 0.45/0.71                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.45/0.71                        ( k2_tops_2 @
% 0.45/0.71                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.45/0.71                      C ) ) ) ) ) ) ) )),
% 0.45/0.71    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.45/0.71  thf('3', plain,
% 0.45/0.71      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.71          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.71           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.71          sk_C)),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('4', plain,
% 0.45/0.71      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.71           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.71            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.71           sk_C)
% 0.45/0.71        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.71      inference('sup-', [status(thm)], ['2', '3'])).
% 0.45/0.71  thf('5', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('6', plain,
% 0.45/0.71      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.71          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.71           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.71          sk_C)),
% 0.45/0.71      inference('demod', [status(thm)], ['4', '5'])).
% 0.45/0.71  thf('7', plain,
% 0.45/0.71      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.71           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.71            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.71           sk_C)
% 0.45/0.71        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.71      inference('sup-', [status(thm)], ['1', '6'])).
% 0.45/0.71  thf('8', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('9', plain,
% 0.45/0.71      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.71          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.71           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.71          sk_C)),
% 0.45/0.71      inference('demod', [status(thm)], ['7', '8'])).
% 0.45/0.71  thf('10', plain,
% 0.45/0.71      (![X32 : $i]:
% 0.45/0.71         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.45/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.71  thf('11', plain,
% 0.45/0.71      ((m1_subset_1 @ sk_C @ 
% 0.45/0.71        (k1_zfmisc_1 @ 
% 0.45/0.71         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('12', plain,
% 0.45/0.71      (((m1_subset_1 @ sk_C @ 
% 0.45/0.71         (k1_zfmisc_1 @ 
% 0.45/0.71          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.45/0.71        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.71      inference('sup+', [status(thm)], ['10', '11'])).
% 0.45/0.71  thf('13', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('14', plain,
% 0.45/0.71      ((m1_subset_1 @ sk_C @ 
% 0.45/0.71        (k1_zfmisc_1 @ 
% 0.45/0.71         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.45/0.71      inference('demod', [status(thm)], ['12', '13'])).
% 0.45/0.71  thf(cc5_funct_2, axiom,
% 0.45/0.71    (![A:$i,B:$i]:
% 0.45/0.71     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.45/0.71       ( ![C:$i]:
% 0.45/0.71         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.71           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.45/0.71             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.45/0.71  thf('15', plain,
% 0.45/0.71      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.45/0.71         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.45/0.71          | (v1_partfun1 @ X20 @ X21)
% 0.45/0.71          | ~ (v1_funct_2 @ X20 @ X21 @ X22)
% 0.45/0.71          | ~ (v1_funct_1 @ X20)
% 0.45/0.71          | (v1_xboole_0 @ X22))),
% 0.45/0.71      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.45/0.71  thf('16', plain,
% 0.45/0.71      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.45/0.71        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.71        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.45/0.71        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.45/0.71      inference('sup-', [status(thm)], ['14', '15'])).
% 0.45/0.71  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('18', plain,
% 0.45/0.71      (![X32 : $i]:
% 0.45/0.71         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.45/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.71  thf('19', plain,
% 0.45/0.71      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('20', plain,
% 0.45/0.71      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.45/0.71        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.71      inference('sup+', [status(thm)], ['18', '19'])).
% 0.45/0.71  thf('21', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('22', plain,
% 0.45/0.71      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.45/0.71      inference('demod', [status(thm)], ['20', '21'])).
% 0.45/0.71  thf('23', plain,
% 0.45/0.71      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.45/0.71        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.45/0.71      inference('demod', [status(thm)], ['16', '17', '22'])).
% 0.45/0.71  thf('24', plain,
% 0.45/0.71      ((m1_subset_1 @ sk_C @ 
% 0.45/0.71        (k1_zfmisc_1 @ 
% 0.45/0.71         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf(redefinition_k2_relset_1, axiom,
% 0.45/0.71    (![A:$i,B:$i,C:$i]:
% 0.45/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.71       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.45/0.71  thf('25', plain,
% 0.45/0.71      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.45/0.71         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.45/0.71          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.45/0.71      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.71  thf('26', plain,
% 0.45/0.71      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.71         = (k2_relat_1 @ sk_C))),
% 0.45/0.71      inference('sup-', [status(thm)], ['24', '25'])).
% 0.45/0.71  thf('27', plain,
% 0.45/0.71      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.71         = (k2_struct_0 @ sk_B))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('28', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.71      inference('sup+', [status(thm)], ['26', '27'])).
% 0.45/0.71  thf('29', plain,
% 0.45/0.71      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.45/0.71        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.45/0.71      inference('demod', [status(thm)], ['23', '28'])).
% 0.45/0.71  thf('30', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.71      inference('sup+', [status(thm)], ['26', '27'])).
% 0.45/0.71  thf('31', plain,
% 0.45/0.71      (![X32 : $i]:
% 0.45/0.71         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.45/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.71  thf(fc2_struct_0, axiom,
% 0.45/0.71    (![A:$i]:
% 0.45/0.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.45/0.71       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.45/0.71  thf('32', plain,
% 0.45/0.71      (![X33 : $i]:
% 0.45/0.71         (~ (v1_xboole_0 @ (u1_struct_0 @ X33))
% 0.45/0.71          | ~ (l1_struct_0 @ X33)
% 0.45/0.71          | (v2_struct_0 @ X33))),
% 0.45/0.71      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.45/0.71  thf('33', plain,
% 0.45/0.71      (![X0 : $i]:
% 0.45/0.71         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.45/0.71          | ~ (l1_struct_0 @ X0)
% 0.45/0.71          | (v2_struct_0 @ X0)
% 0.45/0.71          | ~ (l1_struct_0 @ X0))),
% 0.45/0.71      inference('sup-', [status(thm)], ['31', '32'])).
% 0.45/0.71  thf('34', plain,
% 0.45/0.71      (![X0 : $i]:
% 0.45/0.71         ((v2_struct_0 @ X0)
% 0.45/0.71          | ~ (l1_struct_0 @ X0)
% 0.45/0.71          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.45/0.71      inference('simplify', [status(thm)], ['33'])).
% 0.45/0.71  thf('35', plain,
% 0.45/0.71      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.45/0.71        | ~ (l1_struct_0 @ sk_B)
% 0.45/0.71        | (v2_struct_0 @ sk_B))),
% 0.45/0.71      inference('sup-', [status(thm)], ['30', '34'])).
% 0.45/0.71  thf('36', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('37', plain,
% 0.45/0.71      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.45/0.71      inference('demod', [status(thm)], ['35', '36'])).
% 0.45/0.71  thf('38', plain, (~ (v2_struct_0 @ sk_B)),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('39', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.45/0.71      inference('clc', [status(thm)], ['37', '38'])).
% 0.45/0.71  thf('40', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.45/0.71      inference('clc', [status(thm)], ['29', '39'])).
% 0.45/0.71  thf(d4_partfun1, axiom,
% 0.45/0.71    (![A:$i,B:$i]:
% 0.45/0.71     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.45/0.71       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.45/0.71  thf('41', plain,
% 0.45/0.71      (![X23 : $i, X24 : $i]:
% 0.45/0.71         (~ (v1_partfun1 @ X24 @ X23)
% 0.45/0.71          | ((k1_relat_1 @ X24) = (X23))
% 0.45/0.71          | ~ (v4_relat_1 @ X24 @ X23)
% 0.45/0.71          | ~ (v1_relat_1 @ X24))),
% 0.45/0.71      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.45/0.71  thf('42', plain,
% 0.45/0.71      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.71        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.45/0.71        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.45/0.71      inference('sup-', [status(thm)], ['40', '41'])).
% 0.45/0.71  thf('43', plain,
% 0.45/0.71      ((m1_subset_1 @ sk_C @ 
% 0.45/0.71        (k1_zfmisc_1 @ 
% 0.45/0.71         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf(cc2_relat_1, axiom,
% 0.45/0.71    (![A:$i]:
% 0.45/0.71     ( ( v1_relat_1 @ A ) =>
% 0.45/0.71       ( ![B:$i]:
% 0.45/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.45/0.71  thf('44', plain,
% 0.45/0.71      (![X0 : $i, X1 : $i]:
% 0.45/0.71         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.45/0.71          | (v1_relat_1 @ X0)
% 0.45/0.71          | ~ (v1_relat_1 @ X1))),
% 0.45/0.71      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.45/0.71  thf('45', plain,
% 0.45/0.71      ((~ (v1_relat_1 @ 
% 0.45/0.71           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.45/0.71        | (v1_relat_1 @ sk_C))),
% 0.45/0.71      inference('sup-', [status(thm)], ['43', '44'])).
% 0.45/0.71  thf(fc6_relat_1, axiom,
% 0.45/0.71    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.45/0.71  thf('46', plain,
% 0.45/0.71      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.45/0.71      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.45/0.71  thf('47', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.71      inference('demod', [status(thm)], ['45', '46'])).
% 0.45/0.71  thf('48', plain,
% 0.45/0.71      ((m1_subset_1 @ sk_C @ 
% 0.45/0.71        (k1_zfmisc_1 @ 
% 0.45/0.71         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf(cc2_relset_1, axiom,
% 0.45/0.71    (![A:$i,B:$i,C:$i]:
% 0.45/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.71       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.45/0.71  thf('49', plain,
% 0.45/0.71      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.45/0.71         ((v4_relat_1 @ X14 @ X15)
% 0.45/0.71          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.45/0.71      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.71  thf('50', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.45/0.71      inference('sup-', [status(thm)], ['48', '49'])).
% 0.45/0.71  thf('51', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.45/0.71      inference('demod', [status(thm)], ['42', '47', '50'])).
% 0.45/0.71  thf('52', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.71      inference('sup+', [status(thm)], ['26', '27'])).
% 0.45/0.71  thf('53', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.45/0.71      inference('demod', [status(thm)], ['42', '47', '50'])).
% 0.45/0.71  thf('54', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.45/0.71      inference('demod', [status(thm)], ['42', '47', '50'])).
% 0.45/0.71  thf('55', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.71      inference('sup+', [status(thm)], ['26', '27'])).
% 0.45/0.71  thf('56', plain,
% 0.45/0.71      (![X32 : $i]:
% 0.45/0.71         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.45/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.71  thf('57', plain,
% 0.45/0.71      (![X32 : $i]:
% 0.45/0.71         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.45/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.71  thf('58', plain,
% 0.45/0.71      ((m1_subset_1 @ sk_C @ 
% 0.45/0.71        (k1_zfmisc_1 @ 
% 0.45/0.71         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('59', plain,
% 0.45/0.71      (((m1_subset_1 @ sk_C @ 
% 0.45/0.71         (k1_zfmisc_1 @ 
% 0.45/0.71          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.45/0.71        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.71      inference('sup+', [status(thm)], ['57', '58'])).
% 0.45/0.71  thf('60', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('61', plain,
% 0.45/0.71      ((m1_subset_1 @ sk_C @ 
% 0.45/0.71        (k1_zfmisc_1 @ 
% 0.45/0.71         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.71      inference('demod', [status(thm)], ['59', '60'])).
% 0.45/0.71  thf('62', plain,
% 0.45/0.71      (((m1_subset_1 @ sk_C @ 
% 0.45/0.71         (k1_zfmisc_1 @ 
% 0.45/0.71          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.45/0.72        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.72      inference('sup+', [status(thm)], ['56', '61'])).
% 0.45/0.72  thf('63', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('64', plain,
% 0.45/0.72      ((m1_subset_1 @ sk_C @ 
% 0.45/0.72        (k1_zfmisc_1 @ 
% 0.45/0.72         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.45/0.72      inference('demod', [status(thm)], ['62', '63'])).
% 0.45/0.72  thf('65', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.72      inference('sup+', [status(thm)], ['26', '27'])).
% 0.45/0.72  thf('66', plain,
% 0.45/0.72      ((m1_subset_1 @ sk_C @ 
% 0.45/0.72        (k1_zfmisc_1 @ 
% 0.45/0.72         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.45/0.72      inference('demod', [status(thm)], ['64', '65'])).
% 0.45/0.72  thf('67', plain,
% 0.45/0.72      (![X32 : $i]:
% 0.45/0.72         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.45/0.72      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.72  thf('68', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.45/0.72      inference('clc', [status(thm)], ['29', '39'])).
% 0.45/0.72  thf('69', plain,
% 0.45/0.72      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.72      inference('sup+', [status(thm)], ['67', '68'])).
% 0.45/0.72  thf('70', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('71', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.45/0.72      inference('demod', [status(thm)], ['69', '70'])).
% 0.45/0.72  thf('72', plain,
% 0.45/0.72      (![X23 : $i, X24 : $i]:
% 0.45/0.72         (~ (v1_partfun1 @ X24 @ X23)
% 0.45/0.72          | ((k1_relat_1 @ X24) = (X23))
% 0.45/0.72          | ~ (v4_relat_1 @ X24 @ X23)
% 0.45/0.72          | ~ (v1_relat_1 @ X24))),
% 0.45/0.72      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.45/0.72  thf('73', plain,
% 0.45/0.72      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.72        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.45/0.72        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.45/0.72      inference('sup-', [status(thm)], ['71', '72'])).
% 0.45/0.72  thf('74', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.72      inference('demod', [status(thm)], ['45', '46'])).
% 0.45/0.72  thf('75', plain,
% 0.45/0.72      ((m1_subset_1 @ sk_C @ 
% 0.45/0.72        (k1_zfmisc_1 @ 
% 0.45/0.72         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.72      inference('demod', [status(thm)], ['59', '60'])).
% 0.45/0.72  thf('76', plain,
% 0.45/0.72      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.45/0.72         ((v4_relat_1 @ X14 @ X15)
% 0.45/0.72          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.45/0.72      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.72  thf('77', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.45/0.72      inference('sup-', [status(thm)], ['75', '76'])).
% 0.45/0.72  thf('78', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.72      inference('demod', [status(thm)], ['73', '74', '77'])).
% 0.45/0.72  thf('79', plain,
% 0.45/0.72      ((m1_subset_1 @ sk_C @ 
% 0.45/0.72        (k1_zfmisc_1 @ 
% 0.45/0.72         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.45/0.72      inference('demod', [status(thm)], ['66', '78'])).
% 0.45/0.72  thf(d4_tops_2, axiom,
% 0.45/0.72    (![A:$i,B:$i,C:$i]:
% 0.45/0.72     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.72         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.72       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.45/0.72         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.45/0.72  thf('80', plain,
% 0.45/0.72      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.45/0.72         (((k2_relset_1 @ X35 @ X34 @ X36) != (X34))
% 0.45/0.72          | ~ (v2_funct_1 @ X36)
% 0.45/0.72          | ((k2_tops_2 @ X35 @ X34 @ X36) = (k2_funct_1 @ X36))
% 0.45/0.72          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 0.45/0.72          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 0.45/0.72          | ~ (v1_funct_1 @ X36))),
% 0.45/0.72      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.45/0.72  thf('81', plain,
% 0.45/0.72      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.72        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.45/0.72        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.72            = (k2_funct_1 @ sk_C))
% 0.45/0.72        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.72        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.72            != (k2_relat_1 @ sk_C)))),
% 0.45/0.72      inference('sup-', [status(thm)], ['79', '80'])).
% 0.45/0.72  thf('82', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('83', plain,
% 0.45/0.72      (![X32 : $i]:
% 0.45/0.72         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.45/0.72      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.72  thf('84', plain,
% 0.45/0.72      (![X32 : $i]:
% 0.45/0.72         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.45/0.72      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.72  thf('85', plain,
% 0.45/0.72      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('86', plain,
% 0.45/0.72      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.72        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.72      inference('sup+', [status(thm)], ['84', '85'])).
% 0.45/0.72  thf('87', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('88', plain,
% 0.45/0.72      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.72      inference('demod', [status(thm)], ['86', '87'])).
% 0.45/0.72  thf('89', plain,
% 0.45/0.72      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.45/0.72        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.72      inference('sup+', [status(thm)], ['83', '88'])).
% 0.45/0.72  thf('90', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('91', plain,
% 0.45/0.72      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.45/0.72      inference('demod', [status(thm)], ['89', '90'])).
% 0.45/0.72  thf('92', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.72      inference('sup+', [status(thm)], ['26', '27'])).
% 0.45/0.72  thf('93', plain,
% 0.45/0.72      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.45/0.72      inference('demod', [status(thm)], ['91', '92'])).
% 0.45/0.72  thf('94', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.72      inference('demod', [status(thm)], ['73', '74', '77'])).
% 0.45/0.72  thf('95', plain,
% 0.45/0.72      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.45/0.72      inference('demod', [status(thm)], ['93', '94'])).
% 0.45/0.72  thf('96', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('97', plain,
% 0.45/0.72      (![X32 : $i]:
% 0.45/0.72         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.45/0.72      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.72  thf('98', plain,
% 0.45/0.72      (![X32 : $i]:
% 0.45/0.72         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.45/0.72      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.72  thf('99', plain,
% 0.45/0.72      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.72         = (k2_struct_0 @ sk_B))),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('100', plain,
% 0.45/0.72      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.72          = (k2_struct_0 @ sk_B))
% 0.45/0.72        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.72      inference('sup+', [status(thm)], ['98', '99'])).
% 0.45/0.72  thf('101', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('102', plain,
% 0.45/0.72      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.72         = (k2_struct_0 @ sk_B))),
% 0.45/0.72      inference('demod', [status(thm)], ['100', '101'])).
% 0.45/0.72  thf('103', plain,
% 0.45/0.72      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.72          = (k2_struct_0 @ sk_B))
% 0.45/0.72        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.72      inference('sup+', [status(thm)], ['97', '102'])).
% 0.45/0.72  thf('104', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('105', plain,
% 0.45/0.72      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.72         = (k2_struct_0 @ sk_B))),
% 0.45/0.72      inference('demod', [status(thm)], ['103', '104'])).
% 0.45/0.72  thf('106', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.72      inference('sup+', [status(thm)], ['26', '27'])).
% 0.45/0.72  thf('107', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.72      inference('sup+', [status(thm)], ['26', '27'])).
% 0.45/0.72  thf('108', plain,
% 0.45/0.72      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.72         = (k2_relat_1 @ sk_C))),
% 0.45/0.72      inference('demod', [status(thm)], ['105', '106', '107'])).
% 0.45/0.72  thf('109', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.72      inference('demod', [status(thm)], ['73', '74', '77'])).
% 0.45/0.72  thf('110', plain,
% 0.45/0.72      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.72         = (k2_relat_1 @ sk_C))),
% 0.45/0.72      inference('demod', [status(thm)], ['108', '109'])).
% 0.45/0.72  thf('111', plain,
% 0.45/0.72      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.72          = (k2_funct_1 @ sk_C))
% 0.45/0.72        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.45/0.72      inference('demod', [status(thm)], ['81', '82', '95', '96', '110'])).
% 0.45/0.72  thf('112', plain,
% 0.45/0.72      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.72         = (k2_funct_1 @ sk_C))),
% 0.45/0.72      inference('simplify', [status(thm)], ['111'])).
% 0.45/0.72  thf('113', plain,
% 0.45/0.72      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.72          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.72           (k2_funct_1 @ sk_C)) @ 
% 0.45/0.72          sk_C)),
% 0.45/0.72      inference('demod', [status(thm)],
% 0.45/0.72                ['9', '51', '52', '53', '54', '55', '112'])).
% 0.45/0.72  thf(fc6_funct_1, axiom,
% 0.45/0.72    (![A:$i]:
% 0.45/0.72     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.45/0.72       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.45/0.72         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.45/0.72         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.45/0.72  thf('114', plain,
% 0.45/0.72      (![X10 : $i]:
% 0.45/0.72         ((v2_funct_1 @ (k2_funct_1 @ X10))
% 0.45/0.72          | ~ (v2_funct_1 @ X10)
% 0.45/0.72          | ~ (v1_funct_1 @ X10)
% 0.45/0.72          | ~ (v1_relat_1 @ X10))),
% 0.45/0.72      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.45/0.72  thf('115', plain,
% 0.45/0.72      ((m1_subset_1 @ sk_C @ 
% 0.45/0.72        (k1_zfmisc_1 @ 
% 0.45/0.72         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.45/0.72      inference('demod', [status(thm)], ['66', '78'])).
% 0.45/0.72  thf(t31_funct_2, axiom,
% 0.45/0.72    (![A:$i,B:$i,C:$i]:
% 0.45/0.72     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.72         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.72       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.45/0.72         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.45/0.72           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.45/0.72           ( m1_subset_1 @
% 0.45/0.72             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.45/0.72  thf('116', plain,
% 0.45/0.72      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.45/0.72         (~ (v2_funct_1 @ X29)
% 0.45/0.72          | ((k2_relset_1 @ X31 @ X30 @ X29) != (X30))
% 0.45/0.72          | (m1_subset_1 @ (k2_funct_1 @ X29) @ 
% 0.45/0.72             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.45/0.72          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 0.45/0.72          | ~ (v1_funct_2 @ X29 @ X31 @ X30)
% 0.45/0.72          | ~ (v1_funct_1 @ X29))),
% 0.45/0.72      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.45/0.72  thf('117', plain,
% 0.45/0.72      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.72        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.45/0.72        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.72           (k1_zfmisc_1 @ 
% 0.45/0.72            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.45/0.72        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.72            != (k2_relat_1 @ sk_C))
% 0.45/0.72        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.72      inference('sup-', [status(thm)], ['115', '116'])).
% 0.45/0.72  thf('118', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('119', plain,
% 0.45/0.72      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.45/0.72      inference('demod', [status(thm)], ['93', '94'])).
% 0.45/0.72  thf('120', plain,
% 0.45/0.72      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.72         = (k2_relat_1 @ sk_C))),
% 0.45/0.72      inference('demod', [status(thm)], ['108', '109'])).
% 0.45/0.72  thf('121', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('122', plain,
% 0.45/0.72      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.72         (k1_zfmisc_1 @ 
% 0.45/0.72          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.45/0.72        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.45/0.72      inference('demod', [status(thm)], ['117', '118', '119', '120', '121'])).
% 0.45/0.72  thf('123', plain,
% 0.45/0.72      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.72        (k1_zfmisc_1 @ 
% 0.45/0.72         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.45/0.72      inference('simplify', [status(thm)], ['122'])).
% 0.45/0.72  thf('124', plain,
% 0.45/0.72      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.45/0.72         (((k2_relset_1 @ X35 @ X34 @ X36) != (X34))
% 0.45/0.72          | ~ (v2_funct_1 @ X36)
% 0.45/0.72          | ((k2_tops_2 @ X35 @ X34 @ X36) = (k2_funct_1 @ X36))
% 0.45/0.72          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 0.45/0.72          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 0.45/0.72          | ~ (v1_funct_1 @ X36))),
% 0.45/0.72      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.45/0.72  thf('125', plain,
% 0.45/0.72      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.72        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.45/0.72             (k1_relat_1 @ sk_C))
% 0.45/0.72        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.72            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.72        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.72        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.72            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.45/0.72      inference('sup-', [status(thm)], ['123', '124'])).
% 0.45/0.72  thf('126', plain,
% 0.45/0.72      (![X32 : $i]:
% 0.45/0.72         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.45/0.72      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.72  thf('127', plain,
% 0.45/0.72      ((m1_subset_1 @ sk_C @ 
% 0.45/0.72        (k1_zfmisc_1 @ 
% 0.45/0.72         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.72      inference('demod', [status(thm)], ['59', '60'])).
% 0.45/0.72  thf('128', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.72      inference('demod', [status(thm)], ['73', '74', '77'])).
% 0.45/0.72  thf('129', plain,
% 0.45/0.72      ((m1_subset_1 @ sk_C @ 
% 0.45/0.72        (k1_zfmisc_1 @ 
% 0.45/0.72         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.72      inference('demod', [status(thm)], ['127', '128'])).
% 0.45/0.72  thf('130', plain,
% 0.45/0.72      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.45/0.72         (~ (v2_funct_1 @ X29)
% 0.45/0.72          | ((k2_relset_1 @ X31 @ X30 @ X29) != (X30))
% 0.45/0.72          | (v1_funct_1 @ (k2_funct_1 @ X29))
% 0.45/0.72          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 0.45/0.72          | ~ (v1_funct_2 @ X29 @ X31 @ X30)
% 0.45/0.72          | ~ (v1_funct_1 @ X29))),
% 0.45/0.72      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.45/0.72  thf('131', plain,
% 0.45/0.72      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.72        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.45/0.72        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.72        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.72            != (u1_struct_0 @ sk_B))
% 0.45/0.72        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.72      inference('sup-', [status(thm)], ['129', '130'])).
% 0.45/0.72  thf('132', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('133', plain,
% 0.45/0.72      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.72      inference('demod', [status(thm)], ['86', '87'])).
% 0.45/0.72  thf('134', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.72      inference('demod', [status(thm)], ['73', '74', '77'])).
% 0.45/0.72  thf('135', plain,
% 0.45/0.72      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.45/0.72      inference('demod', [status(thm)], ['133', '134'])).
% 0.45/0.72  thf('136', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('137', plain,
% 0.45/0.72      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.72        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.72            != (u1_struct_0 @ sk_B)))),
% 0.45/0.72      inference('demod', [status(thm)], ['131', '132', '135', '136'])).
% 0.45/0.72  thf('138', plain,
% 0.45/0.72      ((m1_subset_1 @ sk_C @ 
% 0.45/0.72        (k1_zfmisc_1 @ 
% 0.45/0.72         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.72      inference('demod', [status(thm)], ['59', '60'])).
% 0.45/0.72  thf('139', plain,
% 0.45/0.72      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.45/0.72         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.45/0.72          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.45/0.72      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.72  thf('140', plain,
% 0.45/0.72      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.72         = (k2_relat_1 @ sk_C))),
% 0.45/0.72      inference('sup-', [status(thm)], ['138', '139'])).
% 0.45/0.72  thf('141', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.72      inference('demod', [status(thm)], ['73', '74', '77'])).
% 0.45/0.72  thf('142', plain,
% 0.45/0.72      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.72         = (k2_relat_1 @ sk_C))),
% 0.45/0.72      inference('demod', [status(thm)], ['140', '141'])).
% 0.45/0.72  thf('143', plain,
% 0.45/0.72      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.72        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.45/0.72      inference('demod', [status(thm)], ['137', '142'])).
% 0.45/0.72  thf('144', plain,
% 0.45/0.72      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.45/0.72        | ~ (l1_struct_0 @ sk_B)
% 0.45/0.72        | (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.72      inference('sup-', [status(thm)], ['126', '143'])).
% 0.45/0.72  thf('145', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.72      inference('sup+', [status(thm)], ['26', '27'])).
% 0.45/0.72  thf('146', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('147', plain,
% 0.45/0.72      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.45/0.72        | (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.72      inference('demod', [status(thm)], ['144', '145', '146'])).
% 0.45/0.72  thf('148', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.72      inference('simplify', [status(thm)], ['147'])).
% 0.45/0.72  thf('149', plain,
% 0.45/0.72      ((m1_subset_1 @ sk_C @ 
% 0.45/0.72        (k1_zfmisc_1 @ 
% 0.45/0.72         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.45/0.72      inference('demod', [status(thm)], ['66', '78'])).
% 0.45/0.72  thf('150', plain,
% 0.45/0.72      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.45/0.72         (~ (v2_funct_1 @ X29)
% 0.45/0.72          | ((k2_relset_1 @ X31 @ X30 @ X29) != (X30))
% 0.45/0.72          | (v1_funct_2 @ (k2_funct_1 @ X29) @ X30 @ X31)
% 0.45/0.72          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 0.45/0.72          | ~ (v1_funct_2 @ X29 @ X31 @ X30)
% 0.45/0.72          | ~ (v1_funct_1 @ X29))),
% 0.45/0.72      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.45/0.72  thf('151', plain,
% 0.45/0.72      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.72        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.45/0.72        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.45/0.72           (k1_relat_1 @ sk_C))
% 0.45/0.72        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.72            != (k2_relat_1 @ sk_C))
% 0.45/0.72        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.72      inference('sup-', [status(thm)], ['149', '150'])).
% 0.45/0.72  thf('152', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('153', plain,
% 0.45/0.72      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.45/0.72      inference('demod', [status(thm)], ['93', '94'])).
% 0.45/0.72  thf('154', plain,
% 0.45/0.72      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.72         = (k2_relat_1 @ sk_C))),
% 0.45/0.72      inference('demod', [status(thm)], ['108', '109'])).
% 0.45/0.72  thf('155', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('156', plain,
% 0.45/0.72      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.45/0.72         (k1_relat_1 @ sk_C))
% 0.45/0.72        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.45/0.72      inference('demod', [status(thm)], ['151', '152', '153', '154', '155'])).
% 0.45/0.72  thf('157', plain,
% 0.45/0.72      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.45/0.72        (k1_relat_1 @ sk_C))),
% 0.45/0.72      inference('simplify', [status(thm)], ['156'])).
% 0.45/0.72  thf('158', plain,
% 0.45/0.72      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.72          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.72        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.72        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.72            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.45/0.72      inference('demod', [status(thm)], ['125', '148', '157'])).
% 0.45/0.72  thf('159', plain,
% 0.45/0.72      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.72        (k1_zfmisc_1 @ 
% 0.45/0.72         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.45/0.72      inference('simplify', [status(thm)], ['122'])).
% 0.45/0.72  thf('160', plain,
% 0.45/0.72      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.45/0.72         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.45/0.72          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.45/0.72      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.72  thf('161', plain,
% 0.45/0.72      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.72         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.72      inference('sup-', [status(thm)], ['159', '160'])).
% 0.45/0.72  thf('162', plain,
% 0.45/0.72      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.72        (k1_zfmisc_1 @ 
% 0.45/0.72         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.45/0.72      inference('simplify', [status(thm)], ['122'])).
% 0.45/0.72  thf('163', plain,
% 0.45/0.72      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.45/0.72         ((v4_relat_1 @ X14 @ X15)
% 0.45/0.72          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.45/0.72      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.72  thf('164', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.45/0.72      inference('sup-', [status(thm)], ['162', '163'])).
% 0.45/0.72  thf(t209_relat_1, axiom,
% 0.45/0.72    (![A:$i,B:$i]:
% 0.45/0.72     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.45/0.72       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.45/0.72  thf('165', plain,
% 0.45/0.72      (![X7 : $i, X8 : $i]:
% 0.45/0.72         (((X7) = (k7_relat_1 @ X7 @ X8))
% 0.45/0.72          | ~ (v4_relat_1 @ X7 @ X8)
% 0.45/0.72          | ~ (v1_relat_1 @ X7))),
% 0.45/0.72      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.45/0.72  thf('166', plain,
% 0.45/0.72      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.72        | ((k2_funct_1 @ sk_C)
% 0.45/0.72            = (k7_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.45/0.72      inference('sup-', [status(thm)], ['164', '165'])).
% 0.45/0.72  thf('167', plain,
% 0.45/0.72      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.72        (k1_zfmisc_1 @ 
% 0.45/0.72         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.45/0.72      inference('simplify', [status(thm)], ['122'])).
% 0.45/0.72  thf('168', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.45/0.72          | (v1_relat_1 @ X0)
% 0.45/0.72          | ~ (v1_relat_1 @ X1))),
% 0.45/0.72      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.45/0.72  thf('169', plain,
% 0.45/0.72      ((~ (v1_relat_1 @ 
% 0.45/0.72           (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C)))
% 0.45/0.72        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.72      inference('sup-', [status(thm)], ['167', '168'])).
% 0.45/0.72  thf('170', plain,
% 0.45/0.72      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.45/0.72      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.45/0.72  thf('171', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.72      inference('demod', [status(thm)], ['169', '170'])).
% 0.45/0.72  thf('172', plain,
% 0.45/0.72      (((k2_funct_1 @ sk_C)
% 0.45/0.72         = (k7_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C)))),
% 0.45/0.72      inference('demod', [status(thm)], ['166', '171'])).
% 0.45/0.72  thf('173', plain,
% 0.45/0.72      (![X10 : $i]:
% 0.45/0.72         ((v2_funct_1 @ (k2_funct_1 @ X10))
% 0.45/0.72          | ~ (v2_funct_1 @ X10)
% 0.45/0.72          | ~ (v1_funct_1 @ X10)
% 0.45/0.72          | ~ (v1_relat_1 @ X10))),
% 0.45/0.72      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.45/0.72  thf(dt_k2_funct_1, axiom,
% 0.45/0.72    (![A:$i]:
% 0.45/0.72     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.72       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.45/0.72         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.45/0.72  thf('174', plain,
% 0.45/0.72      (![X9 : $i]:
% 0.45/0.72         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 0.45/0.72          | ~ (v1_funct_1 @ X9)
% 0.45/0.72          | ~ (v1_relat_1 @ X9))),
% 0.45/0.72      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.45/0.72  thf('175', plain,
% 0.45/0.72      (![X9 : $i]:
% 0.45/0.72         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 0.45/0.72          | ~ (v1_funct_1 @ X9)
% 0.45/0.72          | ~ (v1_relat_1 @ X9))),
% 0.45/0.72      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.45/0.72  thf('176', plain,
% 0.45/0.72      (![X13 : $i]:
% 0.45/0.72         (~ (v2_funct_1 @ X13)
% 0.45/0.72          | ((k2_funct_1 @ (k2_funct_1 @ X13)) = (X13))
% 0.45/0.72          | ~ (v1_funct_1 @ X13)
% 0.45/0.72          | ~ (v1_relat_1 @ X13))),
% 0.45/0.72      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.45/0.72  thf('177', plain,
% 0.45/0.72      (![X10 : $i]:
% 0.45/0.72         ((v2_funct_1 @ (k2_funct_1 @ X10))
% 0.45/0.72          | ~ (v2_funct_1 @ X10)
% 0.45/0.72          | ~ (v1_funct_1 @ X10)
% 0.45/0.72          | ~ (v1_relat_1 @ X10))),
% 0.45/0.72      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.45/0.72  thf('178', plain,
% 0.45/0.72      (![X9 : $i]:
% 0.45/0.72         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 0.45/0.72          | ~ (v1_funct_1 @ X9)
% 0.45/0.72          | ~ (v1_relat_1 @ X9))),
% 0.45/0.72      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.45/0.72  thf('179', plain,
% 0.45/0.72      (![X9 : $i]:
% 0.45/0.72         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 0.45/0.72          | ~ (v1_funct_1 @ X9)
% 0.45/0.72          | ~ (v1_relat_1 @ X9))),
% 0.45/0.72      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.45/0.72  thf('180', plain,
% 0.45/0.72      (![X9 : $i]:
% 0.45/0.72         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 0.45/0.72          | ~ (v1_funct_1 @ X9)
% 0.45/0.72          | ~ (v1_relat_1 @ X9))),
% 0.45/0.72      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.45/0.72  thf('181', plain,
% 0.45/0.72      (![X9 : $i]:
% 0.45/0.72         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 0.45/0.72          | ~ (v1_funct_1 @ X9)
% 0.45/0.72          | ~ (v1_relat_1 @ X9))),
% 0.45/0.72      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.45/0.72  thf('182', plain,
% 0.45/0.72      (![X13 : $i]:
% 0.45/0.72         (~ (v2_funct_1 @ X13)
% 0.45/0.72          | ((k2_funct_1 @ (k2_funct_1 @ X13)) = (X13))
% 0.45/0.72          | ~ (v1_funct_1 @ X13)
% 0.45/0.72          | ~ (v1_relat_1 @ X13))),
% 0.45/0.72      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.45/0.72  thf('183', plain,
% 0.45/0.72      (![X9 : $i]:
% 0.45/0.72         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 0.45/0.72          | ~ (v1_funct_1 @ X9)
% 0.45/0.72          | ~ (v1_relat_1 @ X9))),
% 0.45/0.72      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.45/0.72  thf(t148_relat_1, axiom,
% 0.45/0.72    (![A:$i,B:$i]:
% 0.45/0.72     ( ( v1_relat_1 @ B ) =>
% 0.45/0.72       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.45/0.72  thf('184', plain,
% 0.45/0.72      (![X4 : $i, X5 : $i]:
% 0.45/0.72         (((k2_relat_1 @ (k7_relat_1 @ X4 @ X5)) = (k9_relat_1 @ X4 @ X5))
% 0.45/0.72          | ~ (v1_relat_1 @ X4))),
% 0.45/0.72      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.45/0.72  thf('185', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         (~ (v1_relat_1 @ X0)
% 0.45/0.72          | ~ (v1_funct_1 @ X0)
% 0.45/0.72          | ((k2_relat_1 @ (k7_relat_1 @ (k2_funct_1 @ X0) @ X1))
% 0.45/0.72              = (k9_relat_1 @ (k2_funct_1 @ X0) @ X1)))),
% 0.45/0.72      inference('sup-', [status(thm)], ['183', '184'])).
% 0.45/0.72  thf('186', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         (((k2_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.45/0.72            = (k9_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ X1))
% 0.45/0.72          | ~ (v1_relat_1 @ X0)
% 0.45/0.72          | ~ (v1_funct_1 @ X0)
% 0.45/0.72          | ~ (v2_funct_1 @ X0)
% 0.45/0.72          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.72          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.45/0.72      inference('sup+', [status(thm)], ['182', '185'])).
% 0.45/0.72  thf('187', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         (~ (v1_relat_1 @ X0)
% 0.45/0.72          | ~ (v1_funct_1 @ X0)
% 0.45/0.72          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.72          | ~ (v2_funct_1 @ X0)
% 0.45/0.72          | ~ (v1_funct_1 @ X0)
% 0.45/0.72          | ~ (v1_relat_1 @ X0)
% 0.45/0.72          | ((k2_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.45/0.72              = (k9_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ X1)))),
% 0.45/0.72      inference('sup-', [status(thm)], ['181', '186'])).
% 0.45/0.72  thf('188', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         (((k2_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.45/0.72            = (k9_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ X1))
% 0.45/0.72          | ~ (v2_funct_1 @ X0)
% 0.45/0.72          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.72          | ~ (v1_funct_1 @ X0)
% 0.45/0.72          | ~ (v1_relat_1 @ X0))),
% 0.45/0.72      inference('simplify', [status(thm)], ['187'])).
% 0.45/0.72  thf('189', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         (~ (v1_relat_1 @ X0)
% 0.45/0.72          | ~ (v1_funct_1 @ X0)
% 0.45/0.72          | ~ (v1_relat_1 @ X0)
% 0.45/0.72          | ~ (v1_funct_1 @ X0)
% 0.45/0.72          | ~ (v2_funct_1 @ X0)
% 0.45/0.72          | ((k2_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.45/0.72              = (k9_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ X1)))),
% 0.45/0.72      inference('sup-', [status(thm)], ['180', '188'])).
% 0.45/0.72  thf('190', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         (((k2_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.45/0.72            = (k9_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ X1))
% 0.45/0.72          | ~ (v2_funct_1 @ X0)
% 0.45/0.72          | ~ (v1_funct_1 @ X0)
% 0.45/0.72          | ~ (v1_relat_1 @ X0))),
% 0.45/0.72      inference('simplify', [status(thm)], ['189'])).
% 0.45/0.72  thf('191', plain,
% 0.45/0.72      (![X10 : $i]:
% 0.45/0.72         ((v2_funct_1 @ (k2_funct_1 @ X10))
% 0.45/0.72          | ~ (v2_funct_1 @ X10)
% 0.45/0.72          | ~ (v1_funct_1 @ X10)
% 0.45/0.72          | ~ (v1_relat_1 @ X10))),
% 0.45/0.72      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.45/0.72  thf('192', plain,
% 0.45/0.72      (![X9 : $i]:
% 0.45/0.72         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 0.45/0.72          | ~ (v1_funct_1 @ X9)
% 0.45/0.72          | ~ (v1_relat_1 @ X9))),
% 0.45/0.72      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.45/0.72  thf('193', plain,
% 0.45/0.72      (![X9 : $i]:
% 0.45/0.72         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 0.45/0.72          | ~ (v1_funct_1 @ X9)
% 0.45/0.72          | ~ (v1_relat_1 @ X9))),
% 0.45/0.72      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.45/0.72  thf('194', plain,
% 0.45/0.72      (![X13 : $i]:
% 0.45/0.72         (~ (v2_funct_1 @ X13)
% 0.45/0.72          | ((k2_funct_1 @ (k2_funct_1 @ X13)) = (X13))
% 0.45/0.72          | ~ (v1_funct_1 @ X13)
% 0.45/0.72          | ~ (v1_relat_1 @ X13))),
% 0.45/0.72      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.45/0.72  thf(t154_funct_1, axiom,
% 0.45/0.72    (![A:$i,B:$i]:
% 0.45/0.72     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.45/0.72       ( ( v2_funct_1 @ B ) =>
% 0.45/0.72         ( ( k9_relat_1 @ B @ A ) = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.45/0.72  thf('195', plain,
% 0.45/0.72      (![X11 : $i, X12 : $i]:
% 0.45/0.72         (~ (v2_funct_1 @ X11)
% 0.45/0.72          | ((k9_relat_1 @ X11 @ X12)
% 0.45/0.72              = (k10_relat_1 @ (k2_funct_1 @ X11) @ X12))
% 0.45/0.72          | ~ (v1_funct_1 @ X11)
% 0.45/0.72          | ~ (v1_relat_1 @ X11))),
% 0.45/0.72      inference('cnf', [status(esa)], [t154_funct_1])).
% 0.45/0.72  thf('196', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         (((k9_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k10_relat_1 @ X0 @ X1))
% 0.45/0.72          | ~ (v1_relat_1 @ X0)
% 0.45/0.72          | ~ (v1_funct_1 @ X0)
% 0.45/0.72          | ~ (v2_funct_1 @ X0)
% 0.45/0.72          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.72          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.72          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.45/0.72      inference('sup+', [status(thm)], ['194', '195'])).
% 0.45/0.72  thf('197', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         (~ (v1_relat_1 @ X0)
% 0.45/0.72          | ~ (v1_funct_1 @ X0)
% 0.45/0.72          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.72          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.72          | ~ (v2_funct_1 @ X0)
% 0.45/0.72          | ~ (v1_funct_1 @ X0)
% 0.45/0.72          | ~ (v1_relat_1 @ X0)
% 0.45/0.72          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k10_relat_1 @ X0 @ X1)))),
% 0.45/0.72      inference('sup-', [status(thm)], ['193', '196'])).
% 0.45/0.72  thf('198', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         (((k9_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k10_relat_1 @ X0 @ X1))
% 0.45/0.72          | ~ (v2_funct_1 @ X0)
% 0.45/0.72          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.72          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.72          | ~ (v1_funct_1 @ X0)
% 0.45/0.72          | ~ (v1_relat_1 @ X0))),
% 0.45/0.72      inference('simplify', [status(thm)], ['197'])).
% 0.45/0.72  thf('199', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         (~ (v1_relat_1 @ X0)
% 0.45/0.72          | ~ (v1_funct_1 @ X0)
% 0.45/0.72          | ~ (v1_relat_1 @ X0)
% 0.45/0.72          | ~ (v1_funct_1 @ X0)
% 0.45/0.72          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.72          | ~ (v2_funct_1 @ X0)
% 0.45/0.72          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k10_relat_1 @ X0 @ X1)))),
% 0.45/0.72      inference('sup-', [status(thm)], ['192', '198'])).
% 0.45/0.72  thf('200', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         (((k9_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k10_relat_1 @ X0 @ X1))
% 0.45/0.72          | ~ (v2_funct_1 @ X0)
% 0.45/0.72          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.72          | ~ (v1_funct_1 @ X0)
% 0.45/0.72          | ~ (v1_relat_1 @ X0))),
% 0.45/0.72      inference('simplify', [status(thm)], ['199'])).
% 0.45/0.72  thf('201', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         (~ (v1_relat_1 @ X0)
% 0.45/0.72          | ~ (v1_funct_1 @ X0)
% 0.45/0.72          | ~ (v2_funct_1 @ X0)
% 0.45/0.72          | ~ (v1_relat_1 @ X0)
% 0.45/0.72          | ~ (v1_funct_1 @ X0)
% 0.45/0.72          | ~ (v2_funct_1 @ X0)
% 0.45/0.72          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k10_relat_1 @ X0 @ X1)))),
% 0.45/0.72      inference('sup-', [status(thm)], ['191', '200'])).
% 0.45/0.72  thf('202', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         (((k9_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k10_relat_1 @ X0 @ X1))
% 0.45/0.72          | ~ (v2_funct_1 @ X0)
% 0.45/0.72          | ~ (v1_funct_1 @ X0)
% 0.45/0.72          | ~ (v1_relat_1 @ X0))),
% 0.45/0.72      inference('simplify', [status(thm)], ['201'])).
% 0.45/0.72  thf('203', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         (((k2_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.45/0.72            = (k10_relat_1 @ (k2_funct_1 @ X1) @ X0))
% 0.45/0.72          | ~ (v1_relat_1 @ X1)
% 0.45/0.72          | ~ (v1_funct_1 @ X1)
% 0.45/0.72          | ~ (v2_funct_1 @ X1)
% 0.45/0.72          | ~ (v1_relat_1 @ (k2_funct_1 @ X1))
% 0.45/0.72          | ~ (v1_funct_1 @ (k2_funct_1 @ X1))
% 0.45/0.72          | ~ (v2_funct_1 @ (k2_funct_1 @ X1)))),
% 0.45/0.72      inference('sup+', [status(thm)], ['190', '202'])).
% 0.45/0.72  thf('204', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         (~ (v1_relat_1 @ X0)
% 0.45/0.72          | ~ (v1_funct_1 @ X0)
% 0.45/0.72          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.72          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.72          | ~ (v2_funct_1 @ X0)
% 0.45/0.72          | ~ (v1_funct_1 @ X0)
% 0.45/0.72          | ~ (v1_relat_1 @ X0)
% 0.45/0.72          | ((k2_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.45/0.72              = (k10_relat_1 @ (k2_funct_1 @ X0) @ X1)))),
% 0.45/0.72      inference('sup-', [status(thm)], ['179', '203'])).
% 0.45/0.72  thf('205', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         (((k2_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.45/0.72            = (k10_relat_1 @ (k2_funct_1 @ X0) @ X1))
% 0.45/0.72          | ~ (v2_funct_1 @ X0)
% 0.45/0.72          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.72          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.72          | ~ (v1_funct_1 @ X0)
% 0.45/0.72          | ~ (v1_relat_1 @ X0))),
% 0.45/0.72      inference('simplify', [status(thm)], ['204'])).
% 0.45/0.72  thf('206', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         (~ (v1_relat_1 @ X0)
% 0.45/0.72          | ~ (v1_funct_1 @ X0)
% 0.45/0.72          | ~ (v1_relat_1 @ X0)
% 0.45/0.72          | ~ (v1_funct_1 @ X0)
% 0.45/0.72          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.72          | ~ (v2_funct_1 @ X0)
% 0.45/0.72          | ((k2_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.45/0.72              = (k10_relat_1 @ (k2_funct_1 @ X0) @ X1)))),
% 0.45/0.72      inference('sup-', [status(thm)], ['178', '205'])).
% 0.45/0.72  thf('207', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         (((k2_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.45/0.72            = (k10_relat_1 @ (k2_funct_1 @ X0) @ X1))
% 0.45/0.72          | ~ (v2_funct_1 @ X0)
% 0.45/0.72          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.72          | ~ (v1_funct_1 @ X0)
% 0.45/0.72          | ~ (v1_relat_1 @ X0))),
% 0.45/0.72      inference('simplify', [status(thm)], ['206'])).
% 0.45/0.72  thf('208', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         (~ (v1_relat_1 @ X0)
% 0.45/0.72          | ~ (v1_funct_1 @ X0)
% 0.45/0.72          | ~ (v2_funct_1 @ X0)
% 0.45/0.72          | ~ (v1_relat_1 @ X0)
% 0.45/0.72          | ~ (v1_funct_1 @ X0)
% 0.45/0.72          | ~ (v2_funct_1 @ X0)
% 0.45/0.72          | ((k2_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.45/0.72              = (k10_relat_1 @ (k2_funct_1 @ X0) @ X1)))),
% 0.45/0.72      inference('sup-', [status(thm)], ['177', '207'])).
% 0.45/0.72  thf('209', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         (((k2_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.45/0.72            = (k10_relat_1 @ (k2_funct_1 @ X0) @ X1))
% 0.45/0.72          | ~ (v2_funct_1 @ X0)
% 0.45/0.72          | ~ (v1_funct_1 @ X0)
% 0.45/0.72          | ~ (v1_relat_1 @ X0))),
% 0.45/0.72      inference('simplify', [status(thm)], ['208'])).
% 0.45/0.72  thf('210', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         (((k2_relat_1 @ (k7_relat_1 @ (k2_funct_1 @ X0) @ X1))
% 0.45/0.72            = (k10_relat_1 @ X0 @ X1))
% 0.45/0.72          | ~ (v1_relat_1 @ X0)
% 0.45/0.72          | ~ (v1_funct_1 @ X0)
% 0.45/0.72          | ~ (v2_funct_1 @ X0)
% 0.45/0.72          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.72          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.72          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.45/0.72      inference('sup+', [status(thm)], ['176', '209'])).
% 0.45/0.72  thf('211', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         (~ (v1_relat_1 @ X0)
% 0.45/0.72          | ~ (v1_funct_1 @ X0)
% 0.45/0.72          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.72          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.72          | ~ (v2_funct_1 @ X0)
% 0.45/0.72          | ~ (v1_funct_1 @ X0)
% 0.45/0.72          | ~ (v1_relat_1 @ X0)
% 0.45/0.72          | ((k2_relat_1 @ (k7_relat_1 @ (k2_funct_1 @ X0) @ X1))
% 0.45/0.72              = (k10_relat_1 @ X0 @ X1)))),
% 0.45/0.72      inference('sup-', [status(thm)], ['175', '210'])).
% 0.45/0.72  thf('212', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         (((k2_relat_1 @ (k7_relat_1 @ (k2_funct_1 @ X0) @ X1))
% 0.45/0.72            = (k10_relat_1 @ X0 @ X1))
% 0.45/0.72          | ~ (v2_funct_1 @ X0)
% 0.45/0.72          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.72          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.72          | ~ (v1_funct_1 @ X0)
% 0.45/0.72          | ~ (v1_relat_1 @ X0))),
% 0.45/0.72      inference('simplify', [status(thm)], ['211'])).
% 0.45/0.72  thf('213', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         (~ (v1_relat_1 @ X0)
% 0.45/0.72          | ~ (v1_funct_1 @ X0)
% 0.45/0.72          | ~ (v1_relat_1 @ X0)
% 0.45/0.72          | ~ (v1_funct_1 @ X0)
% 0.45/0.72          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.72          | ~ (v2_funct_1 @ X0)
% 0.45/0.72          | ((k2_relat_1 @ (k7_relat_1 @ (k2_funct_1 @ X0) @ X1))
% 0.45/0.72              = (k10_relat_1 @ X0 @ X1)))),
% 0.45/0.72      inference('sup-', [status(thm)], ['174', '212'])).
% 0.45/0.72  thf('214', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         (((k2_relat_1 @ (k7_relat_1 @ (k2_funct_1 @ X0) @ X1))
% 0.45/0.72            = (k10_relat_1 @ X0 @ X1))
% 0.45/0.72          | ~ (v2_funct_1 @ X0)
% 0.45/0.72          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.72          | ~ (v1_funct_1 @ X0)
% 0.45/0.72          | ~ (v1_relat_1 @ X0))),
% 0.45/0.72      inference('simplify', [status(thm)], ['213'])).
% 0.45/0.72  thf('215', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         (~ (v1_relat_1 @ X0)
% 0.45/0.72          | ~ (v1_funct_1 @ X0)
% 0.45/0.72          | ~ (v2_funct_1 @ X0)
% 0.45/0.72          | ~ (v1_relat_1 @ X0)
% 0.45/0.72          | ~ (v1_funct_1 @ X0)
% 0.45/0.72          | ~ (v2_funct_1 @ X0)
% 0.45/0.72          | ((k2_relat_1 @ (k7_relat_1 @ (k2_funct_1 @ X0) @ X1))
% 0.45/0.72              = (k10_relat_1 @ X0 @ X1)))),
% 0.45/0.72      inference('sup-', [status(thm)], ['173', '214'])).
% 0.45/0.72  thf('216', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         (((k2_relat_1 @ (k7_relat_1 @ (k2_funct_1 @ X0) @ X1))
% 0.45/0.72            = (k10_relat_1 @ X0 @ X1))
% 0.45/0.72          | ~ (v2_funct_1 @ X0)
% 0.45/0.72          | ~ (v1_funct_1 @ X0)
% 0.45/0.72          | ~ (v1_relat_1 @ X0))),
% 0.45/0.72      inference('simplify', [status(thm)], ['215'])).
% 0.45/0.72  thf('217', plain,
% 0.45/0.72      ((((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.72          = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))
% 0.45/0.72        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.72        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.72        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.72      inference('sup+', [status(thm)], ['172', '216'])).
% 0.45/0.72  thf('218', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.45/0.72      inference('sup-', [status(thm)], ['48', '49'])).
% 0.45/0.72  thf('219', plain,
% 0.45/0.72      (![X7 : $i, X8 : $i]:
% 0.45/0.72         (((X7) = (k7_relat_1 @ X7 @ X8))
% 0.45/0.72          | ~ (v4_relat_1 @ X7 @ X8)
% 0.45/0.72          | ~ (v1_relat_1 @ X7))),
% 0.45/0.72      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.45/0.72  thf('220', plain,
% 0.45/0.72      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.72        | ((sk_C) = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))))),
% 0.45/0.72      inference('sup-', [status(thm)], ['218', '219'])).
% 0.45/0.72  thf('221', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.72      inference('demod', [status(thm)], ['45', '46'])).
% 0.45/0.72  thf('222', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.45/0.72      inference('demod', [status(thm)], ['220', '221'])).
% 0.45/0.72  thf('223', plain,
% 0.45/0.72      (![X4 : $i, X5 : $i]:
% 0.45/0.72         (((k2_relat_1 @ (k7_relat_1 @ X4 @ X5)) = (k9_relat_1 @ X4 @ X5))
% 0.45/0.72          | ~ (v1_relat_1 @ X4))),
% 0.45/0.72      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.45/0.72  thf(t169_relat_1, axiom,
% 0.45/0.72    (![A:$i]:
% 0.45/0.72     ( ( v1_relat_1 @ A ) =>
% 0.45/0.72       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.45/0.72  thf('224', plain,
% 0.45/0.72      (![X6 : $i]:
% 0.45/0.72         (((k10_relat_1 @ X6 @ (k2_relat_1 @ X6)) = (k1_relat_1 @ X6))
% 0.45/0.72          | ~ (v1_relat_1 @ X6))),
% 0.45/0.72      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.45/0.72  thf('225', plain,
% 0.45/0.72      (![X0 : $i, X1 : $i]:
% 0.45/0.72         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.45/0.72            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.45/0.72          | ~ (v1_relat_1 @ X1)
% 0.45/0.72          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.45/0.72      inference('sup+', [status(thm)], ['223', '224'])).
% 0.45/0.72  thf('226', plain,
% 0.45/0.72      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.72        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.72        | ((k10_relat_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.72            (k9_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)))
% 0.45/0.72            = (k1_relat_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.72      inference('sup-', [status(thm)], ['222', '225'])).
% 0.45/0.72  thf('227', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.72      inference('demod', [status(thm)], ['45', '46'])).
% 0.45/0.72  thf('228', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.72      inference('demod', [status(thm)], ['45', '46'])).
% 0.45/0.72  thf('229', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.45/0.72      inference('demod', [status(thm)], ['220', '221'])).
% 0.45/0.72  thf('230', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.45/0.72      inference('demod', [status(thm)], ['220', '221'])).
% 0.45/0.72  thf('231', plain,
% 0.45/0.72      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)))
% 0.45/0.72         = (k1_relat_1 @ sk_C))),
% 0.45/0.72      inference('demod', [status(thm)], ['226', '227', '228', '229', '230'])).
% 0.45/0.72  thf('232', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.45/0.72      inference('demod', [status(thm)], ['220', '221'])).
% 0.45/0.72  thf('233', plain,
% 0.45/0.72      (![X4 : $i, X5 : $i]:
% 0.45/0.72         (((k2_relat_1 @ (k7_relat_1 @ X4 @ X5)) = (k9_relat_1 @ X4 @ X5))
% 0.45/0.72          | ~ (v1_relat_1 @ X4))),
% 0.45/0.72      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.45/0.72  thf('234', plain,
% 0.45/0.72      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)))
% 0.45/0.72        | ~ (v1_relat_1 @ sk_C))),
% 0.45/0.72      inference('sup+', [status(thm)], ['232', '233'])).
% 0.45/0.72  thf('235', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.72      inference('demod', [status(thm)], ['45', '46'])).
% 0.45/0.72  thf('236', plain,
% 0.45/0.72      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.45/0.72      inference('demod', [status(thm)], ['234', '235'])).
% 0.45/0.72  thf('237', plain,
% 0.45/0.72      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.45/0.72      inference('demod', [status(thm)], ['231', '236'])).
% 0.45/0.72  thf('238', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.72      inference('demod', [status(thm)], ['45', '46'])).
% 0.45/0.72  thf('239', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('240', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('241', plain,
% 0.45/0.72      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.45/0.72      inference('demod', [status(thm)], ['217', '237', '238', '239', '240'])).
% 0.45/0.72  thf('242', plain,
% 0.45/0.72      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.72         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.45/0.72      inference('demod', [status(thm)], ['161', '241'])).
% 0.45/0.72  thf('243', plain,
% 0.45/0.72      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.72          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.72        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.72        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))),
% 0.45/0.72      inference('demod', [status(thm)], ['158', '242'])).
% 0.45/0.72  thf('244', plain,
% 0.45/0.72      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.72        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.72            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.72      inference('simplify', [status(thm)], ['243'])).
% 0.45/0.72  thf('245', plain,
% 0.45/0.72      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.72        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.72        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.72        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.72            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.72      inference('sup-', [status(thm)], ['114', '244'])).
% 0.45/0.72  thf('246', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.72      inference('demod', [status(thm)], ['45', '46'])).
% 0.45/0.72  thf('247', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('248', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('249', plain,
% 0.45/0.72      (((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.72         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.72      inference('demod', [status(thm)], ['245', '246', '247', '248'])).
% 0.45/0.72  thf('250', plain,
% 0.45/0.72      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.72          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 0.45/0.72      inference('demod', [status(thm)], ['113', '249'])).
% 0.45/0.72  thf('251', plain,
% 0.45/0.72      ((~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.45/0.72           sk_C)
% 0.45/0.72        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.72        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.72        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.72      inference('sup-', [status(thm)], ['0', '250'])).
% 0.45/0.72  thf('252', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.72      inference('demod', [status(thm)], ['45', '46'])).
% 0.45/0.72  thf('253', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('254', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('255', plain,
% 0.45/0.72      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.45/0.72      inference('demod', [status(thm)], ['251', '252', '253', '254'])).
% 0.45/0.72  thf('256', plain,
% 0.45/0.72      ((m1_subset_1 @ sk_C @ 
% 0.45/0.72        (k1_zfmisc_1 @ 
% 0.45/0.72         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.72      inference('demod', [status(thm)], ['127', '128'])).
% 0.45/0.72  thf('257', plain,
% 0.45/0.72      ((m1_subset_1 @ sk_C @ 
% 0.45/0.72        (k1_zfmisc_1 @ 
% 0.45/0.72         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.72      inference('demod', [status(thm)], ['127', '128'])).
% 0.45/0.72  thf(reflexivity_r2_funct_2, axiom,
% 0.45/0.72    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.72     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.72         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.45/0.72         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.45/0.72         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.72       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.45/0.72  thf('258', plain,
% 0.45/0.72      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.45/0.72         ((r2_funct_2 @ X25 @ X26 @ X27 @ X27)
% 0.45/0.72          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.45/0.72          | ~ (v1_funct_2 @ X27 @ X25 @ X26)
% 0.45/0.72          | ~ (v1_funct_1 @ X27)
% 0.45/0.72          | ~ (v1_funct_1 @ X28)
% 0.45/0.72          | ~ (v1_funct_2 @ X28 @ X25 @ X26)
% 0.45/0.72          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.45/0.72      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.45/0.72  thf('259', plain,
% 0.45/0.72      (![X0 : $i]:
% 0.45/0.72         (~ (m1_subset_1 @ X0 @ 
% 0.45/0.72             (k1_zfmisc_1 @ 
% 0.45/0.72              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.45/0.72          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.45/0.72          | ~ (v1_funct_1 @ X0)
% 0.45/0.72          | ~ (v1_funct_1 @ sk_C)
% 0.45/0.72          | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.45/0.72          | (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.45/0.72             sk_C))),
% 0.45/0.72      inference('sup-', [status(thm)], ['257', '258'])).
% 0.45/0.72  thf('260', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('261', plain,
% 0.45/0.72      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.45/0.72      inference('demod', [status(thm)], ['133', '134'])).
% 0.45/0.72  thf('262', plain,
% 0.45/0.72      (![X0 : $i]:
% 0.45/0.72         (~ (m1_subset_1 @ X0 @ 
% 0.45/0.72             (k1_zfmisc_1 @ 
% 0.45/0.72              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.45/0.72          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.45/0.72          | ~ (v1_funct_1 @ X0)
% 0.45/0.72          | (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.45/0.72             sk_C))),
% 0.45/0.72      inference('demod', [status(thm)], ['259', '260', '261'])).
% 0.45/0.72  thf('263', plain,
% 0.45/0.72      (((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 0.45/0.72        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.72        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.45/0.72      inference('sup-', [status(thm)], ['256', '262'])).
% 0.45/0.72  thf('264', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.72  thf('265', plain,
% 0.45/0.72      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.45/0.72      inference('demod', [status(thm)], ['133', '134'])).
% 0.45/0.72  thf('266', plain,
% 0.45/0.72      ((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.45/0.72      inference('demod', [status(thm)], ['263', '264', '265'])).
% 0.45/0.72  thf('267', plain, ($false), inference('demod', [status(thm)], ['255', '266'])).
% 0.45/0.72  
% 0.45/0.72  % SZS output end Refutation
% 0.45/0.72  
% 0.58/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
