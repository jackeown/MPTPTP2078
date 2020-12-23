%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3yrJIF6D77

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:26 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 421 expanded)
%              Number of leaves         :   34 ( 140 expanded)
%              Depth                    :   20
%              Number of atoms          : 1533 (15340 expanded)
%              Number of equality atoms :   79 ( 661 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X4 ) @ X4 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(t65_tops_2,conjecture,(
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
               => ( ( ( k1_partfun1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ C @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                    = ( k6_partfun1 @ ( k1_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) )
                  & ( ( k1_partfun1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ C )
                    = ( k6_partfun1 @ ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
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
                 => ( ( ( k1_partfun1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ C @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                      = ( k6_partfun1 @ ( k1_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) )
                    & ( ( k1_partfun1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ C )
                      = ( k6_partfun1 @ ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_tops_2])).

thf('1',plain,
    ( ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k6_partfun1 @ ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) )
    | ( ( k1_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_C )
     != ( k6_partfun1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k1_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_C )
     != ( k6_partfun1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) )
   <= ( ( k1_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_C )
     != ( k6_partfun1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X17: $i] :
      ( ( k6_partfun1 @ X17 )
      = ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('5',plain,
    ( ( ( k1_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_C )
     != ( k6_relat_1 @ ( k2_struct_0 @ sk_B ) ) )
   <= ( ( k1_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_C )
     != ( k6_partfun1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('6',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('8',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X19 @ X21 )
       != X19 )
      | ~ ( v2_funct_1 @ X21 )
      | ( ( k2_tops_2 @ X20 @ X19 @ X21 )
        = ( k2_funct_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X20 @ X19 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('9',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('14',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('15',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10','11','12','15'])).

thf('17',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','16'])).

thf('18',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('19',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['17','20','21'])).

thf('23',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('25',plain,
    ( ( ( k1_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ sk_C ) @ sk_C )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
   <= ( ( k1_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_C )
     != ( k6_partfun1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['5','23','24'])).

thf('26',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ X4 @ ( k2_funct_1 @ X4 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) )
        & ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A )
        & ( m1_subset_1 @ ( k2_tops_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) )).

thf('28',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X22 @ X23 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('29',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['22'])).

thf('33',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('35',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( ( k1_partfun1 @ X12 @ X13 @ X15 @ X16 @ X11 @ X14 )
        = ( k5_relat_1 @ X11 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_funct_1 @ ( k2_tops_2 @ X22 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('42',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['22'])).

thf('46',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,
    ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['39','46'])).

thf('48',plain,
    ( ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k6_partfun1 @ ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) )
   <= ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k6_partfun1 @ ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf('49',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['22'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('51',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k1_relset_1 @ X6 @ X7 @ X5 )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('52',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X17: $i] :
      ( ( k6_partfun1 @ X17 )
      = ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('54',plain,
    ( ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_funct_1 @ sk_C ) )
     != ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
   <= ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k6_partfun1 @ ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['48','49','52','53'])).

thf('55',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
     != ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
   <= ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k6_partfun1 @ ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['47','54'])).

thf('56',plain,
    ( ( ( ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k6_partfun1 @ ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['26','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('60',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('61',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) )
     != ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
   <= ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k6_partfun1 @ ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['56','61','62','63'])).

thf('65',plain,
    ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k6_partfun1 @ ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( ( k1_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_C )
     != ( k6_partfun1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) )
    | ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k6_partfun1 @ ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf('67',plain,(
    ( k1_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_C )
 != ( k6_partfun1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['65','66'])).

thf('68',plain,(
    ( k1_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ sk_C ) @ sk_C )
 != ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['25','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('71',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( ( k1_partfun1 @ X12 @ X13 @ X15 @ X16 @ X11 @ X14 )
        = ( k5_relat_1 @ X11 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ X2 @ X1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ X2 @ X1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['69','74'])).

thf('76',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( k1_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
 != ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['68','77'])).

thf('79',plain,
    ( ( ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('81',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) )
 != ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('84',plain,(
    $false ),
    inference(simplify,[status(thm)],['83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3yrJIF6D77
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:42:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.60  % Solved by: fo/fo7.sh
% 0.37/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.60  % done 428 iterations in 0.139s
% 0.37/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.60  % SZS output start Refutation
% 0.37/0.60  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.37/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.60  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.37/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.60  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.37/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.60  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.37/0.60  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.37/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.60  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.37/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.37/0.60  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.37/0.60  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.37/0.60  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.37/0.60  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.37/0.60  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.37/0.60  thf(t61_funct_1, axiom,
% 0.37/0.60    (![A:$i]:
% 0.37/0.60     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.60       ( ( v2_funct_1 @ A ) =>
% 0.37/0.60         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.37/0.60             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.37/0.60           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.37/0.60             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.37/0.60  thf('0', plain,
% 0.37/0.60      (![X4 : $i]:
% 0.37/0.60         (~ (v2_funct_1 @ X4)
% 0.37/0.60          | ((k5_relat_1 @ (k2_funct_1 @ X4) @ X4)
% 0.37/0.60              = (k6_relat_1 @ (k2_relat_1 @ X4)))
% 0.37/0.60          | ~ (v1_funct_1 @ X4)
% 0.37/0.60          | ~ (v1_relat_1 @ X4))),
% 0.37/0.60      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.37/0.60  thf(t65_tops_2, conjecture,
% 0.37/0.60    (![A:$i]:
% 0.37/0.60     ( ( l1_struct_0 @ A ) =>
% 0.37/0.60       ( ![B:$i]:
% 0.37/0.60         ( ( l1_struct_0 @ B ) =>
% 0.37/0.60           ( ![C:$i]:
% 0.37/0.60             ( ( ( v1_funct_1 @ C ) & 
% 0.37/0.60                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.37/0.60                 ( m1_subset_1 @
% 0.37/0.60                   C @ 
% 0.37/0.60                   ( k1_zfmisc_1 @
% 0.37/0.60                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.37/0.60               ( ( ( ( k2_relset_1 @
% 0.37/0.60                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.37/0.60                     ( k2_struct_0 @ B ) ) & 
% 0.37/0.60                   ( v2_funct_1 @ C ) ) =>
% 0.37/0.60                 ( ( ( k1_partfun1 @
% 0.37/0.60                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.37/0.60                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ C @ 
% 0.37/0.60                       ( k2_tops_2 @
% 0.37/0.60                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.37/0.60                     ( k6_partfun1 @
% 0.37/0.60                       ( k1_relset_1 @
% 0.37/0.60                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) & 
% 0.37/0.60                   ( ( k1_partfun1 @
% 0.37/0.60                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.37/0.60                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.37/0.60                       ( k2_tops_2 @
% 0.37/0.60                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.37/0.60                       C ) =
% 0.37/0.60                     ( k6_partfun1 @
% 0.37/0.60                       ( k2_relset_1 @
% 0.37/0.60                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.60    (~( ![A:$i]:
% 0.37/0.60        ( ( l1_struct_0 @ A ) =>
% 0.37/0.60          ( ![B:$i]:
% 0.37/0.60            ( ( l1_struct_0 @ B ) =>
% 0.37/0.60              ( ![C:$i]:
% 0.37/0.60                ( ( ( v1_funct_1 @ C ) & 
% 0.37/0.60                    ( v1_funct_2 @
% 0.37/0.60                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.37/0.60                    ( m1_subset_1 @
% 0.37/0.60                      C @ 
% 0.37/0.60                      ( k1_zfmisc_1 @
% 0.37/0.60                        ( k2_zfmisc_1 @
% 0.37/0.60                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.37/0.60                  ( ( ( ( k2_relset_1 @
% 0.37/0.60                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.37/0.60                        ( k2_struct_0 @ B ) ) & 
% 0.37/0.60                      ( v2_funct_1 @ C ) ) =>
% 0.37/0.60                    ( ( ( k1_partfun1 @
% 0.37/0.60                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.37/0.60                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ C @ 
% 0.37/0.60                          ( k2_tops_2 @
% 0.37/0.60                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.37/0.60                        ( k6_partfun1 @
% 0.37/0.60                          ( k1_relset_1 @
% 0.37/0.60                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) & 
% 0.37/0.60                      ( ( k1_partfun1 @
% 0.37/0.60                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.37/0.60                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.37/0.60                          ( k2_tops_2 @
% 0.37/0.60                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.37/0.60                          C ) =
% 0.37/0.60                        ( k6_partfun1 @
% 0.37/0.60                          ( k2_relset_1 @
% 0.37/0.60                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) ) ) ) ) )),
% 0.37/0.60    inference('cnf.neg', [status(esa)], [t65_tops_2])).
% 0.37/0.60  thf('1', plain,
% 0.37/0.60      ((((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.60          (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.37/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.60          != (k6_partfun1 @ 
% 0.37/0.60              (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))
% 0.37/0.60        | ((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.60            (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.60            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.37/0.60            sk_C)
% 0.37/0.60            != (k6_partfun1 @ 
% 0.37/0.60                (k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.60                 sk_C))))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('2', plain,
% 0.37/0.60      ((((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.60          (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.37/0.60          sk_C)
% 0.37/0.60          != (k6_partfun1 @ 
% 0.37/0.60              (k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))))
% 0.37/0.60         <= (~
% 0.37/0.60             (((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.60                (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.37/0.60                sk_C)
% 0.37/0.60                = (k6_partfun1 @ 
% 0.37/0.60                   (k2_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.60                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.37/0.60      inference('split', [status(esa)], ['1'])).
% 0.37/0.60  thf('3', plain,
% 0.37/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.60         = (k2_struct_0 @ sk_B))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf(redefinition_k6_partfun1, axiom,
% 0.37/0.60    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.37/0.60  thf('4', plain, (![X17 : $i]: ((k6_partfun1 @ X17) = (k6_relat_1 @ X17))),
% 0.37/0.60      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.37/0.60  thf('5', plain,
% 0.37/0.60      ((((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.60          (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.37/0.60          sk_C) != (k6_relat_1 @ (k2_struct_0 @ sk_B))))
% 0.37/0.60         <= (~
% 0.37/0.60             (((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.60                (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.37/0.60                sk_C)
% 0.37/0.60                = (k6_partfun1 @ 
% 0.37/0.60                   (k2_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.60                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.37/0.60      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.37/0.60  thf(d3_struct_0, axiom,
% 0.37/0.60    (![A:$i]:
% 0.37/0.60     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.37/0.60  thf('6', plain,
% 0.37/0.60      (![X18 : $i]:
% 0.37/0.60         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.37/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.60  thf('7', plain,
% 0.37/0.60      ((m1_subset_1 @ sk_C @ 
% 0.37/0.60        (k1_zfmisc_1 @ 
% 0.37/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf(d4_tops_2, axiom,
% 0.37/0.60    (![A:$i,B:$i,C:$i]:
% 0.37/0.60     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.37/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.60       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.37/0.60         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.37/0.60  thf('8', plain,
% 0.37/0.60      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.37/0.60         (((k2_relset_1 @ X20 @ X19 @ X21) != (X19))
% 0.37/0.60          | ~ (v2_funct_1 @ X21)
% 0.37/0.60          | ((k2_tops_2 @ X20 @ X19 @ X21) = (k2_funct_1 @ X21))
% 0.37/0.60          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19)))
% 0.37/0.60          | ~ (v1_funct_2 @ X21 @ X20 @ X19)
% 0.37/0.60          | ~ (v1_funct_1 @ X21))),
% 0.37/0.60      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.37/0.60  thf('9', plain,
% 0.37/0.60      ((~ (v1_funct_1 @ sk_C)
% 0.37/0.60        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.37/0.60        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.60            = (k2_funct_1 @ sk_C))
% 0.37/0.60        | ~ (v2_funct_1 @ sk_C)
% 0.37/0.60        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.60            != (u1_struct_0 @ sk_B)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['7', '8'])).
% 0.37/0.60  thf('10', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('11', plain,
% 0.37/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('12', plain, ((v2_funct_1 @ sk_C)),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('13', plain,
% 0.37/0.60      ((m1_subset_1 @ sk_C @ 
% 0.37/0.60        (k1_zfmisc_1 @ 
% 0.37/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf(redefinition_k2_relset_1, axiom,
% 0.37/0.60    (![A:$i,B:$i,C:$i]:
% 0.37/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.60       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.37/0.60  thf('14', plain,
% 0.37/0.60      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.37/0.60         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 0.37/0.60          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.37/0.60      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.37/0.60  thf('15', plain,
% 0.37/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.60         = (k2_relat_1 @ sk_C))),
% 0.37/0.60      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.60  thf('16', plain,
% 0.37/0.60      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.60          = (k2_funct_1 @ sk_C))
% 0.37/0.60        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.37/0.60      inference('demod', [status(thm)], ['9', '10', '11', '12', '15'])).
% 0.37/0.60  thf('17', plain,
% 0.37/0.60      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.37/0.60        | ~ (l1_struct_0 @ sk_B)
% 0.37/0.60        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.60            = (k2_funct_1 @ sk_C)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['6', '16'])).
% 0.37/0.60  thf('18', plain,
% 0.37/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.60         = (k2_relat_1 @ sk_C))),
% 0.37/0.60      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.60  thf('19', plain,
% 0.37/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.60         = (k2_struct_0 @ sk_B))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('20', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.37/0.60      inference('sup+', [status(thm)], ['18', '19'])).
% 0.37/0.60  thf('21', plain, ((l1_struct_0 @ sk_B)),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('22', plain,
% 0.37/0.60      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.37/0.60        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.60            = (k2_funct_1 @ sk_C)))),
% 0.37/0.60      inference('demod', [status(thm)], ['17', '20', '21'])).
% 0.37/0.60  thf('23', plain,
% 0.37/0.60      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.60         = (k2_funct_1 @ sk_C))),
% 0.37/0.60      inference('simplify', [status(thm)], ['22'])).
% 0.37/0.60  thf('24', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.37/0.60      inference('sup+', [status(thm)], ['18', '19'])).
% 0.37/0.60  thf('25', plain,
% 0.37/0.60      ((((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.60          (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ (k2_funct_1 @ sk_C) @ 
% 0.37/0.60          sk_C) != (k6_relat_1 @ (k2_relat_1 @ sk_C))))
% 0.37/0.60         <= (~
% 0.37/0.60             (((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.60                (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.37/0.60                sk_C)
% 0.37/0.60                = (k6_partfun1 @ 
% 0.37/0.60                   (k2_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.60                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.37/0.60      inference('demod', [status(thm)], ['5', '23', '24'])).
% 0.37/0.60  thf('26', plain,
% 0.37/0.60      (![X4 : $i]:
% 0.37/0.60         (~ (v2_funct_1 @ X4)
% 0.37/0.60          | ((k5_relat_1 @ X4 @ (k2_funct_1 @ X4))
% 0.37/0.60              = (k6_relat_1 @ (k1_relat_1 @ X4)))
% 0.37/0.60          | ~ (v1_funct_1 @ X4)
% 0.37/0.60          | ~ (v1_relat_1 @ X4))),
% 0.37/0.60      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.37/0.60  thf('27', plain,
% 0.37/0.60      ((m1_subset_1 @ sk_C @ 
% 0.37/0.60        (k1_zfmisc_1 @ 
% 0.37/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf(dt_k2_tops_2, axiom,
% 0.37/0.60    (![A:$i,B:$i,C:$i]:
% 0.37/0.60     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.37/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.60       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 0.37/0.60         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 0.37/0.60         ( m1_subset_1 @
% 0.37/0.60           ( k2_tops_2 @ A @ B @ C ) @ 
% 0.37/0.60           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 0.37/0.60  thf('28', plain,
% 0.37/0.60      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.37/0.60         ((m1_subset_1 @ (k2_tops_2 @ X22 @ X23 @ X24) @ 
% 0.37/0.60           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.37/0.60          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.37/0.60          | ~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.37/0.60          | ~ (v1_funct_1 @ X24))),
% 0.37/0.60      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.37/0.60  thf('29', plain,
% 0.37/0.60      ((~ (v1_funct_1 @ sk_C)
% 0.37/0.60        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.37/0.60        | (m1_subset_1 @ 
% 0.37/0.60           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.37/0.60           (k1_zfmisc_1 @ 
% 0.37/0.60            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.37/0.60      inference('sup-', [status(thm)], ['27', '28'])).
% 0.37/0.60  thf('30', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('31', plain,
% 0.37/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('32', plain,
% 0.37/0.60      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.60         = (k2_funct_1 @ sk_C))),
% 0.37/0.60      inference('simplify', [status(thm)], ['22'])).
% 0.37/0.60  thf('33', plain,
% 0.37/0.60      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.37/0.60        (k1_zfmisc_1 @ 
% 0.37/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.37/0.60      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.37/0.60  thf('34', plain,
% 0.37/0.60      ((m1_subset_1 @ sk_C @ 
% 0.37/0.60        (k1_zfmisc_1 @ 
% 0.37/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf(redefinition_k1_partfun1, axiom,
% 0.37/0.60    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.37/0.60     ( ( ( v1_funct_1 @ E ) & 
% 0.37/0.60         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.37/0.60         ( v1_funct_1 @ F ) & 
% 0.37/0.60         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.37/0.60       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.37/0.60  thf('35', plain,
% 0.37/0.60      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.37/0.60         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.37/0.60          | ~ (v1_funct_1 @ X11)
% 0.37/0.60          | ~ (v1_funct_1 @ X14)
% 0.37/0.60          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.37/0.60          | ((k1_partfun1 @ X12 @ X13 @ X15 @ X16 @ X11 @ X14)
% 0.37/0.60              = (k5_relat_1 @ X11 @ X14)))),
% 0.37/0.60      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.37/0.60  thf('36', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.60         (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ X2 @ 
% 0.37/0.60            X1 @ sk_C @ X0) = (k5_relat_1 @ sk_C @ X0))
% 0.37/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.37/0.60          | ~ (v1_funct_1 @ X0)
% 0.37/0.60          | ~ (v1_funct_1 @ sk_C))),
% 0.37/0.60      inference('sup-', [status(thm)], ['34', '35'])).
% 0.37/0.60  thf('37', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('38', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.60         (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ X2 @ 
% 0.37/0.60            X1 @ sk_C @ X0) = (k5_relat_1 @ sk_C @ X0))
% 0.37/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.37/0.60          | ~ (v1_funct_1 @ X0))),
% 0.37/0.60      inference('demod', [status(thm)], ['36', '37'])).
% 0.37/0.60  thf('39', plain,
% 0.37/0.60      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.37/0.60        | ((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.60            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.37/0.60            (k2_funct_1 @ sk_C)) = (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))))),
% 0.37/0.60      inference('sup-', [status(thm)], ['33', '38'])).
% 0.37/0.60  thf('40', plain,
% 0.37/0.60      ((m1_subset_1 @ sk_C @ 
% 0.37/0.60        (k1_zfmisc_1 @ 
% 0.37/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('41', plain,
% 0.37/0.60      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.37/0.60         ((v1_funct_1 @ (k2_tops_2 @ X22 @ X23 @ X24))
% 0.37/0.60          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.37/0.60          | ~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.37/0.60          | ~ (v1_funct_1 @ X24))),
% 0.37/0.60      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.37/0.60  thf('42', plain,
% 0.37/0.60      ((~ (v1_funct_1 @ sk_C)
% 0.37/0.60        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.37/0.60        | (v1_funct_1 @ 
% 0.37/0.60           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['40', '41'])).
% 0.37/0.60  thf('43', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('44', plain,
% 0.37/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('45', plain,
% 0.37/0.60      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.60         = (k2_funct_1 @ sk_C))),
% 0.37/0.60      inference('simplify', [status(thm)], ['22'])).
% 0.37/0.60  thf('46', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.37/0.60      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 0.37/0.60  thf('47', plain,
% 0.37/0.60      (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.60         (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.37/0.60         (k2_funct_1 @ sk_C)) = (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))),
% 0.37/0.60      inference('demod', [status(thm)], ['39', '46'])).
% 0.37/0.60  thf('48', plain,
% 0.37/0.60      ((((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.60          (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.37/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.60          != (k6_partfun1 @ 
% 0.37/0.60              (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))))
% 0.37/0.60         <= (~
% 0.37/0.60             (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.60                (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.37/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.60                = (k6_partfun1 @ 
% 0.37/0.60                   (k1_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.60                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.37/0.60      inference('split', [status(esa)], ['1'])).
% 0.37/0.60  thf('49', plain,
% 0.37/0.60      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.60         = (k2_funct_1 @ sk_C))),
% 0.37/0.60      inference('simplify', [status(thm)], ['22'])).
% 0.37/0.60  thf('50', plain,
% 0.37/0.60      ((m1_subset_1 @ sk_C @ 
% 0.37/0.60        (k1_zfmisc_1 @ 
% 0.37/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf(redefinition_k1_relset_1, axiom,
% 0.37/0.60    (![A:$i,B:$i,C:$i]:
% 0.37/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.60       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.37/0.60  thf('51', plain,
% 0.37/0.60      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.37/0.60         (((k1_relset_1 @ X6 @ X7 @ X5) = (k1_relat_1 @ X5))
% 0.37/0.60          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.37/0.60      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.37/0.60  thf('52', plain,
% 0.37/0.60      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.60         = (k1_relat_1 @ sk_C))),
% 0.37/0.60      inference('sup-', [status(thm)], ['50', '51'])).
% 0.37/0.60  thf('53', plain, (![X17 : $i]: ((k6_partfun1 @ X17) = (k6_relat_1 @ X17))),
% 0.37/0.60      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.37/0.60  thf('54', plain,
% 0.37/0.60      ((((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.60          (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.37/0.60          (k2_funct_1 @ sk_C)) != (k6_relat_1 @ (k1_relat_1 @ sk_C))))
% 0.37/0.60         <= (~
% 0.37/0.60             (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.60                (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.37/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.60                = (k6_partfun1 @ 
% 0.37/0.60                   (k1_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.60                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.37/0.60      inference('demod', [status(thm)], ['48', '49', '52', '53'])).
% 0.37/0.60  thf('55', plain,
% 0.37/0.60      ((((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.37/0.60          != (k6_relat_1 @ (k1_relat_1 @ sk_C))))
% 0.37/0.60         <= (~
% 0.37/0.60             (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.60                (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.37/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.60                = (k6_partfun1 @ 
% 0.37/0.60                   (k1_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.60                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.37/0.60      inference('sup-', [status(thm)], ['47', '54'])).
% 0.37/0.60  thf('56', plain,
% 0.37/0.60      (((((k6_relat_1 @ (k1_relat_1 @ sk_C))
% 0.37/0.60           != (k6_relat_1 @ (k1_relat_1 @ sk_C)))
% 0.37/0.60         | ~ (v1_relat_1 @ sk_C)
% 0.37/0.60         | ~ (v1_funct_1 @ sk_C)
% 0.37/0.60         | ~ (v2_funct_1 @ sk_C)))
% 0.37/0.60         <= (~
% 0.37/0.60             (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.60                (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.37/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.60                = (k6_partfun1 @ 
% 0.37/0.60                   (k1_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.60                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.37/0.60      inference('sup-', [status(thm)], ['26', '55'])).
% 0.37/0.60  thf('57', plain,
% 0.37/0.60      ((m1_subset_1 @ sk_C @ 
% 0.37/0.60        (k1_zfmisc_1 @ 
% 0.37/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf(cc2_relat_1, axiom,
% 0.37/0.60    (![A:$i]:
% 0.37/0.60     ( ( v1_relat_1 @ A ) =>
% 0.37/0.60       ( ![B:$i]:
% 0.37/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.37/0.60  thf('58', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.37/0.60          | (v1_relat_1 @ X0)
% 0.37/0.60          | ~ (v1_relat_1 @ X1))),
% 0.37/0.60      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.37/0.60  thf('59', plain,
% 0.37/0.60      ((~ (v1_relat_1 @ 
% 0.37/0.60           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.37/0.60        | (v1_relat_1 @ sk_C))),
% 0.37/0.60      inference('sup-', [status(thm)], ['57', '58'])).
% 0.37/0.60  thf(fc6_relat_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.37/0.60  thf('60', plain,
% 0.37/0.60      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.37/0.60      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.37/0.60  thf('61', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.60      inference('demod', [status(thm)], ['59', '60'])).
% 0.37/0.60  thf('62', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('63', plain, ((v2_funct_1 @ sk_C)),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('64', plain,
% 0.37/0.60      ((((k6_relat_1 @ (k1_relat_1 @ sk_C))
% 0.37/0.60          != (k6_relat_1 @ (k1_relat_1 @ sk_C))))
% 0.37/0.60         <= (~
% 0.37/0.60             (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.60                (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.37/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.60                = (k6_partfun1 @ 
% 0.37/0.60                   (k1_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.60                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.37/0.60      inference('demod', [status(thm)], ['56', '61', '62', '63'])).
% 0.37/0.60  thf('65', plain,
% 0.37/0.60      ((((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.60          (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.37/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.60          = (k6_partfun1 @ 
% 0.37/0.60             (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))))),
% 0.37/0.60      inference('simplify', [status(thm)], ['64'])).
% 0.37/0.60  thf('66', plain,
% 0.37/0.60      (~
% 0.37/0.60       (((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.60          (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.37/0.60          sk_C)
% 0.37/0.60          = (k6_partfun1 @ 
% 0.37/0.60             (k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))) | 
% 0.37/0.60       ~
% 0.37/0.60       (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.60          (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.37/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.37/0.60          = (k6_partfun1 @ 
% 0.37/0.60             (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))))),
% 0.37/0.60      inference('split', [status(esa)], ['1'])).
% 0.37/0.60  thf('67', plain,
% 0.37/0.60      (~
% 0.37/0.60       (((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.60          (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.37/0.60          sk_C)
% 0.37/0.60          = (k6_partfun1 @ 
% 0.37/0.60             (k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))))),
% 0.37/0.60      inference('sat_resolution*', [status(thm)], ['65', '66'])).
% 0.37/0.60  thf('68', plain,
% 0.37/0.60      (((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.60         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ (k2_funct_1 @ sk_C) @ 
% 0.37/0.60         sk_C) != (k6_relat_1 @ (k2_relat_1 @ sk_C)))),
% 0.37/0.60      inference('simpl_trail', [status(thm)], ['25', '67'])).
% 0.37/0.60  thf('69', plain,
% 0.37/0.60      ((m1_subset_1 @ sk_C @ 
% 0.37/0.60        (k1_zfmisc_1 @ 
% 0.37/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('70', plain,
% 0.37/0.60      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.37/0.60        (k1_zfmisc_1 @ 
% 0.37/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.37/0.60      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.37/0.60  thf('71', plain,
% 0.37/0.60      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.37/0.60         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.37/0.60          | ~ (v1_funct_1 @ X11)
% 0.37/0.60          | ~ (v1_funct_1 @ X14)
% 0.37/0.60          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.37/0.60          | ((k1_partfun1 @ X12 @ X13 @ X15 @ X16 @ X11 @ X14)
% 0.37/0.60              = (k5_relat_1 @ X11 @ X14)))),
% 0.37/0.60      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.37/0.60  thf('72', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.60         (((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ X2 @ 
% 0.37/0.60            X1 @ (k2_funct_1 @ sk_C) @ X0)
% 0.37/0.60            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))
% 0.37/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.37/0.60          | ~ (v1_funct_1 @ X0)
% 0.37/0.60          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['70', '71'])).
% 0.37/0.60  thf('73', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.37/0.60      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 0.37/0.60  thf('74', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.60         (((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ X2 @ 
% 0.37/0.60            X1 @ (k2_funct_1 @ sk_C) @ X0)
% 0.37/0.60            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))
% 0.37/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.37/0.60          | ~ (v1_funct_1 @ X0))),
% 0.37/0.60      inference('demod', [status(thm)], ['72', '73'])).
% 0.37/0.60  thf('75', plain,
% 0.37/0.60      ((~ (v1_funct_1 @ sk_C)
% 0.37/0.60        | ((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.60            (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.60            (k2_funct_1 @ sk_C) @ sk_C)
% 0.37/0.60            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['69', '74'])).
% 0.37/0.60  thf('76', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('77', plain,
% 0.37/0.60      (((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.60         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ (k2_funct_1 @ sk_C) @ 
% 0.37/0.60         sk_C) = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))),
% 0.37/0.60      inference('demod', [status(thm)], ['75', '76'])).
% 0.37/0.60  thf('78', plain,
% 0.37/0.60      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.37/0.60         != (k6_relat_1 @ (k2_relat_1 @ sk_C)))),
% 0.37/0.60      inference('demod', [status(thm)], ['68', '77'])).
% 0.37/0.60  thf('79', plain,
% 0.37/0.60      ((((k6_relat_1 @ (k2_relat_1 @ sk_C))
% 0.37/0.60          != (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.37/0.60        | ~ (v1_relat_1 @ sk_C)
% 0.37/0.60        | ~ (v1_funct_1 @ sk_C)
% 0.37/0.60        | ~ (v2_funct_1 @ sk_C))),
% 0.37/0.60      inference('sup-', [status(thm)], ['0', '78'])).
% 0.37/0.60  thf('80', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.60      inference('demod', [status(thm)], ['59', '60'])).
% 0.37/0.60  thf('81', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('82', plain, ((v2_funct_1 @ sk_C)),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('83', plain,
% 0.37/0.60      (((k6_relat_1 @ (k2_relat_1 @ sk_C))
% 0.37/0.60         != (k6_relat_1 @ (k2_relat_1 @ sk_C)))),
% 0.37/0.60      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 0.37/0.60  thf('84', plain, ($false), inference('simplify', [status(thm)], ['83'])).
% 0.37/0.60  
% 0.37/0.60  % SZS output end Refutation
% 0.37/0.60  
% 0.37/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
