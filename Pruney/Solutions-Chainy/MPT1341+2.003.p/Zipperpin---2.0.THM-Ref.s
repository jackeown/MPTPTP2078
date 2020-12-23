%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hyy92SUhQG

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:26 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 415 expanded)
%              Number of leaves         :   33 ( 138 expanded)
%              Depth                    :   20
%              Number of atoms          : 1517 (15308 expanded)
%              Number of equality atoms :   79 ( 661 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

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
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
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
    ! [X16: $i] :
      ( ( k6_partfun1 @ X16 )
      = ( k6_relat_1 @ X16 ) ) ),
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
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X18 @ X20 )
       != X18 )
      | ~ ( v2_funct_1 @ X20 )
      | ( ( k2_tops_2 @ X19 @ X18 @ X20 )
        = ( k2_funct_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X18 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X19 @ X18 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_relset_1 @ X8 @ X9 @ X7 )
        = ( k2_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
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
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X21 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ~ ( v1_funct_1 @ X23 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( ( k1_partfun1 @ X11 @ X12 @ X14 @ X15 @ X10 @ X13 )
        = ( k5_relat_1 @ X10 @ X13 ) ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_funct_1 @ ( k2_tops_2 @ X21 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ~ ( v1_funct_1 @ X23 ) ) ),
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
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k1_relset_1 @ X5 @ X6 @ X4 )
        = ( k1_relat_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('52',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X16: $i] :
      ( ( k6_partfun1 @ X16 )
      = ( k6_relat_1 @ X16 ) ) ),
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

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('58',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('59',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) )
     != ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
   <= ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k6_partfun1 @ ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['56','59','60','61'])).

thf('63',plain,
    ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k6_partfun1 @ ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( ( k1_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_C )
     != ( k6_partfun1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) )
    | ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k6_partfun1 @ ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf('65',plain,(
    ( k1_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_C )
 != ( k6_partfun1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['63','64'])).

thf('66',plain,(
    ( k1_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ sk_C ) @ sk_C )
 != ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['25','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('69',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( ( k1_partfun1 @ X11 @ X12 @ X14 @ X15 @ X10 @ X13 )
        = ( k5_relat_1 @ X10 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ X2 @ X1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ X2 @ X1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['67','72'])).

thf('74',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( k1_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
 != ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['66','75'])).

thf('77',plain,
    ( ( ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['57','58'])).

thf('79',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) )
 != ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['77','78','79','80'])).

thf('82',plain,(
    $false ),
    inference(simplify,[status(thm)],['81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hyy92SUhQG
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:36:09 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.57  % Solved by: fo/fo7.sh
% 0.19/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.57  % done 449 iterations in 0.124s
% 0.19/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.57  % SZS output start Refutation
% 0.19/0.57  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.19/0.57  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.19/0.57  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.19/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.57  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.19/0.57  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.19/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.57  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.57  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.19/0.57  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.19/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.57  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.19/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.57  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.19/0.57  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.19/0.57  thf(t61_funct_1, axiom,
% 0.19/0.57    (![A:$i]:
% 0.19/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.57       ( ( v2_funct_1 @ A ) =>
% 0.19/0.57         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.19/0.57             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.19/0.57           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.19/0.57             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.19/0.57  thf('0', plain,
% 0.19/0.57      (![X0 : $i]:
% 0.19/0.57         (~ (v2_funct_1 @ X0)
% 0.19/0.57          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.19/0.57              = (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.19/0.57          | ~ (v1_funct_1 @ X0)
% 0.19/0.57          | ~ (v1_relat_1 @ X0))),
% 0.19/0.57      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.19/0.57  thf(t65_tops_2, conjecture,
% 0.19/0.57    (![A:$i]:
% 0.19/0.57     ( ( l1_struct_0 @ A ) =>
% 0.19/0.57       ( ![B:$i]:
% 0.19/0.57         ( ( l1_struct_0 @ B ) =>
% 0.19/0.57           ( ![C:$i]:
% 0.19/0.57             ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.57                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.57                 ( m1_subset_1 @
% 0.19/0.57                   C @ 
% 0.19/0.57                   ( k1_zfmisc_1 @
% 0.19/0.57                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.57               ( ( ( ( k2_relset_1 @
% 0.19/0.57                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.19/0.57                     ( k2_struct_0 @ B ) ) & 
% 0.19/0.57                   ( v2_funct_1 @ C ) ) =>
% 0.19/0.57                 ( ( ( k1_partfun1 @
% 0.19/0.57                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.19/0.57                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ C @ 
% 0.19/0.57                       ( k2_tops_2 @
% 0.19/0.57                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.19/0.57                     ( k6_partfun1 @
% 0.19/0.57                       ( k1_relset_1 @
% 0.19/0.57                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) & 
% 0.19/0.57                   ( ( k1_partfun1 @
% 0.19/0.57                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.19/0.57                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.19/0.57                       ( k2_tops_2 @
% 0.19/0.57                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.19/0.57                       C ) =
% 0.19/0.57                     ( k6_partfun1 @
% 0.19/0.57                       ( k2_relset_1 @
% 0.19/0.57                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.57    (~( ![A:$i]:
% 0.19/0.57        ( ( l1_struct_0 @ A ) =>
% 0.19/0.57          ( ![B:$i]:
% 0.19/0.57            ( ( l1_struct_0 @ B ) =>
% 0.19/0.57              ( ![C:$i]:
% 0.19/0.57                ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.57                    ( v1_funct_2 @
% 0.19/0.57                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.57                    ( m1_subset_1 @
% 0.19/0.57                      C @ 
% 0.19/0.57                      ( k1_zfmisc_1 @
% 0.19/0.57                        ( k2_zfmisc_1 @
% 0.19/0.57                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.57                  ( ( ( ( k2_relset_1 @
% 0.19/0.57                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.19/0.57                        ( k2_struct_0 @ B ) ) & 
% 0.19/0.57                      ( v2_funct_1 @ C ) ) =>
% 0.19/0.57                    ( ( ( k1_partfun1 @
% 0.19/0.57                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.19/0.57                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ C @ 
% 0.19/0.57                          ( k2_tops_2 @
% 0.19/0.57                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.19/0.57                        ( k6_partfun1 @
% 0.19/0.57                          ( k1_relset_1 @
% 0.19/0.57                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) & 
% 0.19/0.57                      ( ( k1_partfun1 @
% 0.19/0.57                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.19/0.57                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.19/0.57                          ( k2_tops_2 @
% 0.19/0.57                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.19/0.57                          C ) =
% 0.19/0.57                        ( k6_partfun1 @
% 0.19/0.57                          ( k2_relset_1 @
% 0.19/0.57                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) ) ) ) ) )),
% 0.19/0.57    inference('cnf.neg', [status(esa)], [t65_tops_2])).
% 0.19/0.57  thf('1', plain,
% 0.19/0.57      ((((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.57          (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.19/0.57          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.19/0.57          != (k6_partfun1 @ 
% 0.19/0.57              (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))
% 0.19/0.57        | ((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.57            (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.57            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.57            sk_C)
% 0.19/0.57            != (k6_partfun1 @ 
% 0.19/0.57                (k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.57                 sk_C))))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('2', plain,
% 0.19/0.57      ((((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.57          (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.57          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.57          sk_C)
% 0.19/0.57          != (k6_partfun1 @ 
% 0.19/0.57              (k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))))
% 0.19/0.57         <= (~
% 0.19/0.57             (((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.57                (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.57                sk_C)
% 0.19/0.57                = (k6_partfun1 @ 
% 0.19/0.57                   (k2_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.57                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.19/0.57      inference('split', [status(esa)], ['1'])).
% 0.19/0.57  thf('3', plain,
% 0.19/0.57      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.19/0.57         = (k2_struct_0 @ sk_B))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf(redefinition_k6_partfun1, axiom,
% 0.19/0.57    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.19/0.57  thf('4', plain, (![X16 : $i]: ((k6_partfun1 @ X16) = (k6_relat_1 @ X16))),
% 0.19/0.57      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.19/0.57  thf('5', plain,
% 0.19/0.57      ((((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.57          (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.57          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.57          sk_C) != (k6_relat_1 @ (k2_struct_0 @ sk_B))))
% 0.19/0.57         <= (~
% 0.19/0.57             (((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.57                (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.57                sk_C)
% 0.19/0.57                = (k6_partfun1 @ 
% 0.19/0.57                   (k2_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.57                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.19/0.57      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.19/0.57  thf(d3_struct_0, axiom,
% 0.19/0.57    (![A:$i]:
% 0.19/0.57     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.19/0.57  thf('6', plain,
% 0.19/0.57      (![X17 : $i]:
% 0.19/0.57         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.19/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.57  thf('7', plain,
% 0.19/0.57      ((m1_subset_1 @ sk_C @ 
% 0.19/0.57        (k1_zfmisc_1 @ 
% 0.19/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf(d4_tops_2, axiom,
% 0.19/0.57    (![A:$i,B:$i,C:$i]:
% 0.19/0.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.19/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.57       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.19/0.57         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.19/0.57  thf('8', plain,
% 0.19/0.57      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.19/0.57         (((k2_relset_1 @ X19 @ X18 @ X20) != (X18))
% 0.19/0.57          | ~ (v2_funct_1 @ X20)
% 0.19/0.57          | ((k2_tops_2 @ X19 @ X18 @ X20) = (k2_funct_1 @ X20))
% 0.19/0.57          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X18)))
% 0.19/0.57          | ~ (v1_funct_2 @ X20 @ X19 @ X18)
% 0.19/0.57          | ~ (v1_funct_1 @ X20))),
% 0.19/0.57      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.19/0.57  thf('9', plain,
% 0.19/0.57      ((~ (v1_funct_1 @ sk_C)
% 0.19/0.57        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.19/0.57        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.19/0.57            = (k2_funct_1 @ sk_C))
% 0.19/0.57        | ~ (v2_funct_1 @ sk_C)
% 0.19/0.57        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.19/0.57            != (u1_struct_0 @ sk_B)))),
% 0.19/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.57  thf('10', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('11', plain,
% 0.19/0.57      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('12', plain, ((v2_funct_1 @ sk_C)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('13', plain,
% 0.19/0.57      ((m1_subset_1 @ sk_C @ 
% 0.19/0.57        (k1_zfmisc_1 @ 
% 0.19/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf(redefinition_k2_relset_1, axiom,
% 0.19/0.57    (![A:$i,B:$i,C:$i]:
% 0.19/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.57       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.19/0.57  thf('14', plain,
% 0.19/0.57      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.57         (((k2_relset_1 @ X8 @ X9 @ X7) = (k2_relat_1 @ X7))
% 0.19/0.57          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.19/0.57      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.19/0.57  thf('15', plain,
% 0.19/0.57      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.19/0.57         = (k2_relat_1 @ sk_C))),
% 0.19/0.57      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.57  thf('16', plain,
% 0.19/0.57      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.19/0.57          = (k2_funct_1 @ sk_C))
% 0.19/0.57        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.19/0.57      inference('demod', [status(thm)], ['9', '10', '11', '12', '15'])).
% 0.19/0.57  thf('17', plain,
% 0.19/0.57      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.19/0.57        | ~ (l1_struct_0 @ sk_B)
% 0.19/0.57        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.19/0.57            = (k2_funct_1 @ sk_C)))),
% 0.19/0.57      inference('sup-', [status(thm)], ['6', '16'])).
% 0.19/0.57  thf('18', plain,
% 0.19/0.57      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.19/0.57         = (k2_relat_1 @ sk_C))),
% 0.19/0.57      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.57  thf('19', plain,
% 0.19/0.57      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.19/0.57         = (k2_struct_0 @ sk_B))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('20', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.19/0.57      inference('sup+', [status(thm)], ['18', '19'])).
% 0.19/0.57  thf('21', plain, ((l1_struct_0 @ sk_B)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('22', plain,
% 0.19/0.57      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.19/0.57        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.19/0.57            = (k2_funct_1 @ sk_C)))),
% 0.19/0.57      inference('demod', [status(thm)], ['17', '20', '21'])).
% 0.19/0.57  thf('23', plain,
% 0.19/0.57      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.19/0.57         = (k2_funct_1 @ sk_C))),
% 0.19/0.57      inference('simplify', [status(thm)], ['22'])).
% 0.19/0.57  thf('24', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.19/0.57      inference('sup+', [status(thm)], ['18', '19'])).
% 0.19/0.57  thf('25', plain,
% 0.19/0.57      ((((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.57          (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ (k2_funct_1 @ sk_C) @ 
% 0.19/0.57          sk_C) != (k6_relat_1 @ (k2_relat_1 @ sk_C))))
% 0.19/0.57         <= (~
% 0.19/0.57             (((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.57                (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.57                sk_C)
% 0.19/0.57                = (k6_partfun1 @ 
% 0.19/0.57                   (k2_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.57                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.19/0.57      inference('demod', [status(thm)], ['5', '23', '24'])).
% 0.19/0.57  thf('26', plain,
% 0.19/0.57      (![X0 : $i]:
% 0.19/0.57         (~ (v2_funct_1 @ X0)
% 0.19/0.57          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.19/0.57              = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.19/0.57          | ~ (v1_funct_1 @ X0)
% 0.19/0.57          | ~ (v1_relat_1 @ X0))),
% 0.19/0.57      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.19/0.57  thf('27', plain,
% 0.19/0.57      ((m1_subset_1 @ sk_C @ 
% 0.19/0.57        (k1_zfmisc_1 @ 
% 0.19/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf(dt_k2_tops_2, axiom,
% 0.19/0.57    (![A:$i,B:$i,C:$i]:
% 0.19/0.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.19/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.57       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 0.19/0.57         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 0.19/0.57         ( m1_subset_1 @
% 0.19/0.57           ( k2_tops_2 @ A @ B @ C ) @ 
% 0.19/0.57           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 0.19/0.57  thf('28', plain,
% 0.19/0.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.19/0.57         ((m1_subset_1 @ (k2_tops_2 @ X21 @ X22 @ X23) @ 
% 0.19/0.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21)))
% 0.19/0.57          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.19/0.57          | ~ (v1_funct_2 @ X23 @ X21 @ X22)
% 0.19/0.57          | ~ (v1_funct_1 @ X23))),
% 0.19/0.57      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.19/0.57  thf('29', plain,
% 0.19/0.57      ((~ (v1_funct_1 @ sk_C)
% 0.19/0.57        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.19/0.57        | (m1_subset_1 @ 
% 0.19/0.57           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.57           (k1_zfmisc_1 @ 
% 0.19/0.57            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.19/0.57      inference('sup-', [status(thm)], ['27', '28'])).
% 0.19/0.57  thf('30', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('31', plain,
% 0.19/0.57      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('32', plain,
% 0.19/0.57      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.19/0.57         = (k2_funct_1 @ sk_C))),
% 0.19/0.57      inference('simplify', [status(thm)], ['22'])).
% 0.19/0.57  thf('33', plain,
% 0.19/0.57      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.19/0.57        (k1_zfmisc_1 @ 
% 0.19/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.19/0.57      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.19/0.57  thf('34', plain,
% 0.19/0.57      ((m1_subset_1 @ sk_C @ 
% 0.19/0.57        (k1_zfmisc_1 @ 
% 0.19/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf(redefinition_k1_partfun1, axiom,
% 0.19/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.19/0.57     ( ( ( v1_funct_1 @ E ) & 
% 0.19/0.57         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.19/0.57         ( v1_funct_1 @ F ) & 
% 0.19/0.57         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.19/0.57       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.19/0.57  thf('35', plain,
% 0.19/0.57      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.19/0.57         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.19/0.57          | ~ (v1_funct_1 @ X10)
% 0.19/0.57          | ~ (v1_funct_1 @ X13)
% 0.19/0.57          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.19/0.57          | ((k1_partfun1 @ X11 @ X12 @ X14 @ X15 @ X10 @ X13)
% 0.19/0.57              = (k5_relat_1 @ X10 @ X13)))),
% 0.19/0.57      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.19/0.57  thf('36', plain,
% 0.19/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.57         (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ X2 @ 
% 0.19/0.57            X1 @ sk_C @ X0) = (k5_relat_1 @ sk_C @ X0))
% 0.19/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.19/0.57          | ~ (v1_funct_1 @ X0)
% 0.19/0.57          | ~ (v1_funct_1 @ sk_C))),
% 0.19/0.57      inference('sup-', [status(thm)], ['34', '35'])).
% 0.19/0.57  thf('37', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('38', plain,
% 0.19/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.57         (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ X2 @ 
% 0.19/0.57            X1 @ sk_C @ X0) = (k5_relat_1 @ sk_C @ X0))
% 0.19/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.19/0.57          | ~ (v1_funct_1 @ X0))),
% 0.19/0.57      inference('demod', [status(thm)], ['36', '37'])).
% 0.19/0.57  thf('39', plain,
% 0.19/0.57      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.19/0.57        | ((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.57            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.19/0.57            (k2_funct_1 @ sk_C)) = (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))))),
% 0.19/0.57      inference('sup-', [status(thm)], ['33', '38'])).
% 0.19/0.57  thf('40', plain,
% 0.19/0.57      ((m1_subset_1 @ sk_C @ 
% 0.19/0.57        (k1_zfmisc_1 @ 
% 0.19/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('41', plain,
% 0.19/0.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.19/0.57         ((v1_funct_1 @ (k2_tops_2 @ X21 @ X22 @ X23))
% 0.19/0.57          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.19/0.57          | ~ (v1_funct_2 @ X23 @ X21 @ X22)
% 0.19/0.57          | ~ (v1_funct_1 @ X23))),
% 0.19/0.57      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.19/0.57  thf('42', plain,
% 0.19/0.57      ((~ (v1_funct_1 @ sk_C)
% 0.19/0.57        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.19/0.57        | (v1_funct_1 @ 
% 0.19/0.57           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 0.19/0.57      inference('sup-', [status(thm)], ['40', '41'])).
% 0.19/0.57  thf('43', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('44', plain,
% 0.19/0.57      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('45', plain,
% 0.19/0.57      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.19/0.57         = (k2_funct_1 @ sk_C))),
% 0.19/0.57      inference('simplify', [status(thm)], ['22'])).
% 0.19/0.57  thf('46', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.19/0.57      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 0.19/0.57  thf('47', plain,
% 0.19/0.57      (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.57         (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.19/0.57         (k2_funct_1 @ sk_C)) = (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))),
% 0.19/0.57      inference('demod', [status(thm)], ['39', '46'])).
% 0.19/0.57  thf('48', plain,
% 0.19/0.57      ((((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.57          (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.19/0.57          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.19/0.57          != (k6_partfun1 @ 
% 0.19/0.57              (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))))
% 0.19/0.57         <= (~
% 0.19/0.57             (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.57                (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.19/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.19/0.57                = (k6_partfun1 @ 
% 0.19/0.57                   (k1_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.57                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.19/0.57      inference('split', [status(esa)], ['1'])).
% 0.19/0.57  thf('49', plain,
% 0.19/0.57      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.19/0.57         = (k2_funct_1 @ sk_C))),
% 0.19/0.57      inference('simplify', [status(thm)], ['22'])).
% 0.19/0.57  thf('50', plain,
% 0.19/0.57      ((m1_subset_1 @ sk_C @ 
% 0.19/0.57        (k1_zfmisc_1 @ 
% 0.19/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf(redefinition_k1_relset_1, axiom,
% 0.19/0.57    (![A:$i,B:$i,C:$i]:
% 0.19/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.57       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.19/0.57  thf('51', plain,
% 0.19/0.57      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.57         (((k1_relset_1 @ X5 @ X6 @ X4) = (k1_relat_1 @ X4))
% 0.19/0.57          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.19/0.57      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.19/0.57  thf('52', plain,
% 0.19/0.57      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.19/0.57         = (k1_relat_1 @ sk_C))),
% 0.19/0.57      inference('sup-', [status(thm)], ['50', '51'])).
% 0.19/0.57  thf('53', plain, (![X16 : $i]: ((k6_partfun1 @ X16) = (k6_relat_1 @ X16))),
% 0.19/0.57      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.19/0.57  thf('54', plain,
% 0.19/0.57      ((((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.57          (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.19/0.57          (k2_funct_1 @ sk_C)) != (k6_relat_1 @ (k1_relat_1 @ sk_C))))
% 0.19/0.57         <= (~
% 0.19/0.57             (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.57                (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.19/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.19/0.57                = (k6_partfun1 @ 
% 0.19/0.57                   (k1_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.57                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.19/0.57      inference('demod', [status(thm)], ['48', '49', '52', '53'])).
% 0.19/0.57  thf('55', plain,
% 0.19/0.57      ((((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.19/0.57          != (k6_relat_1 @ (k1_relat_1 @ sk_C))))
% 0.19/0.57         <= (~
% 0.19/0.57             (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.57                (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.19/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.19/0.57                = (k6_partfun1 @ 
% 0.19/0.57                   (k1_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.57                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.19/0.57      inference('sup-', [status(thm)], ['47', '54'])).
% 0.19/0.57  thf('56', plain,
% 0.19/0.57      (((((k6_relat_1 @ (k1_relat_1 @ sk_C))
% 0.19/0.57           != (k6_relat_1 @ (k1_relat_1 @ sk_C)))
% 0.19/0.57         | ~ (v1_relat_1 @ sk_C)
% 0.19/0.57         | ~ (v1_funct_1 @ sk_C)
% 0.19/0.57         | ~ (v2_funct_1 @ sk_C)))
% 0.19/0.57         <= (~
% 0.19/0.57             (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.57                (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.19/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.19/0.57                = (k6_partfun1 @ 
% 0.19/0.57                   (k1_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.57                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.19/0.57      inference('sup-', [status(thm)], ['26', '55'])).
% 0.19/0.57  thf('57', plain,
% 0.19/0.57      ((m1_subset_1 @ sk_C @ 
% 0.19/0.57        (k1_zfmisc_1 @ 
% 0.19/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf(cc1_relset_1, axiom,
% 0.19/0.57    (![A:$i,B:$i,C:$i]:
% 0.19/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.57       ( v1_relat_1 @ C ) ))).
% 0.19/0.57  thf('58', plain,
% 0.19/0.57      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.57         ((v1_relat_1 @ X1)
% 0.19/0.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3))))),
% 0.19/0.57      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.19/0.57  thf('59', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.57      inference('sup-', [status(thm)], ['57', '58'])).
% 0.19/0.57  thf('60', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('61', plain, ((v2_funct_1 @ sk_C)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('62', plain,
% 0.19/0.57      ((((k6_relat_1 @ (k1_relat_1 @ sk_C))
% 0.19/0.57          != (k6_relat_1 @ (k1_relat_1 @ sk_C))))
% 0.19/0.57         <= (~
% 0.19/0.57             (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.57                (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.19/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.19/0.57                = (k6_partfun1 @ 
% 0.19/0.57                   (k1_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.57                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.19/0.57      inference('demod', [status(thm)], ['56', '59', '60', '61'])).
% 0.19/0.57  thf('63', plain,
% 0.19/0.57      ((((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.57          (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.19/0.57          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.19/0.57          = (k6_partfun1 @ 
% 0.19/0.57             (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))))),
% 0.19/0.57      inference('simplify', [status(thm)], ['62'])).
% 0.19/0.57  thf('64', plain,
% 0.19/0.57      (~
% 0.19/0.57       (((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.57          (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.57          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.57          sk_C)
% 0.19/0.57          = (k6_partfun1 @ 
% 0.19/0.57             (k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))) | 
% 0.19/0.57       ~
% 0.19/0.57       (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.57          (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.19/0.57          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.19/0.57          = (k6_partfun1 @ 
% 0.19/0.57             (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))))),
% 0.19/0.57      inference('split', [status(esa)], ['1'])).
% 0.19/0.57  thf('65', plain,
% 0.19/0.57      (~
% 0.19/0.57       (((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.57          (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.57          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.19/0.57          sk_C)
% 0.19/0.57          = (k6_partfun1 @ 
% 0.19/0.57             (k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))))),
% 0.19/0.57      inference('sat_resolution*', [status(thm)], ['63', '64'])).
% 0.19/0.57  thf('66', plain,
% 0.19/0.57      (((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.57         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ (k2_funct_1 @ sk_C) @ 
% 0.19/0.57         sk_C) != (k6_relat_1 @ (k2_relat_1 @ sk_C)))),
% 0.19/0.57      inference('simpl_trail', [status(thm)], ['25', '65'])).
% 0.19/0.57  thf('67', plain,
% 0.19/0.57      ((m1_subset_1 @ sk_C @ 
% 0.19/0.57        (k1_zfmisc_1 @ 
% 0.19/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('68', plain,
% 0.19/0.57      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.19/0.57        (k1_zfmisc_1 @ 
% 0.19/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.19/0.57      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.19/0.57  thf('69', plain,
% 0.19/0.57      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.19/0.57         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.19/0.57          | ~ (v1_funct_1 @ X10)
% 0.19/0.57          | ~ (v1_funct_1 @ X13)
% 0.19/0.57          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.19/0.57          | ((k1_partfun1 @ X11 @ X12 @ X14 @ X15 @ X10 @ X13)
% 0.19/0.57              = (k5_relat_1 @ X10 @ X13)))),
% 0.19/0.57      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.19/0.57  thf('70', plain,
% 0.19/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.57         (((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ X2 @ 
% 0.19/0.57            X1 @ (k2_funct_1 @ sk_C) @ X0)
% 0.19/0.57            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))
% 0.19/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.19/0.57          | ~ (v1_funct_1 @ X0)
% 0.19/0.57          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.19/0.57      inference('sup-', [status(thm)], ['68', '69'])).
% 0.19/0.57  thf('71', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.19/0.57      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 0.19/0.57  thf('72', plain,
% 0.19/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.57         (((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ X2 @ 
% 0.19/0.57            X1 @ (k2_funct_1 @ sk_C) @ X0)
% 0.19/0.57            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))
% 0.19/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.19/0.57          | ~ (v1_funct_1 @ X0))),
% 0.19/0.57      inference('demod', [status(thm)], ['70', '71'])).
% 0.19/0.57  thf('73', plain,
% 0.19/0.57      ((~ (v1_funct_1 @ sk_C)
% 0.19/0.57        | ((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.57            (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.57            (k2_funct_1 @ sk_C) @ sk_C)
% 0.19/0.57            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)))),
% 0.19/0.57      inference('sup-', [status(thm)], ['67', '72'])).
% 0.19/0.57  thf('74', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('75', plain,
% 0.19/0.57      (((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.57         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ (k2_funct_1 @ sk_C) @ 
% 0.19/0.57         sk_C) = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))),
% 0.19/0.57      inference('demod', [status(thm)], ['73', '74'])).
% 0.19/0.57  thf('76', plain,
% 0.19/0.57      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.19/0.57         != (k6_relat_1 @ (k2_relat_1 @ sk_C)))),
% 0.19/0.57      inference('demod', [status(thm)], ['66', '75'])).
% 0.19/0.57  thf('77', plain,
% 0.19/0.57      ((((k6_relat_1 @ (k2_relat_1 @ sk_C))
% 0.19/0.57          != (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.19/0.57        | ~ (v1_relat_1 @ sk_C)
% 0.19/0.57        | ~ (v1_funct_1 @ sk_C)
% 0.19/0.57        | ~ (v2_funct_1 @ sk_C))),
% 0.19/0.57      inference('sup-', [status(thm)], ['0', '76'])).
% 0.19/0.57  thf('78', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.57      inference('sup-', [status(thm)], ['57', '58'])).
% 0.19/0.57  thf('79', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('80', plain, ((v2_funct_1 @ sk_C)),
% 0.19/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.57  thf('81', plain,
% 0.19/0.57      (((k6_relat_1 @ (k2_relat_1 @ sk_C))
% 0.19/0.57         != (k6_relat_1 @ (k2_relat_1 @ sk_C)))),
% 0.19/0.57      inference('demod', [status(thm)], ['77', '78', '79', '80'])).
% 0.19/0.57  thf('82', plain, ($false), inference('simplify', [status(thm)], ['81'])).
% 0.19/0.57  
% 0.19/0.57  % SZS output end Refutation
% 0.19/0.57  
% 0.19/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
