%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9QIPbxLVCD

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:26 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 642 expanded)
%              Number of leaves         :   34 ( 199 expanded)
%              Depth                    :   20
%              Number of atoms          : 2197 (22445 expanded)
%              Number of equality atoms :  125 ( 980 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

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

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

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

thf('3',plain,
    ( ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k6_partfun1 @ ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) )
    | ( ( k1_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_C )
     != ( k6_partfun1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k1_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_C )
     != ( k6_partfun1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) )
   <= ( ( k1_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_C )
     != ( k6_partfun1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('6',plain,(
    ! [X17: $i] :
      ( ( k6_partfun1 @ X17 )
      = ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('7',plain,
    ( ( ( k1_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_C )
     != ( k6_relat_1 @ ( k2_struct_0 @ sk_B ) ) )
   <= ( ( k1_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_C )
     != ( k6_partfun1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ( ( ( k1_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) @ sk_C )
       != ( k6_relat_1 @ ( k2_struct_0 @ sk_B ) ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_C )
     != ( k6_partfun1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k1_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) @ sk_C )
     != ( k6_relat_1 @ ( k2_struct_0 @ sk_B ) ) )
   <= ( ( k1_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_C )
     != ( k6_partfun1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('13',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('17',plain,
    ( ( ( k1_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) @ sk_C )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
   <= ( ( k1_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_C )
     != ( k6_partfun1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['10','15','16'])).

thf('18',plain,
    ( ( ( ( k1_partfun1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) @ sk_C )
       != ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_C )
     != ( k6_partfun1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['1','17'])).

thf('19',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('20',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( k1_partfun1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) @ sk_C )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
   <= ( ( k1_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_C )
     != ( k6_partfun1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

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

thf('29',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X22 @ X24 )
       != X22 )
      | ~ ( v2_funct_1 @ X24 )
      | ( ( k2_tops_2 @ X23 @ X22 @ X24 )
        = ( k2_funct_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('30',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('33',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('38',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('41',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('46',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('47',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['30','31','38','39','47'])).

thf('49',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( ( k1_partfun1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ sk_C ) @ sk_C )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
   <= ( ( k1_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_C )
     != ( k6_partfun1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['21','49'])).

thf('51',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ X4 @ ( k2_funct_1 @ X4 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

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

thf('53',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relset_1 @ X20 @ X19 @ X18 )
       != X19 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X20 @ X19 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('54',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('57',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('58',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['54','55','56','57','58'])).

thf('60',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
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

thf('62',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( ( k1_partfun1 @ X12 @ X13 @ X15 @ X16 @ X11 @ X14 )
        = ( k5_relat_1 @ X11 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('68',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relset_1 @ X20 @ X19 @ X18 )
       != X19 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X20 @ X19 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('69',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('72',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('73',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['69','70','71','72','73'])).

thf('75',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,
    ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['66','75'])).

thf('77',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('78',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X22 @ X24 )
       != X22 )
      | ~ ( v2_funct_1 @ X24 )
      | ( ( k2_tops_2 @ X23 @ X22 @ X24 )
        = ( k2_funct_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('81',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('86',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['81','82','83','84','85'])).

thf('87',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['78','86'])).

thf('88',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('89',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k6_partfun1 @ ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) )
   <= ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k6_partfun1 @ ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('93',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('94',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k1_relset_1 @ X6 @ X7 @ X5 )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('95',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X17: $i] :
      ( ( k6_partfun1 @ X17 )
      = ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('97',plain,
    ( ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
   <= ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k6_partfun1 @ ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['92','95','96'])).

thf('98',plain,
    ( ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_funct_1 @ sk_C ) )
     != ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
   <= ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k6_partfun1 @ ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['91','97'])).

thf('99',plain,
    ( ( ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_funct_1 @ sk_C ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k6_partfun1 @ ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['77','98'])).

thf('100',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('101',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_funct_1 @ sk_C ) )
     != ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
   <= ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k6_partfun1 @ ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
     != ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
   <= ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k6_partfun1 @ ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['76','102'])).

thf('104',plain,
    ( ( ( ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k6_partfun1 @ ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['51','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('107',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('108',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('109',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) )
     != ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
   <= ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k6_partfun1 @ ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['104','109','110','111'])).

thf('113',plain,
    ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k6_partfun1 @ ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,
    ( ( ( k1_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_C )
     != ( k6_partfun1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) )
    | ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k6_partfun1 @ ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('115',plain,(
    ( k1_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_C )
 != ( k6_partfun1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['113','114'])).

thf('116',plain,(
    ( k1_partfun1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ sk_C ) @ sk_C )
 != ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['50','115'])).

thf('117',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('119',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( ( k1_partfun1 @ X12 @ X13 @ X15 @ X16 @ X11 @ X14 )
        = ( k5_relat_1 @ X11 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ X2 @ X1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['74'])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ X2 @ X1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_partfun1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['117','122'])).

thf('124',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( k1_partfun1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
 != ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['116','125'])).

thf('127',plain,
    ( ( ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','126'])).

thf('128',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['107','108'])).

thf('129',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) )
 != ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['127','128','129','130'])).

thf('132',plain,(
    $false ),
    inference(simplify,[status(thm)],['131'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9QIPbxLVCD
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:04:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.36/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.60  % Solved by: fo/fo7.sh
% 0.36/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.60  % done 480 iterations in 0.137s
% 0.36/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.60  % SZS output start Refutation
% 0.36/0.60  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.36/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.60  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.36/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.60  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.36/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.60  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.36/0.60  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.36/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.60  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.36/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.60  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.36/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.60  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.36/0.60  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.36/0.60  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.36/0.60  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.36/0.60  thf(t61_funct_1, axiom,
% 0.36/0.60    (![A:$i]:
% 0.36/0.60     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.36/0.60       ( ( v2_funct_1 @ A ) =>
% 0.36/0.60         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.36/0.60             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.36/0.60           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.36/0.60             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.36/0.60  thf('0', plain,
% 0.36/0.60      (![X4 : $i]:
% 0.36/0.60         (~ (v2_funct_1 @ X4)
% 0.36/0.60          | ((k5_relat_1 @ (k2_funct_1 @ X4) @ X4)
% 0.36/0.60              = (k6_relat_1 @ (k2_relat_1 @ X4)))
% 0.36/0.60          | ~ (v1_funct_1 @ X4)
% 0.36/0.60          | ~ (v1_relat_1 @ X4))),
% 0.36/0.60      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.36/0.60  thf(d3_struct_0, axiom,
% 0.36/0.60    (![A:$i]:
% 0.36/0.60     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.36/0.60  thf('1', plain,
% 0.36/0.60      (![X21 : $i]:
% 0.36/0.60         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.36/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.60  thf('2', plain,
% 0.36/0.60      (![X21 : $i]:
% 0.36/0.60         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.36/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.60  thf(t65_tops_2, conjecture,
% 0.36/0.60    (![A:$i]:
% 0.36/0.60     ( ( l1_struct_0 @ A ) =>
% 0.36/0.60       ( ![B:$i]:
% 0.36/0.60         ( ( l1_struct_0 @ B ) =>
% 0.36/0.60           ( ![C:$i]:
% 0.36/0.60             ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.60                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.60                 ( m1_subset_1 @
% 0.36/0.60                   C @ 
% 0.36/0.60                   ( k1_zfmisc_1 @
% 0.36/0.60                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.60               ( ( ( ( k2_relset_1 @
% 0.36/0.60                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.36/0.60                     ( k2_struct_0 @ B ) ) & 
% 0.36/0.60                   ( v2_funct_1 @ C ) ) =>
% 0.36/0.60                 ( ( ( k1_partfun1 @
% 0.36/0.60                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.36/0.60                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ C @ 
% 0.36/0.60                       ( k2_tops_2 @
% 0.36/0.60                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.36/0.60                     ( k6_partfun1 @
% 0.36/0.60                       ( k1_relset_1 @
% 0.36/0.60                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) & 
% 0.36/0.60                   ( ( k1_partfun1 @
% 0.36/0.60                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.36/0.60                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.36/0.60                       ( k2_tops_2 @
% 0.36/0.60                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.36/0.60                       C ) =
% 0.36/0.60                     ( k6_partfun1 @
% 0.36/0.60                       ( k2_relset_1 @
% 0.36/0.60                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.60    (~( ![A:$i]:
% 0.36/0.60        ( ( l1_struct_0 @ A ) =>
% 0.36/0.60          ( ![B:$i]:
% 0.36/0.60            ( ( l1_struct_0 @ B ) =>
% 0.36/0.60              ( ![C:$i]:
% 0.36/0.60                ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.60                    ( v1_funct_2 @
% 0.36/0.60                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.60                    ( m1_subset_1 @
% 0.36/0.60                      C @ 
% 0.36/0.60                      ( k1_zfmisc_1 @
% 0.36/0.60                        ( k2_zfmisc_1 @
% 0.36/0.60                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.60                  ( ( ( ( k2_relset_1 @
% 0.36/0.60                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.36/0.60                        ( k2_struct_0 @ B ) ) & 
% 0.36/0.60                      ( v2_funct_1 @ C ) ) =>
% 0.36/0.60                    ( ( ( k1_partfun1 @
% 0.36/0.60                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.36/0.60                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ C @ 
% 0.36/0.60                          ( k2_tops_2 @
% 0.36/0.60                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.36/0.60                        ( k6_partfun1 @
% 0.36/0.60                          ( k1_relset_1 @
% 0.36/0.60                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) & 
% 0.36/0.60                      ( ( k1_partfun1 @
% 0.36/0.60                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.36/0.60                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.36/0.60                          ( k2_tops_2 @
% 0.36/0.60                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.36/0.60                          C ) =
% 0.36/0.60                        ( k6_partfun1 @
% 0.36/0.60                          ( k2_relset_1 @
% 0.36/0.60                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) ) ) ) ) )),
% 0.36/0.60    inference('cnf.neg', [status(esa)], [t65_tops_2])).
% 0.36/0.60  thf('3', plain,
% 0.36/0.60      ((((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.60          (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.36/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.60          != (k6_partfun1 @ 
% 0.36/0.60              (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))
% 0.36/0.60        | ((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.60            (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.60            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.36/0.60            sk_C)
% 0.36/0.60            != (k6_partfun1 @ 
% 0.36/0.60                (k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.60                 sk_C))))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('4', plain,
% 0.36/0.60      ((((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.60          (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.36/0.60          sk_C)
% 0.36/0.60          != (k6_partfun1 @ 
% 0.36/0.60              (k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))))
% 0.36/0.60         <= (~
% 0.36/0.60             (((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.60                (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.36/0.60                sk_C)
% 0.36/0.60                = (k6_partfun1 @ 
% 0.36/0.60                   (k2_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.60                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.36/0.60      inference('split', [status(esa)], ['3'])).
% 0.36/0.60  thf('5', plain,
% 0.36/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.60         = (k2_struct_0 @ sk_B))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf(redefinition_k6_partfun1, axiom,
% 0.36/0.60    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.36/0.60  thf('6', plain, (![X17 : $i]: ((k6_partfun1 @ X17) = (k6_relat_1 @ X17))),
% 0.36/0.60      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.36/0.60  thf('7', plain,
% 0.36/0.60      ((((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.60          (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.36/0.60          sk_C) != (k6_relat_1 @ (k2_struct_0 @ sk_B))))
% 0.36/0.60         <= (~
% 0.36/0.60             (((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.60                (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.36/0.60                sk_C)
% 0.36/0.60                = (k6_partfun1 @ 
% 0.36/0.60                   (k2_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.60                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.36/0.60      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.36/0.60  thf('8', plain,
% 0.36/0.60      (((((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.60           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.60           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C) @ 
% 0.36/0.60           sk_C) != (k6_relat_1 @ (k2_struct_0 @ sk_B)))
% 0.36/0.60         | ~ (l1_struct_0 @ sk_B)))
% 0.36/0.60         <= (~
% 0.36/0.60             (((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.60                (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.36/0.60                sk_C)
% 0.36/0.60                = (k6_partfun1 @ 
% 0.36/0.60                   (k2_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.60                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.36/0.60      inference('sup-', [status(thm)], ['2', '7'])).
% 0.36/0.60  thf('9', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('10', plain,
% 0.36/0.60      ((((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.60          (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C) @ 
% 0.36/0.60          sk_C) != (k6_relat_1 @ (k2_struct_0 @ sk_B))))
% 0.36/0.60         <= (~
% 0.36/0.60             (((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.60                (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.36/0.60                sk_C)
% 0.36/0.60                = (k6_partfun1 @ 
% 0.36/0.60                   (k2_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.60                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.36/0.60      inference('demod', [status(thm)], ['8', '9'])).
% 0.36/0.60  thf('11', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_C @ 
% 0.36/0.60        (k1_zfmisc_1 @ 
% 0.36/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf(redefinition_k2_relset_1, axiom,
% 0.36/0.60    (![A:$i,B:$i,C:$i]:
% 0.36/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.60       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.36/0.60  thf('12', plain,
% 0.36/0.60      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.36/0.60         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 0.36/0.60          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.36/0.60      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.36/0.60  thf('13', plain,
% 0.36/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.60         = (k2_relat_1 @ sk_C))),
% 0.36/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.60  thf('14', plain,
% 0.36/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.60         = (k2_struct_0 @ sk_B))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('15', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.60      inference('sup+', [status(thm)], ['13', '14'])).
% 0.36/0.60  thf('16', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.60      inference('sup+', [status(thm)], ['13', '14'])).
% 0.36/0.60  thf('17', plain,
% 0.36/0.60      ((((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.60          (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C) @ 
% 0.36/0.60          sk_C) != (k6_relat_1 @ (k2_relat_1 @ sk_C))))
% 0.36/0.60         <= (~
% 0.36/0.60             (((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.60                (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.36/0.60                sk_C)
% 0.36/0.60                = (k6_partfun1 @ 
% 0.36/0.60                   (k2_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.60                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.36/0.60      inference('demod', [status(thm)], ['10', '15', '16'])).
% 0.36/0.60  thf('18', plain,
% 0.36/0.60      (((((k1_partfun1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.60           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.60           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C) @ 
% 0.36/0.60           sk_C) != (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.36/0.60         | ~ (l1_struct_0 @ sk_B)))
% 0.36/0.60         <= (~
% 0.36/0.60             (((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.60                (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.36/0.60                sk_C)
% 0.36/0.60                = (k6_partfun1 @ 
% 0.36/0.60                   (k2_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.60                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.36/0.60      inference('sup-', [status(thm)], ['1', '17'])).
% 0.36/0.60  thf('19', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.60      inference('sup+', [status(thm)], ['13', '14'])).
% 0.36/0.60  thf('20', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('21', plain,
% 0.36/0.60      ((((k1_partfun1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.60          (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C) @ 
% 0.36/0.60          sk_C) != (k6_relat_1 @ (k2_relat_1 @ sk_C))))
% 0.36/0.60         <= (~
% 0.36/0.60             (((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.60                (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.36/0.60                sk_C)
% 0.36/0.60                = (k6_partfun1 @ 
% 0.36/0.60                   (k2_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.60                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.36/0.60      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.36/0.60  thf('22', plain,
% 0.36/0.60      (![X21 : $i]:
% 0.36/0.60         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.36/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.60  thf('23', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_C @ 
% 0.36/0.60        (k1_zfmisc_1 @ 
% 0.36/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('24', plain,
% 0.36/0.60      (((m1_subset_1 @ sk_C @ 
% 0.36/0.60         (k1_zfmisc_1 @ 
% 0.36/0.60          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.36/0.60        | ~ (l1_struct_0 @ sk_B))),
% 0.36/0.60      inference('sup+', [status(thm)], ['22', '23'])).
% 0.36/0.60  thf('25', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('26', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_C @ 
% 0.36/0.60        (k1_zfmisc_1 @ 
% 0.36/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.36/0.60      inference('demod', [status(thm)], ['24', '25'])).
% 0.36/0.60  thf('27', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.60      inference('sup+', [status(thm)], ['13', '14'])).
% 0.36/0.60  thf('28', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_C @ 
% 0.36/0.60        (k1_zfmisc_1 @ 
% 0.36/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.36/0.60      inference('demod', [status(thm)], ['26', '27'])).
% 0.36/0.60  thf(d4_tops_2, axiom,
% 0.36/0.60    (![A:$i,B:$i,C:$i]:
% 0.36/0.60     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.36/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.60       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.36/0.60         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.36/0.60  thf('29', plain,
% 0.36/0.60      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.36/0.60         (((k2_relset_1 @ X23 @ X22 @ X24) != (X22))
% 0.36/0.60          | ~ (v2_funct_1 @ X24)
% 0.36/0.60          | ((k2_tops_2 @ X23 @ X22 @ X24) = (k2_funct_1 @ X24))
% 0.36/0.60          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.36/0.60          | ~ (v1_funct_2 @ X24 @ X23 @ X22)
% 0.36/0.60          | ~ (v1_funct_1 @ X24))),
% 0.36/0.60      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.36/0.60  thf('30', plain,
% 0.36/0.60      ((~ (v1_funct_1 @ sk_C)
% 0.36/0.60        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.36/0.60        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.36/0.60            = (k2_funct_1 @ sk_C))
% 0.36/0.60        | ~ (v2_funct_1 @ sk_C)
% 0.36/0.60        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.36/0.60            != (k2_relat_1 @ sk_C)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['28', '29'])).
% 0.36/0.60  thf('31', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('32', plain,
% 0.36/0.60      (![X21 : $i]:
% 0.36/0.60         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.36/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.60  thf('33', plain,
% 0.36/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('34', plain,
% 0.36/0.60      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.36/0.60        | ~ (l1_struct_0 @ sk_B))),
% 0.36/0.60      inference('sup+', [status(thm)], ['32', '33'])).
% 0.36/0.60  thf('35', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('36', plain,
% 0.36/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.36/0.60      inference('demod', [status(thm)], ['34', '35'])).
% 0.36/0.60  thf('37', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.60      inference('sup+', [status(thm)], ['13', '14'])).
% 0.36/0.60  thf('38', plain,
% 0.36/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.36/0.60      inference('demod', [status(thm)], ['36', '37'])).
% 0.36/0.60  thf('39', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('40', plain,
% 0.36/0.60      (![X21 : $i]:
% 0.36/0.60         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.36/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.60  thf('41', plain,
% 0.36/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.60         = (k2_struct_0 @ sk_B))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('42', plain,
% 0.36/0.60      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.36/0.60          = (k2_struct_0 @ sk_B))
% 0.36/0.60        | ~ (l1_struct_0 @ sk_B))),
% 0.36/0.60      inference('sup+', [status(thm)], ['40', '41'])).
% 0.36/0.60  thf('43', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('44', plain,
% 0.36/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.36/0.60         = (k2_struct_0 @ sk_B))),
% 0.36/0.60      inference('demod', [status(thm)], ['42', '43'])).
% 0.36/0.60  thf('45', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.60      inference('sup+', [status(thm)], ['13', '14'])).
% 0.36/0.60  thf('46', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.60      inference('sup+', [status(thm)], ['13', '14'])).
% 0.36/0.60  thf('47', plain,
% 0.36/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.36/0.60         = (k2_relat_1 @ sk_C))),
% 0.36/0.60      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.36/0.60  thf('48', plain,
% 0.36/0.60      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.36/0.60          = (k2_funct_1 @ sk_C))
% 0.36/0.60        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.36/0.60      inference('demod', [status(thm)], ['30', '31', '38', '39', '47'])).
% 0.36/0.60  thf('49', plain,
% 0.36/0.60      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.36/0.60         = (k2_funct_1 @ sk_C))),
% 0.36/0.60      inference('simplify', [status(thm)], ['48'])).
% 0.36/0.60  thf('50', plain,
% 0.36/0.60      ((((k1_partfun1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.60          (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.60          sk_C) != (k6_relat_1 @ (k2_relat_1 @ sk_C))))
% 0.36/0.60         <= (~
% 0.36/0.60             (((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.60                (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.36/0.60                sk_C)
% 0.36/0.60                = (k6_partfun1 @ 
% 0.36/0.60                   (k2_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.60                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.36/0.60      inference('demod', [status(thm)], ['21', '49'])).
% 0.36/0.60  thf('51', plain,
% 0.36/0.60      (![X4 : $i]:
% 0.36/0.60         (~ (v2_funct_1 @ X4)
% 0.36/0.60          | ((k5_relat_1 @ X4 @ (k2_funct_1 @ X4))
% 0.36/0.60              = (k6_relat_1 @ (k1_relat_1 @ X4)))
% 0.36/0.60          | ~ (v1_funct_1 @ X4)
% 0.36/0.60          | ~ (v1_relat_1 @ X4))),
% 0.36/0.60      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.36/0.60  thf('52', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_C @ 
% 0.36/0.60        (k1_zfmisc_1 @ 
% 0.36/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.36/0.60      inference('demod', [status(thm)], ['26', '27'])).
% 0.36/0.60  thf(t31_funct_2, axiom,
% 0.36/0.60    (![A:$i,B:$i,C:$i]:
% 0.36/0.60     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.36/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.60       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.36/0.60         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.36/0.60           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.36/0.60           ( m1_subset_1 @
% 0.36/0.60             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.36/0.60  thf('53', plain,
% 0.36/0.60      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.36/0.60         (~ (v2_funct_1 @ X18)
% 0.36/0.60          | ((k2_relset_1 @ X20 @ X19 @ X18) != (X19))
% 0.36/0.60          | (m1_subset_1 @ (k2_funct_1 @ X18) @ 
% 0.36/0.60             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.36/0.60          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19)))
% 0.36/0.60          | ~ (v1_funct_2 @ X18 @ X20 @ X19)
% 0.36/0.60          | ~ (v1_funct_1 @ X18))),
% 0.36/0.60      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.36/0.60  thf('54', plain,
% 0.36/0.60      ((~ (v1_funct_1 @ sk_C)
% 0.36/0.60        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.36/0.60        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.60           (k1_zfmisc_1 @ 
% 0.36/0.60            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.36/0.60        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.36/0.60            != (k2_relat_1 @ sk_C))
% 0.36/0.60        | ~ (v2_funct_1 @ sk_C))),
% 0.36/0.60      inference('sup-', [status(thm)], ['52', '53'])).
% 0.36/0.60  thf('55', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('56', plain,
% 0.36/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.36/0.60      inference('demod', [status(thm)], ['36', '37'])).
% 0.36/0.60  thf('57', plain,
% 0.36/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.36/0.60         = (k2_relat_1 @ sk_C))),
% 0.36/0.60      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.36/0.60  thf('58', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('59', plain,
% 0.36/0.60      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.60         (k1_zfmisc_1 @ 
% 0.36/0.60          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.36/0.60        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.36/0.60      inference('demod', [status(thm)], ['54', '55', '56', '57', '58'])).
% 0.36/0.60  thf('60', plain,
% 0.36/0.60      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.60        (k1_zfmisc_1 @ 
% 0.36/0.60         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.60      inference('simplify', [status(thm)], ['59'])).
% 0.36/0.60  thf('61', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_C @ 
% 0.36/0.60        (k1_zfmisc_1 @ 
% 0.36/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf(redefinition_k1_partfun1, axiom,
% 0.36/0.60    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.36/0.60     ( ( ( v1_funct_1 @ E ) & 
% 0.36/0.60         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.36/0.60         ( v1_funct_1 @ F ) & 
% 0.36/0.60         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.36/0.60       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.36/0.60  thf('62', plain,
% 0.36/0.60      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.36/0.60         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.36/0.60          | ~ (v1_funct_1 @ X11)
% 0.36/0.60          | ~ (v1_funct_1 @ X14)
% 0.36/0.60          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.36/0.60          | ((k1_partfun1 @ X12 @ X13 @ X15 @ X16 @ X11 @ X14)
% 0.36/0.60              = (k5_relat_1 @ X11 @ X14)))),
% 0.36/0.60      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.36/0.60  thf('63', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.60         (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ X2 @ 
% 0.36/0.60            X1 @ sk_C @ X0) = (k5_relat_1 @ sk_C @ X0))
% 0.36/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.36/0.60          | ~ (v1_funct_1 @ X0)
% 0.36/0.60          | ~ (v1_funct_1 @ sk_C))),
% 0.36/0.60      inference('sup-', [status(thm)], ['61', '62'])).
% 0.36/0.60  thf('64', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('65', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.60         (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ X2 @ 
% 0.36/0.60            X1 @ sk_C @ X0) = (k5_relat_1 @ sk_C @ X0))
% 0.36/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.36/0.60          | ~ (v1_funct_1 @ X0))),
% 0.36/0.60      inference('demod', [status(thm)], ['63', '64'])).
% 0.36/0.60  thf('66', plain,
% 0.36/0.60      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.36/0.60        | ((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.60            (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.36/0.60            (k2_funct_1 @ sk_C)) = (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))))),
% 0.36/0.60      inference('sup-', [status(thm)], ['60', '65'])).
% 0.36/0.60  thf('67', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_C @ 
% 0.36/0.60        (k1_zfmisc_1 @ 
% 0.36/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.36/0.60      inference('demod', [status(thm)], ['26', '27'])).
% 0.36/0.60  thf('68', plain,
% 0.36/0.60      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.36/0.60         (~ (v2_funct_1 @ X18)
% 0.36/0.60          | ((k2_relset_1 @ X20 @ X19 @ X18) != (X19))
% 0.36/0.60          | (v1_funct_1 @ (k2_funct_1 @ X18))
% 0.36/0.60          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19)))
% 0.36/0.60          | ~ (v1_funct_2 @ X18 @ X20 @ X19)
% 0.36/0.60          | ~ (v1_funct_1 @ X18))),
% 0.36/0.60      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.36/0.60  thf('69', plain,
% 0.36/0.60      ((~ (v1_funct_1 @ sk_C)
% 0.36/0.60        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.36/0.60        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.36/0.60        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.36/0.60            != (k2_relat_1 @ sk_C))
% 0.36/0.60        | ~ (v2_funct_1 @ sk_C))),
% 0.36/0.60      inference('sup-', [status(thm)], ['67', '68'])).
% 0.36/0.60  thf('70', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('71', plain,
% 0.36/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.36/0.60      inference('demod', [status(thm)], ['36', '37'])).
% 0.36/0.60  thf('72', plain,
% 0.36/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.36/0.60         = (k2_relat_1 @ sk_C))),
% 0.36/0.60      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.36/0.60  thf('73', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('74', plain,
% 0.36/0.60      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.36/0.60        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.36/0.60      inference('demod', [status(thm)], ['69', '70', '71', '72', '73'])).
% 0.36/0.60  thf('75', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.36/0.60      inference('simplify', [status(thm)], ['74'])).
% 0.36/0.60  thf('76', plain,
% 0.36/0.60      (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.60         (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.36/0.60         (k2_funct_1 @ sk_C)) = (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))),
% 0.36/0.60      inference('demod', [status(thm)], ['66', '75'])).
% 0.36/0.60  thf('77', plain,
% 0.36/0.60      (![X21 : $i]:
% 0.36/0.60         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.36/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.60  thf('78', plain,
% 0.36/0.60      (![X21 : $i]:
% 0.36/0.60         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.36/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.60  thf('79', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_C @ 
% 0.36/0.60        (k1_zfmisc_1 @ 
% 0.36/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('80', plain,
% 0.36/0.60      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.36/0.60         (((k2_relset_1 @ X23 @ X22 @ X24) != (X22))
% 0.36/0.60          | ~ (v2_funct_1 @ X24)
% 0.36/0.60          | ((k2_tops_2 @ X23 @ X22 @ X24) = (k2_funct_1 @ X24))
% 0.36/0.60          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.36/0.60          | ~ (v1_funct_2 @ X24 @ X23 @ X22)
% 0.36/0.60          | ~ (v1_funct_1 @ X24))),
% 0.36/0.60      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.36/0.60  thf('81', plain,
% 0.36/0.60      ((~ (v1_funct_1 @ sk_C)
% 0.36/0.60        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.36/0.60        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.60            = (k2_funct_1 @ sk_C))
% 0.36/0.60        | ~ (v2_funct_1 @ sk_C)
% 0.36/0.60        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.60            != (u1_struct_0 @ sk_B)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['79', '80'])).
% 0.36/0.60  thf('82', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('83', plain,
% 0.36/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('84', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('85', plain,
% 0.36/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.60         = (k2_relat_1 @ sk_C))),
% 0.36/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.60  thf('86', plain,
% 0.36/0.60      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.60          = (k2_funct_1 @ sk_C))
% 0.36/0.60        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.36/0.60      inference('demod', [status(thm)], ['81', '82', '83', '84', '85'])).
% 0.36/0.60  thf('87', plain,
% 0.36/0.60      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.36/0.60        | ~ (l1_struct_0 @ sk_B)
% 0.36/0.60        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.60            = (k2_funct_1 @ sk_C)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['78', '86'])).
% 0.36/0.60  thf('88', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.60      inference('sup+', [status(thm)], ['13', '14'])).
% 0.36/0.60  thf('89', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('90', plain,
% 0.36/0.60      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.36/0.60        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.60            = (k2_funct_1 @ sk_C)))),
% 0.36/0.60      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.36/0.60  thf('91', plain,
% 0.36/0.60      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.60         = (k2_funct_1 @ sk_C))),
% 0.36/0.60      inference('simplify', [status(thm)], ['90'])).
% 0.36/0.60  thf('92', plain,
% 0.36/0.60      ((((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.60          (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.36/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.60          != (k6_partfun1 @ 
% 0.36/0.60              (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))))
% 0.36/0.60         <= (~
% 0.36/0.60             (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.60                (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.36/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.60                = (k6_partfun1 @ 
% 0.36/0.60                   (k1_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.60                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.36/0.60      inference('split', [status(esa)], ['3'])).
% 0.36/0.60  thf('93', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_C @ 
% 0.36/0.60        (k1_zfmisc_1 @ 
% 0.36/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf(redefinition_k1_relset_1, axiom,
% 0.36/0.60    (![A:$i,B:$i,C:$i]:
% 0.36/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.60       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.36/0.60  thf('94', plain,
% 0.36/0.60      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.36/0.60         (((k1_relset_1 @ X6 @ X7 @ X5) = (k1_relat_1 @ X5))
% 0.36/0.60          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.36/0.60      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.36/0.60  thf('95', plain,
% 0.36/0.60      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.60         = (k1_relat_1 @ sk_C))),
% 0.36/0.60      inference('sup-', [status(thm)], ['93', '94'])).
% 0.36/0.60  thf('96', plain, (![X17 : $i]: ((k6_partfun1 @ X17) = (k6_relat_1 @ X17))),
% 0.36/0.60      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.36/0.60  thf('97', plain,
% 0.36/0.60      ((((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.60          (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.36/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.60          != (k6_relat_1 @ (k1_relat_1 @ sk_C))))
% 0.36/0.60         <= (~
% 0.36/0.60             (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.60                (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.36/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.60                = (k6_partfun1 @ 
% 0.36/0.60                   (k1_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.60                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.36/0.60      inference('demod', [status(thm)], ['92', '95', '96'])).
% 0.36/0.60  thf('98', plain,
% 0.36/0.60      ((((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.60          (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.36/0.60          (k2_funct_1 @ sk_C)) != (k6_relat_1 @ (k1_relat_1 @ sk_C))))
% 0.36/0.60         <= (~
% 0.36/0.60             (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.60                (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.36/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.60                = (k6_partfun1 @ 
% 0.36/0.60                   (k1_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.60                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.36/0.60      inference('sup-', [status(thm)], ['91', '97'])).
% 0.36/0.60  thf('99', plain,
% 0.36/0.60      (((((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.60           (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.36/0.60           (k2_funct_1 @ sk_C)) != (k6_relat_1 @ (k1_relat_1 @ sk_C)))
% 0.36/0.60         | ~ (l1_struct_0 @ sk_B)))
% 0.36/0.60         <= (~
% 0.36/0.60             (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.60                (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.36/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.60                = (k6_partfun1 @ 
% 0.36/0.60                   (k1_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.60                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.36/0.60      inference('sup-', [status(thm)], ['77', '98'])).
% 0.36/0.60  thf('100', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.60      inference('sup+', [status(thm)], ['13', '14'])).
% 0.36/0.60  thf('101', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('102', plain,
% 0.36/0.60      ((((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.60          (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.36/0.60          (k2_funct_1 @ sk_C)) != (k6_relat_1 @ (k1_relat_1 @ sk_C))))
% 0.36/0.60         <= (~
% 0.36/0.60             (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.60                (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.36/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.60                = (k6_partfun1 @ 
% 0.36/0.60                   (k1_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.60                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.36/0.60      inference('demod', [status(thm)], ['99', '100', '101'])).
% 0.36/0.60  thf('103', plain,
% 0.36/0.60      ((((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.36/0.60          != (k6_relat_1 @ (k1_relat_1 @ sk_C))))
% 0.36/0.60         <= (~
% 0.36/0.60             (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.60                (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.36/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.60                = (k6_partfun1 @ 
% 0.36/0.60                   (k1_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.60                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.36/0.60      inference('sup-', [status(thm)], ['76', '102'])).
% 0.36/0.60  thf('104', plain,
% 0.36/0.60      (((((k6_relat_1 @ (k1_relat_1 @ sk_C))
% 0.36/0.60           != (k6_relat_1 @ (k1_relat_1 @ sk_C)))
% 0.36/0.60         | ~ (v1_relat_1 @ sk_C)
% 0.36/0.60         | ~ (v1_funct_1 @ sk_C)
% 0.36/0.60         | ~ (v2_funct_1 @ sk_C)))
% 0.36/0.60         <= (~
% 0.36/0.60             (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.60                (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.36/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.60                = (k6_partfun1 @ 
% 0.36/0.60                   (k1_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.60                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.36/0.60      inference('sup-', [status(thm)], ['51', '103'])).
% 0.36/0.60  thf('105', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_C @ 
% 0.36/0.60        (k1_zfmisc_1 @ 
% 0.36/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf(cc2_relat_1, axiom,
% 0.36/0.60    (![A:$i]:
% 0.36/0.60     ( ( v1_relat_1 @ A ) =>
% 0.36/0.60       ( ![B:$i]:
% 0.36/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.36/0.60  thf('106', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.36/0.60          | (v1_relat_1 @ X0)
% 0.36/0.60          | ~ (v1_relat_1 @ X1))),
% 0.36/0.60      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.36/0.60  thf('107', plain,
% 0.36/0.60      ((~ (v1_relat_1 @ 
% 0.36/0.60           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.36/0.60        | (v1_relat_1 @ sk_C))),
% 0.36/0.60      inference('sup-', [status(thm)], ['105', '106'])).
% 0.36/0.60  thf(fc6_relat_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.36/0.60  thf('108', plain,
% 0.36/0.60      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.36/0.60      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.36/0.60  thf('109', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.60      inference('demod', [status(thm)], ['107', '108'])).
% 0.36/0.60  thf('110', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('111', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('112', plain,
% 0.36/0.60      ((((k6_relat_1 @ (k1_relat_1 @ sk_C))
% 0.36/0.60          != (k6_relat_1 @ (k1_relat_1 @ sk_C))))
% 0.36/0.60         <= (~
% 0.36/0.60             (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.60                (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.36/0.60                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.60                = (k6_partfun1 @ 
% 0.36/0.60                   (k1_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.60                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.36/0.60      inference('demod', [status(thm)], ['104', '109', '110', '111'])).
% 0.36/0.60  thf('113', plain,
% 0.36/0.60      ((((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.60          (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.36/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.60          = (k6_partfun1 @ 
% 0.36/0.60             (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))))),
% 0.36/0.60      inference('simplify', [status(thm)], ['112'])).
% 0.36/0.60  thf('114', plain,
% 0.36/0.60      (~
% 0.36/0.60       (((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.60          (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.36/0.60          sk_C)
% 0.36/0.60          = (k6_partfun1 @ 
% 0.36/0.60             (k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))) | 
% 0.36/0.60       ~
% 0.36/0.60       (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.60          (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.36/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.61          = (k6_partfun1 @ 
% 0.36/0.61             (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))))),
% 0.36/0.61      inference('split', [status(esa)], ['3'])).
% 0.36/0.61  thf('115', plain,
% 0.36/0.61      (~
% 0.36/0.61       (((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.61          (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.61          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.36/0.61          sk_C)
% 0.36/0.61          = (k6_partfun1 @ 
% 0.36/0.61             (k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))))),
% 0.36/0.61      inference('sat_resolution*', [status(thm)], ['113', '114'])).
% 0.36/0.61  thf('116', plain,
% 0.36/0.61      (((k1_partfun1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.61         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.61         sk_C) != (k6_relat_1 @ (k2_relat_1 @ sk_C)))),
% 0.36/0.61      inference('simpl_trail', [status(thm)], ['50', '115'])).
% 0.36/0.61  thf('117', plain,
% 0.36/0.61      ((m1_subset_1 @ sk_C @ 
% 0.36/0.61        (k1_zfmisc_1 @ 
% 0.36/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('118', plain,
% 0.36/0.61      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.61        (k1_zfmisc_1 @ 
% 0.36/0.61         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.61      inference('simplify', [status(thm)], ['59'])).
% 0.36/0.61  thf('119', plain,
% 0.36/0.61      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.36/0.61         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.36/0.61          | ~ (v1_funct_1 @ X11)
% 0.36/0.61          | ~ (v1_funct_1 @ X14)
% 0.36/0.61          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.36/0.61          | ((k1_partfun1 @ X12 @ X13 @ X15 @ X16 @ X11 @ X14)
% 0.36/0.61              = (k5_relat_1 @ X11 @ X14)))),
% 0.36/0.61      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.36/0.61  thf('120', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.61         (((k1_partfun1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ X2 @ 
% 0.36/0.61            X1 @ (k2_funct_1 @ sk_C) @ X0)
% 0.36/0.61            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))
% 0.36/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.36/0.61          | ~ (v1_funct_1 @ X0)
% 0.36/0.61          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['118', '119'])).
% 0.36/0.61  thf('121', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.36/0.61      inference('simplify', [status(thm)], ['74'])).
% 0.36/0.61  thf('122', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.61         (((k1_partfun1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ X2 @ 
% 0.36/0.61            X1 @ (k2_funct_1 @ sk_C) @ X0)
% 0.36/0.61            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))
% 0.36/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.36/0.61          | ~ (v1_funct_1 @ X0))),
% 0.36/0.61      inference('demod', [status(thm)], ['120', '121'])).
% 0.36/0.61  thf('123', plain,
% 0.36/0.61      ((~ (v1_funct_1 @ sk_C)
% 0.36/0.61        | ((k1_partfun1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.61            (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.61            (k2_funct_1 @ sk_C) @ sk_C)
% 0.36/0.61            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['117', '122'])).
% 0.36/0.61  thf('124', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('125', plain,
% 0.36/0.61      (((k1_partfun1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.61         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.61         sk_C) = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))),
% 0.36/0.61      inference('demod', [status(thm)], ['123', '124'])).
% 0.36/0.61  thf('126', plain,
% 0.36/0.61      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.36/0.61         != (k6_relat_1 @ (k2_relat_1 @ sk_C)))),
% 0.36/0.61      inference('demod', [status(thm)], ['116', '125'])).
% 0.36/0.61  thf('127', plain,
% 0.36/0.61      ((((k6_relat_1 @ (k2_relat_1 @ sk_C))
% 0.36/0.61          != (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.36/0.61        | ~ (v1_relat_1 @ sk_C)
% 0.36/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.36/0.61        | ~ (v2_funct_1 @ sk_C))),
% 0.36/0.61      inference('sup-', [status(thm)], ['0', '126'])).
% 0.36/0.61  thf('128', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.61      inference('demod', [status(thm)], ['107', '108'])).
% 0.36/0.61  thf('129', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('130', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('131', plain,
% 0.36/0.61      (((k6_relat_1 @ (k2_relat_1 @ sk_C))
% 0.36/0.61         != (k6_relat_1 @ (k2_relat_1 @ sk_C)))),
% 0.36/0.61      inference('demod', [status(thm)], ['127', '128', '129', '130'])).
% 0.36/0.61  thf('132', plain, ($false), inference('simplify', [status(thm)], ['131'])).
% 0.36/0.61  
% 0.36/0.61  % SZS output end Refutation
% 0.36/0.61  
% 0.36/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
