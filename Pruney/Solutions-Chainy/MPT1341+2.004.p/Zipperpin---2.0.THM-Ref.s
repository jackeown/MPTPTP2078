%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PJmuE0MtYW

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:26 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 636 expanded)
%              Number of leaves         :   33 ( 197 expanded)
%              Depth                    :   20
%              Number of atoms          : 2181 (22413 expanded)
%              Number of equality atoms :  125 ( 980 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

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

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

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

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

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

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
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
    ! [X16: $i] :
      ( ( k6_partfun1 @ X16 )
      = ( k6_relat_1 @ X16 ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_relset_1 @ X8 @ X9 @ X7 )
        = ( k2_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
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
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X21 @ X23 )
       != X21 )
      | ~ ( v2_funct_1 @ X23 )
      | ( ( k2_tops_2 @ X22 @ X21 @ X23 )
        = ( k2_funct_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X23 @ X22 @ X21 )
      | ~ ( v1_funct_1 @ X23 ) ) ),
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
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
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
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
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
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k2_relset_1 @ X19 @ X18 @ X17 )
       != X18 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X18 ) ) )
      | ~ ( v1_funct_2 @ X17 @ X19 @ X18 )
      | ~ ( v1_funct_1 @ X17 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( ( k1_partfun1 @ X11 @ X12 @ X14 @ X15 @ X10 @ X13 )
        = ( k5_relat_1 @ X10 @ X13 ) ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k2_relset_1 @ X19 @ X18 @ X17 )
       != X18 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X18 ) ) )
      | ~ ( v1_funct_2 @ X17 @ X19 @ X18 )
      | ~ ( v1_funct_1 @ X17 ) ) ),
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
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('78',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X21 @ X23 )
       != X21 )
      | ~ ( v2_funct_1 @ X23 )
      | ( ( k2_tops_2 @ X22 @ X21 @ X23 )
        = ( k2_funct_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X23 @ X22 @ X21 )
      | ~ ( v1_funct_1 @ X23 ) ) ),
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
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k1_relset_1 @ X5 @ X6 @ X4 )
        = ( k1_relat_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('95',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X16: $i] :
      ( ( k6_partfun1 @ X16 )
      = ( k6_relat_1 @ X16 ) ) ),
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

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('106',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('107',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) )
     != ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
   <= ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k6_partfun1 @ ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['104','107','108','109'])).

thf('111',plain,
    ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k6_partfun1 @ ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,
    ( ( ( k1_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_C )
     != ( k6_partfun1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) )
    | ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k6_partfun1 @ ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('113',plain,(
    ( k1_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_C )
 != ( k6_partfun1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['111','112'])).

thf('114',plain,(
    ( k1_partfun1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ sk_C ) @ sk_C )
 != ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['50','113'])).

thf('115',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('117',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( ( k1_partfun1 @ X11 @ X12 @ X14 @ X15 @ X10 @ X13 )
        = ( k5_relat_1 @ X10 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ X2 @ X1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['74'])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ X2 @ X1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_partfun1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['115','120'])).

thf('122',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( k1_partfun1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
 != ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['114','123'])).

thf('125',plain,
    ( ( ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','124'])).

thf('126',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['105','106'])).

thf('127',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) )
 != ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['125','126','127','128'])).

thf('130',plain,(
    $false ),
    inference(simplify,[status(thm)],['129'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PJmuE0MtYW
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:45:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.58  % Solved by: fo/fo7.sh
% 0.20/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.58  % done 474 iterations in 0.119s
% 0.20/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.58  % SZS output start Refutation
% 0.20/0.58  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.20/0.58  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.58  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.20/0.58  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.58  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.58  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.20/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.58  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.58  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.20/0.58  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.58  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.58  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.58  thf(t61_funct_1, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.58       ( ( v2_funct_1 @ A ) =>
% 0.20/0.58         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.20/0.58             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.20/0.58           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.20/0.58             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.20/0.58  thf('0', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (v2_funct_1 @ X0)
% 0.20/0.58          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.20/0.58              = (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.20/0.58          | ~ (v1_funct_1 @ X0)
% 0.20/0.58          | ~ (v1_relat_1 @ X0))),
% 0.20/0.58      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.20/0.58  thf(d3_struct_0, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.20/0.58  thf('1', plain,
% 0.20/0.58      (![X20 : $i]:
% 0.20/0.58         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.20/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.58  thf('2', plain,
% 0.20/0.58      (![X20 : $i]:
% 0.20/0.58         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.20/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.58  thf(t65_tops_2, conjecture,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( l1_struct_0 @ A ) =>
% 0.20/0.58       ( ![B:$i]:
% 0.20/0.58         ( ( l1_struct_0 @ B ) =>
% 0.20/0.58           ( ![C:$i]:
% 0.20/0.58             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.58                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.58                 ( m1_subset_1 @
% 0.20/0.58                   C @ 
% 0.20/0.58                   ( k1_zfmisc_1 @
% 0.20/0.58                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.58               ( ( ( ( k2_relset_1 @
% 0.20/0.58                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.20/0.58                     ( k2_struct_0 @ B ) ) & 
% 0.20/0.58                   ( v2_funct_1 @ C ) ) =>
% 0.20/0.58                 ( ( ( k1_partfun1 @
% 0.20/0.58                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.20/0.58                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ C @ 
% 0.20/0.58                       ( k2_tops_2 @
% 0.20/0.58                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.20/0.58                     ( k6_partfun1 @
% 0.20/0.58                       ( k1_relset_1 @
% 0.20/0.58                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) & 
% 0.20/0.58                   ( ( k1_partfun1 @
% 0.20/0.58                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.20/0.58                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.20/0.58                       ( k2_tops_2 @
% 0.20/0.58                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.20/0.58                       C ) =
% 0.20/0.58                     ( k6_partfun1 @
% 0.20/0.58                       ( k2_relset_1 @
% 0.20/0.58                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.58    (~( ![A:$i]:
% 0.20/0.58        ( ( l1_struct_0 @ A ) =>
% 0.20/0.58          ( ![B:$i]:
% 0.20/0.58            ( ( l1_struct_0 @ B ) =>
% 0.20/0.58              ( ![C:$i]:
% 0.20/0.58                ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.58                    ( v1_funct_2 @
% 0.20/0.58                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.58                    ( m1_subset_1 @
% 0.20/0.58                      C @ 
% 0.20/0.58                      ( k1_zfmisc_1 @
% 0.20/0.58                        ( k2_zfmisc_1 @
% 0.20/0.58                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.58                  ( ( ( ( k2_relset_1 @
% 0.20/0.58                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.20/0.58                        ( k2_struct_0 @ B ) ) & 
% 0.20/0.58                      ( v2_funct_1 @ C ) ) =>
% 0.20/0.58                    ( ( ( k1_partfun1 @
% 0.20/0.58                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.20/0.58                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ C @ 
% 0.20/0.58                          ( k2_tops_2 @
% 0.20/0.58                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.20/0.58                        ( k6_partfun1 @
% 0.20/0.58                          ( k1_relset_1 @
% 0.20/0.58                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) & 
% 0.20/0.58                      ( ( k1_partfun1 @
% 0.20/0.58                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.20/0.58                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.20/0.58                          ( k2_tops_2 @
% 0.20/0.58                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 0.20/0.58                          C ) =
% 0.20/0.58                        ( k6_partfun1 @
% 0.20/0.58                          ( k2_relset_1 @
% 0.20/0.58                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.58    inference('cnf.neg', [status(esa)], [t65_tops_2])).
% 0.20/0.58  thf('3', plain,
% 0.20/0.58      ((((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58          (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.20/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.20/0.58          != (k6_partfun1 @ 
% 0.20/0.58              (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))
% 0.20/0.58        | ((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.58            (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.20/0.58            sk_C)
% 0.20/0.58            != (k6_partfun1 @ 
% 0.20/0.58                (k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58                 sk_C))))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('4', plain,
% 0.20/0.58      ((((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.58          (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.20/0.58          sk_C)
% 0.20/0.58          != (k6_partfun1 @ 
% 0.20/0.58              (k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))))
% 0.20/0.58         <= (~
% 0.20/0.58             (((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.58                (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.20/0.58                sk_C)
% 0.20/0.58                = (k6_partfun1 @ 
% 0.20/0.58                   (k2_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.58                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.20/0.58      inference('split', [status(esa)], ['3'])).
% 0.20/0.58  thf('5', plain,
% 0.20/0.58      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.20/0.58         = (k2_struct_0 @ sk_B))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(redefinition_k6_partfun1, axiom,
% 0.20/0.58    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.20/0.58  thf('6', plain, (![X16 : $i]: ((k6_partfun1 @ X16) = (k6_relat_1 @ X16))),
% 0.20/0.58      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.58  thf('7', plain,
% 0.20/0.58      ((((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.58          (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.20/0.58          sk_C) != (k6_relat_1 @ (k2_struct_0 @ sk_B))))
% 0.20/0.58         <= (~
% 0.20/0.58             (((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.58                (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.20/0.58                sk_C)
% 0.20/0.58                = (k6_partfun1 @ 
% 0.20/0.58                   (k2_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.58                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.20/0.58      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.20/0.58  thf('8', plain,
% 0.20/0.58      (((((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.58           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C) @ 
% 0.20/0.58           sk_C) != (k6_relat_1 @ (k2_struct_0 @ sk_B)))
% 0.20/0.58         | ~ (l1_struct_0 @ sk_B)))
% 0.20/0.58         <= (~
% 0.20/0.58             (((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.58                (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.20/0.58                sk_C)
% 0.20/0.58                = (k6_partfun1 @ 
% 0.20/0.58                   (k2_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.58                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['2', '7'])).
% 0.20/0.58  thf('9', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('10', plain,
% 0.20/0.58      ((((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.58          (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C) @ 
% 0.20/0.58          sk_C) != (k6_relat_1 @ (k2_struct_0 @ sk_B))))
% 0.20/0.58         <= (~
% 0.20/0.58             (((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.58                (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.20/0.58                sk_C)
% 0.20/0.58                = (k6_partfun1 @ 
% 0.20/0.58                   (k2_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.58                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.20/0.58      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.58  thf('11', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_C @ 
% 0.20/0.58        (k1_zfmisc_1 @ 
% 0.20/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.58       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.58  thf('12', plain,
% 0.20/0.58      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.58         (((k2_relset_1 @ X8 @ X9 @ X7) = (k2_relat_1 @ X7))
% 0.20/0.58          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.20/0.58      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.58  thf('13', plain,
% 0.20/0.58      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.20/0.58         = (k2_relat_1 @ sk_C))),
% 0.20/0.58      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.58  thf('14', plain,
% 0.20/0.58      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.20/0.58         = (k2_struct_0 @ sk_B))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('15', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.20/0.58      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.58  thf('16', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.20/0.58      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.58  thf('17', plain,
% 0.20/0.58      ((((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.58          (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C) @ 
% 0.20/0.58          sk_C) != (k6_relat_1 @ (k2_relat_1 @ sk_C))))
% 0.20/0.58         <= (~
% 0.20/0.58             (((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.58                (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.20/0.58                sk_C)
% 0.20/0.58                = (k6_partfun1 @ 
% 0.20/0.58                   (k2_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.58                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.20/0.58      inference('demod', [status(thm)], ['10', '15', '16'])).
% 0.20/0.58  thf('18', plain,
% 0.20/0.58      (((((k1_partfun1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.58           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C) @ 
% 0.20/0.58           sk_C) != (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.20/0.58         | ~ (l1_struct_0 @ sk_B)))
% 0.20/0.58         <= (~
% 0.20/0.58             (((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.58                (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.20/0.58                sk_C)
% 0.20/0.58                = (k6_partfun1 @ 
% 0.20/0.58                   (k2_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.58                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['1', '17'])).
% 0.20/0.58  thf('19', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.20/0.58      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.58  thf('20', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('21', plain,
% 0.20/0.58      ((((k1_partfun1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.58          (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C) @ 
% 0.20/0.58          sk_C) != (k6_relat_1 @ (k2_relat_1 @ sk_C))))
% 0.20/0.58         <= (~
% 0.20/0.58             (((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.58                (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.20/0.58                sk_C)
% 0.20/0.58                = (k6_partfun1 @ 
% 0.20/0.58                   (k2_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.58                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.20/0.58      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.20/0.58  thf('22', plain,
% 0.20/0.58      (![X20 : $i]:
% 0.20/0.58         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.20/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.58  thf('23', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_C @ 
% 0.20/0.58        (k1_zfmisc_1 @ 
% 0.20/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('24', plain,
% 0.20/0.58      (((m1_subset_1 @ sk_C @ 
% 0.20/0.58         (k1_zfmisc_1 @ 
% 0.20/0.58          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.20/0.58        | ~ (l1_struct_0 @ sk_B))),
% 0.20/0.58      inference('sup+', [status(thm)], ['22', '23'])).
% 0.20/0.58  thf('25', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('26', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_C @ 
% 0.20/0.58        (k1_zfmisc_1 @ 
% 0.20/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.20/0.58      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.58  thf('27', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.20/0.58      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.58  thf('28', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_C @ 
% 0.20/0.58        (k1_zfmisc_1 @ 
% 0.20/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.20/0.58      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.58  thf(d4_tops_2, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.58       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.20/0.58         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.20/0.58  thf('29', plain,
% 0.20/0.58      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.58         (((k2_relset_1 @ X22 @ X21 @ X23) != (X21))
% 0.20/0.58          | ~ (v2_funct_1 @ X23)
% 0.20/0.58          | ((k2_tops_2 @ X22 @ X21 @ X23) = (k2_funct_1 @ X23))
% 0.20/0.58          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21)))
% 0.20/0.58          | ~ (v1_funct_2 @ X23 @ X22 @ X21)
% 0.20/0.58          | ~ (v1_funct_1 @ X23))),
% 0.20/0.58      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.20/0.58  thf('30', plain,
% 0.20/0.58      ((~ (v1_funct_1 @ sk_C)
% 0.20/0.58        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.20/0.58        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.20/0.58            = (k2_funct_1 @ sk_C))
% 0.20/0.58        | ~ (v2_funct_1 @ sk_C)
% 0.20/0.58        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.20/0.58            != (k2_relat_1 @ sk_C)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.58  thf('31', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('32', plain,
% 0.20/0.58      (![X20 : $i]:
% 0.20/0.58         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.20/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.58  thf('33', plain,
% 0.20/0.58      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('34', plain,
% 0.20/0.58      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.20/0.58        | ~ (l1_struct_0 @ sk_B))),
% 0.20/0.58      inference('sup+', [status(thm)], ['32', '33'])).
% 0.20/0.58  thf('35', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('36', plain,
% 0.20/0.58      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.20/0.58      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.58  thf('37', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.20/0.58      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.58  thf('38', plain,
% 0.20/0.58      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.20/0.58      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.58  thf('39', plain, ((v2_funct_1 @ sk_C)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('40', plain,
% 0.20/0.58      (![X20 : $i]:
% 0.20/0.58         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.20/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.58  thf('41', plain,
% 0.20/0.58      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.20/0.58         = (k2_struct_0 @ sk_B))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('42', plain,
% 0.20/0.58      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.20/0.58          = (k2_struct_0 @ sk_B))
% 0.20/0.58        | ~ (l1_struct_0 @ sk_B))),
% 0.20/0.58      inference('sup+', [status(thm)], ['40', '41'])).
% 0.20/0.58  thf('43', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('44', plain,
% 0.20/0.58      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.20/0.58         = (k2_struct_0 @ sk_B))),
% 0.20/0.58      inference('demod', [status(thm)], ['42', '43'])).
% 0.20/0.58  thf('45', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.20/0.58      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.58  thf('46', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.20/0.58      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.58  thf('47', plain,
% 0.20/0.58      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.20/0.58         = (k2_relat_1 @ sk_C))),
% 0.20/0.58      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.20/0.58  thf('48', plain,
% 0.20/0.58      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.20/0.58          = (k2_funct_1 @ sk_C))
% 0.20/0.58        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.20/0.58      inference('demod', [status(thm)], ['30', '31', '38', '39', '47'])).
% 0.20/0.58  thf('49', plain,
% 0.20/0.58      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.20/0.58         = (k2_funct_1 @ sk_C))),
% 0.20/0.58      inference('simplify', [status(thm)], ['48'])).
% 0.20/0.58  thf('50', plain,
% 0.20/0.58      ((((k1_partfun1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.58          (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ (k2_funct_1 @ sk_C) @ 
% 0.20/0.58          sk_C) != (k6_relat_1 @ (k2_relat_1 @ sk_C))))
% 0.20/0.58         <= (~
% 0.20/0.58             (((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.58                (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.20/0.58                sk_C)
% 0.20/0.58                = (k6_partfun1 @ 
% 0.20/0.58                   (k2_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.58                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.20/0.58      inference('demod', [status(thm)], ['21', '49'])).
% 0.20/0.58  thf('51', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (v2_funct_1 @ X0)
% 0.20/0.58          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.20/0.58              = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.20/0.58          | ~ (v1_funct_1 @ X0)
% 0.20/0.58          | ~ (v1_relat_1 @ X0))),
% 0.20/0.58      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.20/0.58  thf('52', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_C @ 
% 0.20/0.58        (k1_zfmisc_1 @ 
% 0.20/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.20/0.58      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.58  thf(t31_funct_2, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.58       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.20/0.58         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.20/0.58           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.20/0.58           ( m1_subset_1 @
% 0.20/0.58             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.20/0.58  thf('53', plain,
% 0.20/0.58      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.58         (~ (v2_funct_1 @ X17)
% 0.20/0.58          | ((k2_relset_1 @ X19 @ X18 @ X17) != (X18))
% 0.20/0.58          | (m1_subset_1 @ (k2_funct_1 @ X17) @ 
% 0.20/0.58             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.20/0.58          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X18)))
% 0.20/0.58          | ~ (v1_funct_2 @ X17 @ X19 @ X18)
% 0.20/0.58          | ~ (v1_funct_1 @ X17))),
% 0.20/0.58      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.20/0.58  thf('54', plain,
% 0.20/0.58      ((~ (v1_funct_1 @ sk_C)
% 0.20/0.58        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.20/0.58        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.20/0.58           (k1_zfmisc_1 @ 
% 0.20/0.58            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.20/0.58        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.20/0.58            != (k2_relat_1 @ sk_C))
% 0.20/0.58        | ~ (v2_funct_1 @ sk_C))),
% 0.20/0.58      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.58  thf('55', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('56', plain,
% 0.20/0.58      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.20/0.58      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.58  thf('57', plain,
% 0.20/0.58      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.20/0.58         = (k2_relat_1 @ sk_C))),
% 0.20/0.58      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.20/0.58  thf('58', plain, ((v2_funct_1 @ sk_C)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('59', plain,
% 0.20/0.58      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.20/0.58         (k1_zfmisc_1 @ 
% 0.20/0.58          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.20/0.58        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.20/0.58      inference('demod', [status(thm)], ['54', '55', '56', '57', '58'])).
% 0.20/0.58  thf('60', plain,
% 0.20/0.58      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.20/0.58        (k1_zfmisc_1 @ 
% 0.20/0.58         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.58      inference('simplify', [status(thm)], ['59'])).
% 0.20/0.58  thf('61', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_C @ 
% 0.20/0.58        (k1_zfmisc_1 @ 
% 0.20/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(redefinition_k1_partfun1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.58     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.58         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.58         ( v1_funct_1 @ F ) & 
% 0.20/0.58         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.20/0.58       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.20/0.58  thf('62', plain,
% 0.20/0.58      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.58         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.20/0.58          | ~ (v1_funct_1 @ X10)
% 0.20/0.58          | ~ (v1_funct_1 @ X13)
% 0.20/0.58          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.20/0.58          | ((k1_partfun1 @ X11 @ X12 @ X14 @ X15 @ X10 @ X13)
% 0.20/0.58              = (k5_relat_1 @ X10 @ X13)))),
% 0.20/0.58      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.20/0.58  thf('63', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.58         (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ X2 @ 
% 0.20/0.58            X1 @ sk_C @ X0) = (k5_relat_1 @ sk_C @ X0))
% 0.20/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.20/0.58          | ~ (v1_funct_1 @ X0)
% 0.20/0.58          | ~ (v1_funct_1 @ sk_C))),
% 0.20/0.58      inference('sup-', [status(thm)], ['61', '62'])).
% 0.20/0.58  thf('64', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('65', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.58         (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ X2 @ 
% 0.20/0.58            X1 @ sk_C @ X0) = (k5_relat_1 @ sk_C @ X0))
% 0.20/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.20/0.58          | ~ (v1_funct_1 @ X0))),
% 0.20/0.58      inference('demod', [status(thm)], ['63', '64'])).
% 0.20/0.58  thf('66', plain,
% 0.20/0.58      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.20/0.58        | ((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58            (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.20/0.58            (k2_funct_1 @ sk_C)) = (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['60', '65'])).
% 0.20/0.58  thf('67', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_C @ 
% 0.20/0.58        (k1_zfmisc_1 @ 
% 0.20/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.20/0.58      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.58  thf('68', plain,
% 0.20/0.58      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.58         (~ (v2_funct_1 @ X17)
% 0.20/0.58          | ((k2_relset_1 @ X19 @ X18 @ X17) != (X18))
% 0.20/0.58          | (v1_funct_1 @ (k2_funct_1 @ X17))
% 0.20/0.58          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X18)))
% 0.20/0.58          | ~ (v1_funct_2 @ X17 @ X19 @ X18)
% 0.20/0.58          | ~ (v1_funct_1 @ X17))),
% 0.20/0.58      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.20/0.58  thf('69', plain,
% 0.20/0.58      ((~ (v1_funct_1 @ sk_C)
% 0.20/0.58        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.20/0.58        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.20/0.58        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.20/0.58            != (k2_relat_1 @ sk_C))
% 0.20/0.58        | ~ (v2_funct_1 @ sk_C))),
% 0.20/0.58      inference('sup-', [status(thm)], ['67', '68'])).
% 0.20/0.58  thf('70', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('71', plain,
% 0.20/0.58      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.20/0.58      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.58  thf('72', plain,
% 0.20/0.58      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.20/0.58         = (k2_relat_1 @ sk_C))),
% 0.20/0.58      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.20/0.58  thf('73', plain, ((v2_funct_1 @ sk_C)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('74', plain,
% 0.20/0.58      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.20/0.58        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.20/0.58      inference('demod', [status(thm)], ['69', '70', '71', '72', '73'])).
% 0.20/0.58  thf('75', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.20/0.58      inference('simplify', [status(thm)], ['74'])).
% 0.20/0.58  thf('76', plain,
% 0.20/0.58      (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58         (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.20/0.58         (k2_funct_1 @ sk_C)) = (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))),
% 0.20/0.58      inference('demod', [status(thm)], ['66', '75'])).
% 0.20/0.58  thf('77', plain,
% 0.20/0.58      (![X20 : $i]:
% 0.20/0.58         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.20/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.58  thf('78', plain,
% 0.20/0.58      (![X20 : $i]:
% 0.20/0.58         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.20/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.58  thf('79', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_C @ 
% 0.20/0.58        (k1_zfmisc_1 @ 
% 0.20/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('80', plain,
% 0.20/0.58      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.58         (((k2_relset_1 @ X22 @ X21 @ X23) != (X21))
% 0.20/0.58          | ~ (v2_funct_1 @ X23)
% 0.20/0.58          | ((k2_tops_2 @ X22 @ X21 @ X23) = (k2_funct_1 @ X23))
% 0.20/0.58          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21)))
% 0.20/0.58          | ~ (v1_funct_2 @ X23 @ X22 @ X21)
% 0.20/0.58          | ~ (v1_funct_1 @ X23))),
% 0.20/0.58      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.20/0.58  thf('81', plain,
% 0.20/0.58      ((~ (v1_funct_1 @ sk_C)
% 0.20/0.58        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.20/0.58        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.20/0.58            = (k2_funct_1 @ sk_C))
% 0.20/0.58        | ~ (v2_funct_1 @ sk_C)
% 0.20/0.58        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.20/0.58            != (u1_struct_0 @ sk_B)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['79', '80'])).
% 0.20/0.58  thf('82', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('83', plain,
% 0.20/0.58      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('84', plain, ((v2_funct_1 @ sk_C)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('85', plain,
% 0.20/0.58      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.20/0.58         = (k2_relat_1 @ sk_C))),
% 0.20/0.58      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.58  thf('86', plain,
% 0.20/0.58      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.20/0.58          = (k2_funct_1 @ sk_C))
% 0.20/0.58        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.20/0.58      inference('demod', [status(thm)], ['81', '82', '83', '84', '85'])).
% 0.20/0.58  thf('87', plain,
% 0.20/0.58      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.20/0.58        | ~ (l1_struct_0 @ sk_B)
% 0.20/0.58        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.20/0.58            = (k2_funct_1 @ sk_C)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['78', '86'])).
% 0.20/0.58  thf('88', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.20/0.58      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.58  thf('89', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('90', plain,
% 0.20/0.58      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.20/0.58        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.20/0.58            = (k2_funct_1 @ sk_C)))),
% 0.20/0.58      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.20/0.58  thf('91', plain,
% 0.20/0.58      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.20/0.58         = (k2_funct_1 @ sk_C))),
% 0.20/0.58      inference('simplify', [status(thm)], ['90'])).
% 0.20/0.58  thf('92', plain,
% 0.20/0.58      ((((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58          (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.20/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.20/0.58          != (k6_partfun1 @ 
% 0.20/0.58              (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))))
% 0.20/0.58         <= (~
% 0.20/0.58             (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58                (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.20/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.20/0.58                = (k6_partfun1 @ 
% 0.20/0.58                   (k1_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.58                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.20/0.58      inference('split', [status(esa)], ['3'])).
% 0.20/0.58  thf('93', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_C @ 
% 0.20/0.58        (k1_zfmisc_1 @ 
% 0.20/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.58       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.58  thf('94', plain,
% 0.20/0.58      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.58         (((k1_relset_1 @ X5 @ X6 @ X4) = (k1_relat_1 @ X4))
% 0.20/0.58          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.20/0.58      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.58  thf('95', plain,
% 0.20/0.58      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.20/0.58         = (k1_relat_1 @ sk_C))),
% 0.20/0.58      inference('sup-', [status(thm)], ['93', '94'])).
% 0.20/0.58  thf('96', plain, (![X16 : $i]: ((k6_partfun1 @ X16) = (k6_relat_1 @ X16))),
% 0.20/0.58      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.58  thf('97', plain,
% 0.20/0.58      ((((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58          (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.20/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.20/0.58          != (k6_relat_1 @ (k1_relat_1 @ sk_C))))
% 0.20/0.58         <= (~
% 0.20/0.58             (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58                (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.20/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.20/0.58                = (k6_partfun1 @ 
% 0.20/0.58                   (k1_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.58                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.20/0.58      inference('demod', [status(thm)], ['92', '95', '96'])).
% 0.20/0.58  thf('98', plain,
% 0.20/0.58      ((((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58          (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.20/0.58          (k2_funct_1 @ sk_C)) != (k6_relat_1 @ (k1_relat_1 @ sk_C))))
% 0.20/0.58         <= (~
% 0.20/0.58             (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58                (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.20/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.20/0.58                = (k6_partfun1 @ 
% 0.20/0.58                   (k1_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.58                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['91', '97'])).
% 0.20/0.58  thf('99', plain,
% 0.20/0.58      (((((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58           (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.20/0.58           (k2_funct_1 @ sk_C)) != (k6_relat_1 @ (k1_relat_1 @ sk_C)))
% 0.20/0.58         | ~ (l1_struct_0 @ sk_B)))
% 0.20/0.58         <= (~
% 0.20/0.58             (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58                (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.20/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.20/0.58                = (k6_partfun1 @ 
% 0.20/0.58                   (k1_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.58                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['77', '98'])).
% 0.20/0.58  thf('100', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.20/0.58      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.58  thf('101', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('102', plain,
% 0.20/0.58      ((((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58          (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.20/0.58          (k2_funct_1 @ sk_C)) != (k6_relat_1 @ (k1_relat_1 @ sk_C))))
% 0.20/0.58         <= (~
% 0.20/0.58             (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58                (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.20/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.20/0.58                = (k6_partfun1 @ 
% 0.20/0.58                   (k1_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.58                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.20/0.58      inference('demod', [status(thm)], ['99', '100', '101'])).
% 0.20/0.58  thf('103', plain,
% 0.20/0.58      ((((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.20/0.58          != (k6_relat_1 @ (k1_relat_1 @ sk_C))))
% 0.20/0.58         <= (~
% 0.20/0.58             (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58                (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.20/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.20/0.58                = (k6_partfun1 @ 
% 0.20/0.58                   (k1_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.58                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['76', '102'])).
% 0.20/0.58  thf('104', plain,
% 0.20/0.58      (((((k6_relat_1 @ (k1_relat_1 @ sk_C))
% 0.20/0.58           != (k6_relat_1 @ (k1_relat_1 @ sk_C)))
% 0.20/0.58         | ~ (v1_relat_1 @ sk_C)
% 0.20/0.58         | ~ (v1_funct_1 @ sk_C)
% 0.20/0.58         | ~ (v2_funct_1 @ sk_C)))
% 0.20/0.58         <= (~
% 0.20/0.58             (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58                (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.20/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.20/0.58                = (k6_partfun1 @ 
% 0.20/0.58                   (k1_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.58                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['51', '103'])).
% 0.20/0.58  thf('105', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_C @ 
% 0.20/0.58        (k1_zfmisc_1 @ 
% 0.20/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(cc1_relset_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.58       ( v1_relat_1 @ C ) ))).
% 0.20/0.58  thf('106', plain,
% 0.20/0.58      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.58         ((v1_relat_1 @ X1)
% 0.20/0.58          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3))))),
% 0.20/0.58      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.58  thf('107', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.58      inference('sup-', [status(thm)], ['105', '106'])).
% 0.20/0.58  thf('108', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('109', plain, ((v2_funct_1 @ sk_C)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('110', plain,
% 0.20/0.58      ((((k6_relat_1 @ (k1_relat_1 @ sk_C))
% 0.20/0.58          != (k6_relat_1 @ (k1_relat_1 @ sk_C))))
% 0.20/0.58         <= (~
% 0.20/0.58             (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58                (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.20/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.20/0.58                = (k6_partfun1 @ 
% 0.20/0.58                   (k1_relset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.58                    (u1_struct_0 @ sk_B) @ sk_C)))))),
% 0.20/0.58      inference('demod', [status(thm)], ['104', '107', '108', '109'])).
% 0.20/0.58  thf('111', plain,
% 0.20/0.58      ((((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58          (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.20/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.20/0.58          = (k6_partfun1 @ 
% 0.20/0.58             (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))))),
% 0.20/0.58      inference('simplify', [status(thm)], ['110'])).
% 0.20/0.58  thf('112', plain,
% 0.20/0.58      (~
% 0.20/0.58       (((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.58          (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.20/0.58          sk_C)
% 0.20/0.58          = (k6_partfun1 @ 
% 0.20/0.58             (k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))) | 
% 0.20/0.58       ~
% 0.20/0.58       (((k1_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58          (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.20/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.20/0.58          = (k6_partfun1 @ 
% 0.20/0.58             (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))))),
% 0.20/0.58      inference('split', [status(esa)], ['3'])).
% 0.20/0.58  thf('113', plain,
% 0.20/0.58      (~
% 0.20/0.58       (((k1_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.58          (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.20/0.58          sk_C)
% 0.20/0.58          = (k6_partfun1 @ 
% 0.20/0.58             (k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))))),
% 0.20/0.58      inference('sat_resolution*', [status(thm)], ['111', '112'])).
% 0.20/0.58  thf('114', plain,
% 0.20/0.58      (((k1_partfun1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.58         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ (k2_funct_1 @ sk_C) @ 
% 0.20/0.58         sk_C) != (k6_relat_1 @ (k2_relat_1 @ sk_C)))),
% 0.20/0.58      inference('simpl_trail', [status(thm)], ['50', '113'])).
% 0.20/0.58  thf('115', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_C @ 
% 0.20/0.58        (k1_zfmisc_1 @ 
% 0.20/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('116', plain,
% 0.20/0.58      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.20/0.58        (k1_zfmisc_1 @ 
% 0.20/0.58         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.58      inference('simplify', [status(thm)], ['59'])).
% 0.20/0.58  thf('117', plain,
% 0.20/0.58      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.58         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.20/0.58          | ~ (v1_funct_1 @ X10)
% 0.20/0.58          | ~ (v1_funct_1 @ X13)
% 0.20/0.58          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.20/0.58          | ((k1_partfun1 @ X11 @ X12 @ X14 @ X15 @ X10 @ X13)
% 0.20/0.58              = (k5_relat_1 @ X10 @ X13)))),
% 0.20/0.58      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.20/0.58  thf('118', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.58         (((k1_partfun1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ X2 @ 
% 0.20/0.58            X1 @ (k2_funct_1 @ sk_C) @ X0)
% 0.20/0.58            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))
% 0.20/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.20/0.58          | ~ (v1_funct_1 @ X0)
% 0.20/0.58          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['116', '117'])).
% 0.20/0.58  thf('119', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.20/0.58      inference('simplify', [status(thm)], ['74'])).
% 0.20/0.58  thf('120', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.58         (((k1_partfun1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ X2 @ 
% 0.20/0.58            X1 @ (k2_funct_1 @ sk_C) @ X0)
% 0.20/0.58            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))
% 0.20/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.20/0.58          | ~ (v1_funct_1 @ X0))),
% 0.20/0.58      inference('demod', [status(thm)], ['118', '119'])).
% 0.20/0.58  thf('121', plain,
% 0.20/0.58      ((~ (v1_funct_1 @ sk_C)
% 0.20/0.58        | ((k1_partfun1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.58            (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.58            (k2_funct_1 @ sk_C) @ sk_C)
% 0.20/0.58            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['115', '120'])).
% 0.20/0.58  thf('122', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('123', plain,
% 0.20/0.58      (((k1_partfun1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.58         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ (k2_funct_1 @ sk_C) @ 
% 0.20/0.58         sk_C) = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))),
% 0.20/0.58      inference('demod', [status(thm)], ['121', '122'])).
% 0.20/0.58  thf('124', plain,
% 0.20/0.58      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.20/0.58         != (k6_relat_1 @ (k2_relat_1 @ sk_C)))),
% 0.20/0.58      inference('demod', [status(thm)], ['114', '123'])).
% 0.20/0.58  thf('125', plain,
% 0.20/0.58      ((((k6_relat_1 @ (k2_relat_1 @ sk_C))
% 0.20/0.58          != (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.20/0.58        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.58        | ~ (v2_funct_1 @ sk_C))),
% 0.20/0.58      inference('sup-', [status(thm)], ['0', '124'])).
% 0.20/0.58  thf('126', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.58      inference('sup-', [status(thm)], ['105', '106'])).
% 0.20/0.58  thf('127', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('128', plain, ((v2_funct_1 @ sk_C)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('129', plain,
% 0.20/0.58      (((k6_relat_1 @ (k2_relat_1 @ sk_C))
% 0.20/0.58         != (k6_relat_1 @ (k2_relat_1 @ sk_C)))),
% 0.20/0.58      inference('demod', [status(thm)], ['125', '126', '127', '128'])).
% 0.20/0.58  thf('130', plain, ($false), inference('simplify', [status(thm)], ['129'])).
% 0.20/0.58  
% 0.20/0.58  % SZS output end Refutation
% 0.20/0.58  
% 0.20/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
