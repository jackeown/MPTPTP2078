%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bfTNL8xwUn

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:00 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  202 ( 772 expanded)
%              Number of leaves         :   38 ( 241 expanded)
%              Depth                    :   27
%              Number of atoms          : 2187 (18761 expanded)
%              Number of equality atoms :  131 ( 938 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('1',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('3',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('4',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X20: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X20 ) @ ( k2_relat_1 @ X20 ) ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X20: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X20 ) @ ( k2_relat_1 @ X20 ) ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('16',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X20: $i] :
      ( ( v1_funct_2 @ X20 @ ( k1_relat_1 @ X20 ) @ ( k2_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('19',plain,(
    ! [X20: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X20 ) @ ( k2_relat_1 @ X20 ) ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

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

thf('20',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X23 @ X25 )
       != X23 )
      | ~ ( v2_funct_1 @ X25 )
      | ( ( k2_tops_2 @ X24 @ X23 @ X25 )
        = ( k2_funct_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X24 @ X23 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('27',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('28',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('29',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('30',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
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

thf('31',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf('37',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','38'])).

thf('40',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','41'])).

thf('43',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('47',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('51',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('56',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( v1_partfun1 @ X15 @ X16 )
      | ~ ( v1_funct_2 @ X15 @ X16 @ X17 )
      | ~ ( v1_funct_1 @ X15 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('57',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('60',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58','63'])).

thf('65',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('66',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('68',plain,(
    ! [X22: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('69',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['66','73'])).

thf('75',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['50','74'])).

thf('76',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('78',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_partfun1 @ X19 @ X18 )
      | ( ( k1_relat_1 @ X19 )
        = X18 )
      | ~ ( v4_relat_1 @ X19 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('79',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('82',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('83',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('84',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('86',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('90',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('91',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['79','84','91'])).

thf('93',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['79','84','91'])).

thf('94',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('95',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['79','84','91'])).

thf('96',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','49','92','93','94','95'])).

thf('97',plain,
    ( ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
       != ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','96'])).

thf('98',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['82','83'])).

thf('100',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['97','98','99','100'])).

thf('102',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('104',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relset_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) @ ( k2_funct_1 @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('107',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('108',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('109',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('110',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['31'])).

thf('111',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['108','113'])).

thf('115',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['107','116'])).

thf('118',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('121',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['79','84','91'])).

thf('122',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['66','73'])).

thf('123',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_partfun1 @ X19 @ X18 )
      | ( ( k1_relat_1 @ X19 )
        = X18 )
      | ~ ( v4_relat_1 @ X19 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('124',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['82','83'])).

thf('126',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('128',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['124','125','128'])).

thf('130',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('131',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('132',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['119','120','121','129','130','131'])).

thf('133',plain,
    ( ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['106','132'])).

thf('134',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['82','83'])).

thf('136',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['133','134','135','136'])).

thf('138',plain,
    ( ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['105','137'])).

thf('139',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['82','83'])).

thf('142',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['138','139','140','141'])).

thf('143',plain,
    ( ( ( ( k2_relat_1 @ sk_C )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['102','142'])).

thf('144',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['82','83'])).

thf('145',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['143','144','145','146'])).

thf('148',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['31'])).

thf('150',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['148','149'])).

thf('151',plain,(
    ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['101','150'])).

thf('152',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','151'])).

thf('153',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['82','83'])).

thf('156',plain,(
    ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['152','153','154','155'])).

thf('157',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','156'])).

thf('158',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['82','83'])).

thf('159',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['157','158','159','160'])).

thf('162',plain,(
    $false ),
    inference(simplify,[status(thm)],['161'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bfTNL8xwUn
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:07:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.42/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.61  % Solved by: fo/fo7.sh
% 0.42/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.61  % done 253 iterations in 0.134s
% 0.42/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.61  % SZS output start Refutation
% 0.42/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.42/0.61  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.42/0.61  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.42/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.42/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.42/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.42/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.42/0.61  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.42/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.42/0.61  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.42/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.42/0.61  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.42/0.61  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.42/0.61  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.42/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.42/0.61  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.42/0.61  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.42/0.61  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.42/0.61  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.42/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.42/0.61  thf(t55_funct_1, axiom,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.42/0.61       ( ( v2_funct_1 @ A ) =>
% 0.42/0.61         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.42/0.61           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.42/0.61  thf('0', plain,
% 0.42/0.61      (![X5 : $i]:
% 0.42/0.61         (~ (v2_funct_1 @ X5)
% 0.42/0.61          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.42/0.61          | ~ (v1_funct_1 @ X5)
% 0.42/0.61          | ~ (v1_relat_1 @ X5))),
% 0.42/0.61      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.42/0.61  thf('1', plain,
% 0.42/0.61      (![X5 : $i]:
% 0.42/0.61         (~ (v2_funct_1 @ X5)
% 0.42/0.61          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.42/0.61          | ~ (v1_funct_1 @ X5)
% 0.42/0.61          | ~ (v1_relat_1 @ X5))),
% 0.42/0.61      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.42/0.61  thf(dt_k2_funct_1, axiom,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.42/0.61       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.42/0.61         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.42/0.61  thf('2', plain,
% 0.42/0.61      (![X4 : $i]:
% 0.42/0.61         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.42/0.61          | ~ (v1_funct_1 @ X4)
% 0.42/0.61          | ~ (v1_relat_1 @ X4))),
% 0.42/0.61      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.42/0.61  thf('3', plain,
% 0.42/0.61      (![X4 : $i]:
% 0.42/0.61         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.42/0.61          | ~ (v1_funct_1 @ X4)
% 0.42/0.61          | ~ (v1_relat_1 @ X4))),
% 0.42/0.61      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.42/0.61  thf('4', plain,
% 0.42/0.61      (![X5 : $i]:
% 0.42/0.61         (~ (v2_funct_1 @ X5)
% 0.42/0.61          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 0.42/0.61          | ~ (v1_funct_1 @ X5)
% 0.42/0.61          | ~ (v1_relat_1 @ X5))),
% 0.42/0.61      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.42/0.61  thf(t3_funct_2, axiom,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.42/0.61       ( ( v1_funct_1 @ A ) & 
% 0.42/0.61         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.42/0.61         ( m1_subset_1 @
% 0.42/0.61           A @ 
% 0.42/0.61           ( k1_zfmisc_1 @
% 0.42/0.61             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.42/0.61  thf('5', plain,
% 0.42/0.61      (![X20 : $i]:
% 0.42/0.61         ((m1_subset_1 @ X20 @ 
% 0.42/0.61           (k1_zfmisc_1 @ 
% 0.42/0.61            (k2_zfmisc_1 @ (k1_relat_1 @ X20) @ (k2_relat_1 @ X20))))
% 0.42/0.61          | ~ (v1_funct_1 @ X20)
% 0.42/0.61          | ~ (v1_relat_1 @ X20))),
% 0.42/0.61      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.42/0.61  thf('6', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.42/0.61           (k1_zfmisc_1 @ 
% 0.42/0.61            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 0.42/0.61          | ~ (v1_relat_1 @ X0)
% 0.42/0.61          | ~ (v1_funct_1 @ X0)
% 0.42/0.61          | ~ (v2_funct_1 @ X0)
% 0.42/0.61          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.42/0.61          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 0.42/0.61      inference('sup+', [status(thm)], ['4', '5'])).
% 0.42/0.62  thf('7', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ X0)
% 0.42/0.62          | ~ (v1_funct_1 @ X0)
% 0.42/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.42/0.62          | ~ (v2_funct_1 @ X0)
% 0.42/0.62          | ~ (v1_funct_1 @ X0)
% 0.42/0.62          | ~ (v1_relat_1 @ X0)
% 0.42/0.62          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.42/0.62             (k1_zfmisc_1 @ 
% 0.42/0.62              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 0.42/0.62               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['3', '6'])).
% 0.42/0.62  thf('8', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.42/0.62           (k1_zfmisc_1 @ 
% 0.42/0.62            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 0.42/0.62          | ~ (v2_funct_1 @ X0)
% 0.42/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.42/0.62          | ~ (v1_funct_1 @ X0)
% 0.42/0.62          | ~ (v1_relat_1 @ X0))),
% 0.42/0.62      inference('simplify', [status(thm)], ['7'])).
% 0.42/0.62  thf('9', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ X0)
% 0.42/0.62          | ~ (v1_funct_1 @ X0)
% 0.42/0.62          | ~ (v1_relat_1 @ X0)
% 0.42/0.62          | ~ (v1_funct_1 @ X0)
% 0.42/0.62          | ~ (v2_funct_1 @ X0)
% 0.42/0.62          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.42/0.62             (k1_zfmisc_1 @ 
% 0.42/0.62              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 0.42/0.62               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['2', '8'])).
% 0.42/0.62  thf('10', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.42/0.62           (k1_zfmisc_1 @ 
% 0.42/0.62            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 0.42/0.62          | ~ (v2_funct_1 @ X0)
% 0.42/0.62          | ~ (v1_funct_1 @ X0)
% 0.42/0.62          | ~ (v1_relat_1 @ X0))),
% 0.42/0.62      inference('simplify', [status(thm)], ['9'])).
% 0.42/0.62  thf('11', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.42/0.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 0.42/0.62          | ~ (v1_relat_1 @ X0)
% 0.42/0.62          | ~ (v1_funct_1 @ X0)
% 0.42/0.62          | ~ (v2_funct_1 @ X0)
% 0.42/0.62          | ~ (v1_relat_1 @ X0)
% 0.42/0.62          | ~ (v1_funct_1 @ X0)
% 0.42/0.62          | ~ (v2_funct_1 @ X0))),
% 0.42/0.62      inference('sup+', [status(thm)], ['1', '10'])).
% 0.42/0.62  thf('12', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (v2_funct_1 @ X0)
% 0.42/0.62          | ~ (v1_funct_1 @ X0)
% 0.42/0.62          | ~ (v1_relat_1 @ X0)
% 0.42/0.62          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.42/0.62             (k1_zfmisc_1 @ 
% 0.42/0.62              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 0.42/0.62      inference('simplify', [status(thm)], ['11'])).
% 0.42/0.62  thf(redefinition_k2_relset_1, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.62       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.42/0.62  thf('13', plain,
% 0.42/0.62      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.42/0.62         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.42/0.62          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.42/0.62      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.42/0.62  thf('14', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ X0)
% 0.42/0.62          | ~ (v1_funct_1 @ X0)
% 0.42/0.62          | ~ (v2_funct_1 @ X0)
% 0.42/0.62          | ((k2_relset_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0) @ 
% 0.42/0.62              (k2_funct_1 @ X0)) = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['12', '13'])).
% 0.42/0.62  thf('15', plain,
% 0.42/0.62      (![X20 : $i]:
% 0.42/0.62         ((m1_subset_1 @ X20 @ 
% 0.42/0.62           (k1_zfmisc_1 @ 
% 0.42/0.62            (k2_zfmisc_1 @ (k1_relat_1 @ X20) @ (k2_relat_1 @ X20))))
% 0.42/0.62          | ~ (v1_funct_1 @ X20)
% 0.42/0.62          | ~ (v1_relat_1 @ X20))),
% 0.42/0.62      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.42/0.62  thf('16', plain,
% 0.42/0.62      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.42/0.62         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.42/0.62          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.42/0.62      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.42/0.62  thf('17', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ X0)
% 0.42/0.62          | ~ (v1_funct_1 @ X0)
% 0.42/0.62          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.42/0.62              = (k2_relat_1 @ X0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['15', '16'])).
% 0.42/0.62  thf('18', plain,
% 0.42/0.62      (![X20 : $i]:
% 0.42/0.62         ((v1_funct_2 @ X20 @ (k1_relat_1 @ X20) @ (k2_relat_1 @ X20))
% 0.42/0.62          | ~ (v1_funct_1 @ X20)
% 0.42/0.62          | ~ (v1_relat_1 @ X20))),
% 0.42/0.62      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.42/0.62  thf('19', plain,
% 0.42/0.62      (![X20 : $i]:
% 0.42/0.62         ((m1_subset_1 @ X20 @ 
% 0.42/0.62           (k1_zfmisc_1 @ 
% 0.42/0.62            (k2_zfmisc_1 @ (k1_relat_1 @ X20) @ (k2_relat_1 @ X20))))
% 0.42/0.62          | ~ (v1_funct_1 @ X20)
% 0.42/0.62          | ~ (v1_relat_1 @ X20))),
% 0.42/0.62      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.42/0.62  thf(d4_tops_2, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i]:
% 0.42/0.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.42/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.62       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.42/0.62         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.42/0.62  thf('20', plain,
% 0.42/0.62      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.42/0.62         (((k2_relset_1 @ X24 @ X23 @ X25) != (X23))
% 0.42/0.62          | ~ (v2_funct_1 @ X25)
% 0.42/0.62          | ((k2_tops_2 @ X24 @ X23 @ X25) = (k2_funct_1 @ X25))
% 0.42/0.62          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23)))
% 0.42/0.62          | ~ (v1_funct_2 @ X25 @ X24 @ X23)
% 0.42/0.62          | ~ (v1_funct_1 @ X25))),
% 0.42/0.62      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.42/0.62  thf('21', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ X0)
% 0.42/0.62          | ~ (v1_funct_1 @ X0)
% 0.42/0.62          | ~ (v1_funct_1 @ X0)
% 0.42/0.62          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.42/0.62          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.42/0.62              = (k2_funct_1 @ X0))
% 0.42/0.62          | ~ (v2_funct_1 @ X0)
% 0.42/0.62          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.42/0.62              != (k2_relat_1 @ X0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['19', '20'])).
% 0.42/0.62  thf('22', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.42/0.62            != (k2_relat_1 @ X0))
% 0.42/0.62          | ~ (v2_funct_1 @ X0)
% 0.42/0.62          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.42/0.62              = (k2_funct_1 @ X0))
% 0.42/0.62          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.42/0.62          | ~ (v1_funct_1 @ X0)
% 0.42/0.62          | ~ (v1_relat_1 @ X0))),
% 0.42/0.62      inference('simplify', [status(thm)], ['21'])).
% 0.42/0.62  thf('23', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ X0)
% 0.42/0.62          | ~ (v1_funct_1 @ X0)
% 0.42/0.62          | ~ (v1_relat_1 @ X0)
% 0.42/0.62          | ~ (v1_funct_1 @ X0)
% 0.42/0.62          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.42/0.62              = (k2_funct_1 @ X0))
% 0.42/0.62          | ~ (v2_funct_1 @ X0)
% 0.42/0.62          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.42/0.62              != (k2_relat_1 @ X0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['18', '22'])).
% 0.42/0.62  thf('24', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.42/0.62            != (k2_relat_1 @ X0))
% 0.42/0.62          | ~ (v2_funct_1 @ X0)
% 0.42/0.62          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.42/0.62              = (k2_funct_1 @ X0))
% 0.42/0.62          | ~ (v1_funct_1 @ X0)
% 0.42/0.62          | ~ (v1_relat_1 @ X0))),
% 0.42/0.62      inference('simplify', [status(thm)], ['23'])).
% 0.42/0.62  thf('25', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (((k2_relat_1 @ X0) != (k2_relat_1 @ X0))
% 0.42/0.62          | ~ (v1_funct_1 @ X0)
% 0.42/0.62          | ~ (v1_relat_1 @ X0)
% 0.42/0.62          | ~ (v1_relat_1 @ X0)
% 0.42/0.62          | ~ (v1_funct_1 @ X0)
% 0.42/0.62          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.42/0.62              = (k2_funct_1 @ X0))
% 0.42/0.62          | ~ (v2_funct_1 @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['17', '24'])).
% 0.42/0.62  thf('26', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (v2_funct_1 @ X0)
% 0.42/0.62          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.42/0.62              = (k2_funct_1 @ X0))
% 0.42/0.62          | ~ (v1_relat_1 @ X0)
% 0.42/0.62          | ~ (v1_funct_1 @ X0))),
% 0.42/0.62      inference('simplify', [status(thm)], ['25'])).
% 0.42/0.62  thf(d3_struct_0, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.42/0.62  thf('27', plain,
% 0.42/0.62      (![X21 : $i]:
% 0.42/0.62         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.62  thf('28', plain,
% 0.42/0.62      (![X21 : $i]:
% 0.42/0.62         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.62  thf('29', plain,
% 0.42/0.62      (![X21 : $i]:
% 0.42/0.62         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.62  thf('30', plain,
% 0.42/0.62      (![X21 : $i]:
% 0.42/0.62         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.62  thf(t62_tops_2, conjecture,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( l1_struct_0 @ A ) =>
% 0.42/0.62       ( ![B:$i]:
% 0.42/0.62         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.42/0.62           ( ![C:$i]:
% 0.42/0.62             ( ( ( v1_funct_1 @ C ) & 
% 0.42/0.62                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.42/0.62                 ( m1_subset_1 @
% 0.42/0.62                   C @ 
% 0.42/0.62                   ( k1_zfmisc_1 @
% 0.42/0.62                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.42/0.62               ( ( ( ( k2_relset_1 @
% 0.42/0.62                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.42/0.62                     ( k2_struct_0 @ B ) ) & 
% 0.42/0.62                   ( v2_funct_1 @ C ) ) =>
% 0.42/0.62                 ( ( ( k1_relset_1 @
% 0.42/0.62                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.42/0.62                       ( k2_tops_2 @
% 0.42/0.62                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.42/0.62                     ( k2_struct_0 @ B ) ) & 
% 0.42/0.62                   ( ( k2_relset_1 @
% 0.42/0.62                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.42/0.62                       ( k2_tops_2 @
% 0.42/0.62                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.42/0.62                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.42/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.62    (~( ![A:$i]:
% 0.42/0.62        ( ( l1_struct_0 @ A ) =>
% 0.42/0.62          ( ![B:$i]:
% 0.42/0.62            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.42/0.62              ( ![C:$i]:
% 0.42/0.62                ( ( ( v1_funct_1 @ C ) & 
% 0.42/0.62                    ( v1_funct_2 @
% 0.42/0.62                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.42/0.62                    ( m1_subset_1 @
% 0.42/0.62                      C @ 
% 0.42/0.62                      ( k1_zfmisc_1 @
% 0.42/0.62                        ( k2_zfmisc_1 @
% 0.42/0.62                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.42/0.62                  ( ( ( ( k2_relset_1 @
% 0.42/0.62                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.42/0.62                        ( k2_struct_0 @ B ) ) & 
% 0.42/0.62                      ( v2_funct_1 @ C ) ) =>
% 0.42/0.62                    ( ( ( k1_relset_1 @
% 0.42/0.62                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.42/0.62                          ( k2_tops_2 @
% 0.42/0.62                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.42/0.62                        ( k2_struct_0 @ B ) ) & 
% 0.42/0.62                      ( ( k2_relset_1 @
% 0.42/0.62                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.42/0.62                          ( k2_tops_2 @
% 0.42/0.62                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.42/0.62                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.42/0.62    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.42/0.62  thf('31', plain,
% 0.42/0.62      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62          != (k2_struct_0 @ sk_B))
% 0.42/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62            != (k2_struct_0 @ sk_A)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('32', plain,
% 0.42/0.62      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62          != (k2_struct_0 @ sk_A)))
% 0.42/0.62         <= (~
% 0.42/0.62             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62                = (k2_struct_0 @ sk_A))))),
% 0.42/0.62      inference('split', [status(esa)], ['31'])).
% 0.42/0.62  thf('33', plain,
% 0.42/0.62      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62           != (k2_struct_0 @ sk_A))
% 0.42/0.62         | ~ (l1_struct_0 @ sk_B)))
% 0.42/0.62         <= (~
% 0.42/0.62             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62                = (k2_struct_0 @ sk_A))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['30', '32'])).
% 0.42/0.62  thf('34', plain, ((l1_struct_0 @ sk_B)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('35', plain,
% 0.42/0.62      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62          != (k2_struct_0 @ sk_A)))
% 0.42/0.62         <= (~
% 0.42/0.62             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62                = (k2_struct_0 @ sk_A))))),
% 0.42/0.62      inference('demod', [status(thm)], ['33', '34'])).
% 0.42/0.62  thf('36', plain,
% 0.42/0.62      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.42/0.62           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62           != (k2_struct_0 @ sk_A))
% 0.42/0.62         | ~ (l1_struct_0 @ sk_A)))
% 0.42/0.62         <= (~
% 0.42/0.62             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62                = (k2_struct_0 @ sk_A))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['29', '35'])).
% 0.42/0.62  thf('37', plain, ((l1_struct_0 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('38', plain,
% 0.42/0.62      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.42/0.62          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62          != (k2_struct_0 @ sk_A)))
% 0.42/0.62         <= (~
% 0.42/0.62             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62                = (k2_struct_0 @ sk_A))))),
% 0.42/0.62      inference('demod', [status(thm)], ['36', '37'])).
% 0.42/0.62  thf('39', plain,
% 0.42/0.62      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.42/0.62           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62           != (k2_struct_0 @ sk_A))
% 0.42/0.62         | ~ (l1_struct_0 @ sk_A)))
% 0.42/0.62         <= (~
% 0.42/0.62             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62                = (k2_struct_0 @ sk_A))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['28', '38'])).
% 0.42/0.62  thf('40', plain, ((l1_struct_0 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('41', plain,
% 0.42/0.62      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.42/0.62          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62          != (k2_struct_0 @ sk_A)))
% 0.42/0.62         <= (~
% 0.42/0.62             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62                = (k2_struct_0 @ sk_A))))),
% 0.42/0.62      inference('demod', [status(thm)], ['39', '40'])).
% 0.42/0.62  thf('42', plain,
% 0.42/0.62      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.42/0.62           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62           != (k2_struct_0 @ sk_A))
% 0.42/0.62         | ~ (l1_struct_0 @ sk_B)))
% 0.42/0.62         <= (~
% 0.42/0.62             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62                = (k2_struct_0 @ sk_A))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['27', '41'])).
% 0.42/0.62  thf('43', plain, ((l1_struct_0 @ sk_B)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('44', plain,
% 0.42/0.62      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.42/0.62          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62          != (k2_struct_0 @ sk_A)))
% 0.42/0.62         <= (~
% 0.42/0.62             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62                = (k2_struct_0 @ sk_A))))),
% 0.42/0.62      inference('demod', [status(thm)], ['42', '43'])).
% 0.42/0.62  thf('45', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_C @ 
% 0.42/0.62        (k1_zfmisc_1 @ 
% 0.42/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('46', plain,
% 0.42/0.62      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.42/0.62         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.42/0.62          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.42/0.62      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.42/0.62  thf('47', plain,
% 0.42/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.42/0.62         = (k2_relat_1 @ sk_C))),
% 0.42/0.62      inference('sup-', [status(thm)], ['45', '46'])).
% 0.42/0.62  thf('48', plain,
% 0.42/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.42/0.62         = (k2_struct_0 @ sk_B))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('49', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.42/0.62      inference('sup+', [status(thm)], ['47', '48'])).
% 0.42/0.62  thf('50', plain,
% 0.42/0.62      (![X21 : $i]:
% 0.42/0.62         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.62  thf('51', plain,
% 0.42/0.62      (![X21 : $i]:
% 0.42/0.62         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.62  thf('52', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_C @ 
% 0.42/0.62        (k1_zfmisc_1 @ 
% 0.42/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('53', plain,
% 0.42/0.62      (((m1_subset_1 @ sk_C @ 
% 0.42/0.62         (k1_zfmisc_1 @ 
% 0.42/0.62          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.42/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.42/0.62      inference('sup+', [status(thm)], ['51', '52'])).
% 0.42/0.62  thf('54', plain, ((l1_struct_0 @ sk_B)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('55', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_C @ 
% 0.42/0.62        (k1_zfmisc_1 @ 
% 0.42/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.42/0.62      inference('demod', [status(thm)], ['53', '54'])).
% 0.42/0.62  thf(cc5_funct_2, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.42/0.62       ( ![C:$i]:
% 0.42/0.62         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.62           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.42/0.62             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.42/0.62  thf('56', plain,
% 0.42/0.62      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.42/0.62         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.42/0.62          | (v1_partfun1 @ X15 @ X16)
% 0.42/0.62          | ~ (v1_funct_2 @ X15 @ X16 @ X17)
% 0.42/0.62          | ~ (v1_funct_1 @ X15)
% 0.42/0.62          | (v1_xboole_0 @ X17))),
% 0.42/0.62      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.42/0.62  thf('57', plain,
% 0.42/0.62      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.42/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.42/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.42/0.62        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['55', '56'])).
% 0.42/0.62  thf('58', plain, ((v1_funct_1 @ sk_C)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('59', plain,
% 0.42/0.62      (![X21 : $i]:
% 0.42/0.62         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.62  thf('60', plain,
% 0.42/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('61', plain,
% 0.42/0.62      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.42/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.42/0.62      inference('sup+', [status(thm)], ['59', '60'])).
% 0.42/0.62  thf('62', plain, ((l1_struct_0 @ sk_B)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('63', plain,
% 0.42/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.42/0.62      inference('demod', [status(thm)], ['61', '62'])).
% 0.42/0.62  thf('64', plain,
% 0.42/0.62      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.42/0.62        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('demod', [status(thm)], ['57', '58', '63'])).
% 0.42/0.62  thf('65', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.42/0.62      inference('sup+', [status(thm)], ['47', '48'])).
% 0.42/0.62  thf('66', plain,
% 0.42/0.62      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.42/0.62        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('demod', [status(thm)], ['64', '65'])).
% 0.42/0.62  thf('67', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.42/0.62      inference('sup+', [status(thm)], ['47', '48'])).
% 0.42/0.62  thf(fc5_struct_0, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.42/0.62       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.42/0.62  thf('68', plain,
% 0.42/0.62      (![X22 : $i]:
% 0.42/0.62         (~ (v1_xboole_0 @ (k2_struct_0 @ X22))
% 0.42/0.62          | ~ (l1_struct_0 @ X22)
% 0.42/0.62          | (v2_struct_0 @ X22))),
% 0.42/0.62      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.42/0.62  thf('69', plain,
% 0.42/0.62      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.42/0.62        | (v2_struct_0 @ sk_B)
% 0.42/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.42/0.62      inference('sup-', [status(thm)], ['67', '68'])).
% 0.42/0.62  thf('70', plain, ((l1_struct_0 @ sk_B)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('71', plain,
% 0.42/0.62      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.42/0.62      inference('demod', [status(thm)], ['69', '70'])).
% 0.42/0.62  thf('72', plain, (~ (v2_struct_0 @ sk_B)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('73', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.42/0.62      inference('clc', [status(thm)], ['71', '72'])).
% 0.42/0.62  thf('74', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.42/0.62      inference('clc', [status(thm)], ['66', '73'])).
% 0.42/0.62  thf('75', plain,
% 0.42/0.62      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.42/0.62      inference('sup+', [status(thm)], ['50', '74'])).
% 0.42/0.62  thf('76', plain, ((l1_struct_0 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('77', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.42/0.62      inference('demod', [status(thm)], ['75', '76'])).
% 0.42/0.62  thf(d4_partfun1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.42/0.62       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.42/0.62  thf('78', plain,
% 0.42/0.62      (![X18 : $i, X19 : $i]:
% 0.42/0.62         (~ (v1_partfun1 @ X19 @ X18)
% 0.42/0.62          | ((k1_relat_1 @ X19) = (X18))
% 0.42/0.62          | ~ (v4_relat_1 @ X19 @ X18)
% 0.42/0.62          | ~ (v1_relat_1 @ X19))),
% 0.42/0.62      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.42/0.62  thf('79', plain,
% 0.42/0.62      ((~ (v1_relat_1 @ sk_C)
% 0.42/0.62        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.42/0.62        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['77', '78'])).
% 0.42/0.62  thf('80', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_C @ 
% 0.42/0.62        (k1_zfmisc_1 @ 
% 0.42/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(cc2_relat_1, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( v1_relat_1 @ A ) =>
% 0.42/0.62       ( ![B:$i]:
% 0.42/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.42/0.62  thf('81', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.42/0.62          | (v1_relat_1 @ X0)
% 0.42/0.62          | ~ (v1_relat_1 @ X1))),
% 0.42/0.62      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.42/0.62  thf('82', plain,
% 0.42/0.62      ((~ (v1_relat_1 @ 
% 0.42/0.62           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.42/0.62        | (v1_relat_1 @ sk_C))),
% 0.42/0.62      inference('sup-', [status(thm)], ['80', '81'])).
% 0.42/0.62  thf(fc6_relat_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.42/0.62  thf('83', plain,
% 0.42/0.62      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.42/0.62      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.42/0.62  thf('84', plain, ((v1_relat_1 @ sk_C)),
% 0.42/0.62      inference('demod', [status(thm)], ['82', '83'])).
% 0.42/0.62  thf('85', plain,
% 0.42/0.62      (![X21 : $i]:
% 0.42/0.62         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.62  thf('86', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_C @ 
% 0.42/0.62        (k1_zfmisc_1 @ 
% 0.42/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('87', plain,
% 0.42/0.62      (((m1_subset_1 @ sk_C @ 
% 0.42/0.62         (k1_zfmisc_1 @ 
% 0.42/0.62          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.42/0.62        | ~ (l1_struct_0 @ sk_A))),
% 0.42/0.62      inference('sup+', [status(thm)], ['85', '86'])).
% 0.42/0.62  thf('88', plain, ((l1_struct_0 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('89', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_C @ 
% 0.42/0.62        (k1_zfmisc_1 @ 
% 0.42/0.62         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.42/0.62      inference('demod', [status(thm)], ['87', '88'])).
% 0.42/0.62  thf(cc2_relset_1, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.62       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.42/0.62  thf('90', plain,
% 0.42/0.62      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.42/0.62         ((v4_relat_1 @ X6 @ X7)
% 0.42/0.62          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.42/0.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.42/0.62  thf('91', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['89', '90'])).
% 0.42/0.62  thf('92', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.42/0.62      inference('demod', [status(thm)], ['79', '84', '91'])).
% 0.42/0.62  thf('93', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.42/0.62      inference('demod', [status(thm)], ['79', '84', '91'])).
% 0.42/0.62  thf('94', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.42/0.62      inference('sup+', [status(thm)], ['47', '48'])).
% 0.42/0.62  thf('95', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.42/0.62      inference('demod', [status(thm)], ['79', '84', '91'])).
% 0.42/0.62  thf('96', plain,
% 0.42/0.62      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.42/0.62          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.42/0.62          != (k1_relat_1 @ sk_C)))
% 0.42/0.62         <= (~
% 0.42/0.62             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62                = (k2_struct_0 @ sk_A))))),
% 0.42/0.62      inference('demod', [status(thm)], ['44', '49', '92', '93', '94', '95'])).
% 0.42/0.62  thf('97', plain,
% 0.42/0.62      (((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.42/0.62           (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.42/0.62         | ~ (v1_funct_1 @ sk_C)
% 0.42/0.62         | ~ (v1_relat_1 @ sk_C)
% 0.42/0.62         | ~ (v2_funct_1 @ sk_C)))
% 0.42/0.62         <= (~
% 0.42/0.62             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62                = (k2_struct_0 @ sk_A))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['26', '96'])).
% 0.42/0.62  thf('98', plain, ((v1_funct_1 @ sk_C)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('99', plain, ((v1_relat_1 @ sk_C)),
% 0.42/0.62      inference('demod', [status(thm)], ['82', '83'])).
% 0.42/0.62  thf('100', plain, ((v2_funct_1 @ sk_C)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('101', plain,
% 0.42/0.62      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.42/0.62          (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 0.42/0.62         <= (~
% 0.42/0.62             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62                = (k2_struct_0 @ sk_A))))),
% 0.42/0.62      inference('demod', [status(thm)], ['97', '98', '99', '100'])).
% 0.42/0.62  thf('102', plain,
% 0.42/0.62      (![X5 : $i]:
% 0.42/0.62         (~ (v2_funct_1 @ X5)
% 0.42/0.62          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 0.42/0.62          | ~ (v1_funct_1 @ X5)
% 0.42/0.62          | ~ (v1_relat_1 @ X5))),
% 0.42/0.62      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.42/0.62  thf('103', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (v2_funct_1 @ X0)
% 0.42/0.62          | ~ (v1_funct_1 @ X0)
% 0.42/0.62          | ~ (v1_relat_1 @ X0)
% 0.42/0.62          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.42/0.62             (k1_zfmisc_1 @ 
% 0.42/0.62              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 0.42/0.62      inference('simplify', [status(thm)], ['11'])).
% 0.42/0.62  thf(redefinition_k1_relset_1, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.62       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.42/0.62  thf('104', plain,
% 0.42/0.62      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.42/0.62         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.42/0.62          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.42/0.62      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.42/0.62  thf('105', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ X0)
% 0.42/0.62          | ~ (v1_funct_1 @ X0)
% 0.42/0.62          | ~ (v2_funct_1 @ X0)
% 0.42/0.62          | ((k1_relset_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0) @ 
% 0.42/0.62              (k2_funct_1 @ X0)) = (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['103', '104'])).
% 0.42/0.62  thf('106', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (v2_funct_1 @ X0)
% 0.42/0.62          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.42/0.62              = (k2_funct_1 @ X0))
% 0.42/0.62          | ~ (v1_relat_1 @ X0)
% 0.42/0.62          | ~ (v1_funct_1 @ X0))),
% 0.42/0.62      inference('simplify', [status(thm)], ['25'])).
% 0.42/0.62  thf('107', plain,
% 0.42/0.62      (![X21 : $i]:
% 0.42/0.62         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.62  thf('108', plain,
% 0.42/0.62      (![X21 : $i]:
% 0.42/0.62         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.62  thf('109', plain,
% 0.42/0.62      (![X21 : $i]:
% 0.42/0.62         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.62  thf('110', plain,
% 0.42/0.62      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62          != (k2_struct_0 @ sk_B)))
% 0.42/0.62         <= (~
% 0.42/0.62             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62                = (k2_struct_0 @ sk_B))))),
% 0.42/0.62      inference('split', [status(esa)], ['31'])).
% 0.42/0.62  thf('111', plain,
% 0.42/0.62      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62           != (k2_struct_0 @ sk_B))
% 0.42/0.62         | ~ (l1_struct_0 @ sk_B)))
% 0.42/0.62         <= (~
% 0.42/0.62             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62                = (k2_struct_0 @ sk_B))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['109', '110'])).
% 0.42/0.62  thf('112', plain, ((l1_struct_0 @ sk_B)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('113', plain,
% 0.42/0.62      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62          != (k2_struct_0 @ sk_B)))
% 0.42/0.62         <= (~
% 0.42/0.62             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62                = (k2_struct_0 @ sk_B))))),
% 0.42/0.62      inference('demod', [status(thm)], ['111', '112'])).
% 0.42/0.62  thf('114', plain,
% 0.42/0.62      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.42/0.62           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62           != (k2_struct_0 @ sk_B))
% 0.42/0.62         | ~ (l1_struct_0 @ sk_A)))
% 0.42/0.62         <= (~
% 0.42/0.62             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62                = (k2_struct_0 @ sk_B))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['108', '113'])).
% 0.42/0.62  thf('115', plain, ((l1_struct_0 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('116', plain,
% 0.42/0.62      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.42/0.62          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62          != (k2_struct_0 @ sk_B)))
% 0.42/0.62         <= (~
% 0.42/0.62             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62                = (k2_struct_0 @ sk_B))))),
% 0.42/0.62      inference('demod', [status(thm)], ['114', '115'])).
% 0.42/0.62  thf('117', plain,
% 0.42/0.62      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.42/0.62           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62           != (k2_struct_0 @ sk_B))
% 0.42/0.62         | ~ (l1_struct_0 @ sk_B)))
% 0.42/0.62         <= (~
% 0.42/0.62             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62                = (k2_struct_0 @ sk_B))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['107', '116'])).
% 0.42/0.62  thf('118', plain, ((l1_struct_0 @ sk_B)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('119', plain,
% 0.42/0.62      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.42/0.62          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62          != (k2_struct_0 @ sk_B)))
% 0.42/0.62         <= (~
% 0.42/0.62             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62                = (k2_struct_0 @ sk_B))))),
% 0.42/0.62      inference('demod', [status(thm)], ['117', '118'])).
% 0.42/0.62  thf('120', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.42/0.62      inference('sup+', [status(thm)], ['47', '48'])).
% 0.42/0.62  thf('121', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.42/0.62      inference('demod', [status(thm)], ['79', '84', '91'])).
% 0.42/0.62  thf('122', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.42/0.62      inference('clc', [status(thm)], ['66', '73'])).
% 0.42/0.62  thf('123', plain,
% 0.42/0.62      (![X18 : $i, X19 : $i]:
% 0.42/0.62         (~ (v1_partfun1 @ X19 @ X18)
% 0.42/0.62          | ((k1_relat_1 @ X19) = (X18))
% 0.42/0.62          | ~ (v4_relat_1 @ X19 @ X18)
% 0.42/0.62          | ~ (v1_relat_1 @ X19))),
% 0.42/0.62      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.42/0.62  thf('124', plain,
% 0.42/0.62      ((~ (v1_relat_1 @ sk_C)
% 0.42/0.62        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.42/0.62        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['122', '123'])).
% 0.42/0.62  thf('125', plain, ((v1_relat_1 @ sk_C)),
% 0.42/0.62      inference('demod', [status(thm)], ['82', '83'])).
% 0.42/0.62  thf('126', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_C @ 
% 0.42/0.62        (k1_zfmisc_1 @ 
% 0.42/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('127', plain,
% 0.42/0.62      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.42/0.62         ((v4_relat_1 @ X6 @ X7)
% 0.42/0.62          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.42/0.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.42/0.62  thf('128', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['126', '127'])).
% 0.42/0.62  thf('129', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.42/0.62      inference('demod', [status(thm)], ['124', '125', '128'])).
% 0.42/0.62  thf('130', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.42/0.62      inference('sup+', [status(thm)], ['47', '48'])).
% 0.42/0.62  thf('131', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.42/0.62      inference('sup+', [status(thm)], ['47', '48'])).
% 0.42/0.62  thf('132', plain,
% 0.42/0.62      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.42/0.62          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.42/0.62          != (k2_relat_1 @ sk_C)))
% 0.42/0.62         <= (~
% 0.42/0.62             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62                = (k2_struct_0 @ sk_B))))),
% 0.42/0.62      inference('demod', [status(thm)],
% 0.42/0.62                ['119', '120', '121', '129', '130', '131'])).
% 0.42/0.62  thf('133', plain,
% 0.42/0.62      (((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.42/0.62           (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C))
% 0.42/0.62         | ~ (v1_funct_1 @ sk_C)
% 0.42/0.62         | ~ (v1_relat_1 @ sk_C)
% 0.42/0.62         | ~ (v2_funct_1 @ sk_C)))
% 0.42/0.62         <= (~
% 0.42/0.62             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62                = (k2_struct_0 @ sk_B))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['106', '132'])).
% 0.42/0.62  thf('134', plain, ((v1_funct_1 @ sk_C)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('135', plain, ((v1_relat_1 @ sk_C)),
% 0.42/0.62      inference('demod', [status(thm)], ['82', '83'])).
% 0.42/0.62  thf('136', plain, ((v2_funct_1 @ sk_C)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('137', plain,
% 0.42/0.62      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.42/0.62          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.42/0.62         <= (~
% 0.42/0.62             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62                = (k2_struct_0 @ sk_B))))),
% 0.42/0.62      inference('demod', [status(thm)], ['133', '134', '135', '136'])).
% 0.42/0.62  thf('138', plain,
% 0.42/0.62      (((((k1_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C))
% 0.42/0.62         | ~ (v2_funct_1 @ sk_C)
% 0.42/0.62         | ~ (v1_funct_1 @ sk_C)
% 0.42/0.62         | ~ (v1_relat_1 @ sk_C)))
% 0.42/0.62         <= (~
% 0.42/0.62             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62                = (k2_struct_0 @ sk_B))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['105', '137'])).
% 0.42/0.62  thf('139', plain, ((v2_funct_1 @ sk_C)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('140', plain, ((v1_funct_1 @ sk_C)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('141', plain, ((v1_relat_1 @ sk_C)),
% 0.42/0.62      inference('demod', [status(thm)], ['82', '83'])).
% 0.42/0.62  thf('142', plain,
% 0.42/0.62      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.42/0.62         <= (~
% 0.42/0.62             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62                = (k2_struct_0 @ sk_B))))),
% 0.42/0.62      inference('demod', [status(thm)], ['138', '139', '140', '141'])).
% 0.42/0.62  thf('143', plain,
% 0.42/0.62      (((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.42/0.62         | ~ (v1_relat_1 @ sk_C)
% 0.42/0.62         | ~ (v1_funct_1 @ sk_C)
% 0.42/0.62         | ~ (v2_funct_1 @ sk_C)))
% 0.42/0.62         <= (~
% 0.42/0.62             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62                = (k2_struct_0 @ sk_B))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['102', '142'])).
% 0.42/0.62  thf('144', plain, ((v1_relat_1 @ sk_C)),
% 0.42/0.62      inference('demod', [status(thm)], ['82', '83'])).
% 0.42/0.62  thf('145', plain, ((v1_funct_1 @ sk_C)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('146', plain, ((v2_funct_1 @ sk_C)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('147', plain,
% 0.42/0.62      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.42/0.62         <= (~
% 0.42/0.62             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62                = (k2_struct_0 @ sk_B))))),
% 0.42/0.62      inference('demod', [status(thm)], ['143', '144', '145', '146'])).
% 0.42/0.62  thf('148', plain,
% 0.42/0.62      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62          = (k2_struct_0 @ sk_B)))),
% 0.42/0.62      inference('simplify', [status(thm)], ['147'])).
% 0.42/0.62  thf('149', plain,
% 0.42/0.62      (~
% 0.42/0.62       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62          = (k2_struct_0 @ sk_A))) | 
% 0.42/0.62       ~
% 0.42/0.62       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62          = (k2_struct_0 @ sk_B)))),
% 0.42/0.62      inference('split', [status(esa)], ['31'])).
% 0.42/0.62  thf('150', plain,
% 0.42/0.62      (~
% 0.42/0.62       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.62          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.42/0.62          = (k2_struct_0 @ sk_A)))),
% 0.42/0.62      inference('sat_resolution*', [status(thm)], ['148', '149'])).
% 0.42/0.62  thf('151', plain,
% 0.42/0.62      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.42/0.62         (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))),
% 0.42/0.62      inference('simpl_trail', [status(thm)], ['101', '150'])).
% 0.42/0.62  thf('152', plain,
% 0.42/0.62      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.42/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.42/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.42/0.62        | ~ (v1_relat_1 @ sk_C))),
% 0.42/0.62      inference('sup-', [status(thm)], ['14', '151'])).
% 0.42/0.62  thf('153', plain, ((v2_funct_1 @ sk_C)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('154', plain, ((v1_funct_1 @ sk_C)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('155', plain, ((v1_relat_1 @ sk_C)),
% 0.42/0.62      inference('demod', [status(thm)], ['82', '83'])).
% 0.42/0.62  thf('156', plain,
% 0.42/0.62      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))),
% 0.42/0.62      inference('demod', [status(thm)], ['152', '153', '154', '155'])).
% 0.42/0.62  thf('157', plain,
% 0.42/0.62      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 0.42/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.42/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.42/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.42/0.62      inference('sup-', [status(thm)], ['0', '156'])).
% 0.42/0.62  thf('158', plain, ((v1_relat_1 @ sk_C)),
% 0.42/0.62      inference('demod', [status(thm)], ['82', '83'])).
% 0.42/0.62  thf('159', plain, ((v1_funct_1 @ sk_C)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('160', plain, ((v2_funct_1 @ sk_C)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('161', plain, (((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))),
% 0.42/0.62      inference('demod', [status(thm)], ['157', '158', '159', '160'])).
% 0.42/0.62  thf('162', plain, ($false), inference('simplify', [status(thm)], ['161'])).
% 0.42/0.62  
% 0.42/0.62  % SZS output end Refutation
% 0.42/0.62  
% 0.42/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
