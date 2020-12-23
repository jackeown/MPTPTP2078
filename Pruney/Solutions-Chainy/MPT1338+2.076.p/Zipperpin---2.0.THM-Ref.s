%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rKe7bHrfez

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  234 (1116 expanded)
%              Number of leaves         :   38 ( 338 expanded)
%              Depth                    :   28
%              Number of atoms          : 2382 (27086 expanded)
%              Number of equality atoms :  149 (1362 expanded)
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
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
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

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relset_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) @ ( k2_funct_1 @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X20: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X20 ) @ ( k2_relat_1 @ X20 ) ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

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

thf('30',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['30'])).

thf('32',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf('36',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','37'])).

thf('39',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('43',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('47',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('52',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( v1_partfun1 @ X15 @ X16 )
      | ~ ( v1_funct_2 @ X15 @ X16 @ X17 )
      | ~ ( v1_funct_1 @ X15 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('53',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('56',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54','59'])).

thf('61',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('62',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('64',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('65',plain,(
    ! [X22: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['63','67'])).

thf('69',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','72'])).

thf('74',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['46','73'])).

thf('75',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['74','75'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('77',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_partfun1 @ X19 @ X18 )
      | ( ( k1_relat_1 @ X19 )
        = X18 )
      | ~ ( v4_relat_1 @ X19 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('78',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('81',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('82',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('83',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('85',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('89',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('90',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['78','83','90'])).

thf('92',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','72'])).

thf('93',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_partfun1 @ X19 @ X18 )
      | ( ( k1_relat_1 @ X19 )
        = X18 )
      | ~ ( v4_relat_1 @ X19 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('94',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['81','82'])).

thf('96',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('98',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['94','95','98'])).

thf('100',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('101',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('102',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','45','91','99','100','101'])).

thf('103',plain,
    ( ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','102'])).

thf('104',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['81','82'])).

thf('106',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['103','104','105','106'])).

thf('108',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('110',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('113',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('114',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['94','95','98'])).

thf('116',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
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

thf('118',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('121',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('122',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['120','125'])).

thf('127',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('130',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['78','83','90'])).

thf('132',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('135',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('136',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('141',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('142',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['139','140','141'])).

thf('143',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['134','142'])).

thf('144',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['78','83','90'])).

thf('147',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['118','119','132','133','147'])).

thf('149',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('151',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('152',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('153',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['30'])).

thf('154',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['151','156'])).

thf('158',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['150','159'])).

thf('161',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['160','161'])).

thf('163',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('164',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['94','95','98'])).

thf('165',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['78','83','90'])).

thf('166',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('167',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['78','83','90'])).

thf('168',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['162','163','164','165','166','167'])).

thf('169',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['149','168'])).

thf('170',plain,
    ( ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
       != ( k1_relat_1 @ sk_C ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['111','169'])).

thf('171',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['81','82'])).

thf('174',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['170','171','172','173'])).

thf('175',plain,
    ( ( ( ( k1_relat_1 @ sk_C )
       != ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['108','174'])).

thf('176',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['81','82'])).

thf('177',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['175','176','177','178'])).

thf('180',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['30'])).

thf('182',plain,(
    ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['180','181'])).

thf('183',plain,(
    ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['107','182'])).

thf('184',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','183'])).

thf('185',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['81','82'])).

thf('188',plain,(
    ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['184','185','186','187'])).

thf('189',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','188'])).

thf('190',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['81','82'])).

thf('191',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['189','190','191','192'])).

thf('194',plain,(
    $false ),
    inference(simplify,[status(thm)],['193'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rKe7bHrfez
% 0.15/0.34  % Computer   : n018.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 10:06:12 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.34  % Running portfolio for 600 s
% 0.15/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 273 iterations in 0.098s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.56  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.56  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.56  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.56  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.56  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.56  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.21/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.56  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.56  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.56  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.56  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.21/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.56  thf(t55_funct_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.56       ( ( v2_funct_1 @ A ) =>
% 0.21/0.56         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.21/0.56           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.21/0.56  thf('0', plain,
% 0.21/0.56      (![X5 : $i]:
% 0.21/0.56         (~ (v2_funct_1 @ X5)
% 0.21/0.56          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 0.21/0.56          | ~ (v1_funct_1 @ X5)
% 0.21/0.56          | ~ (v1_relat_1 @ X5))),
% 0.21/0.56      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.21/0.56  thf('1', plain,
% 0.21/0.56      (![X5 : $i]:
% 0.21/0.56         (~ (v2_funct_1 @ X5)
% 0.21/0.56          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.21/0.56          | ~ (v1_funct_1 @ X5)
% 0.21/0.56          | ~ (v1_relat_1 @ X5))),
% 0.21/0.56      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.21/0.56  thf(dt_k2_funct_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.56       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.21/0.56         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.21/0.56  thf('2', plain,
% 0.21/0.56      (![X4 : $i]:
% 0.21/0.56         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.21/0.56          | ~ (v1_funct_1 @ X4)
% 0.21/0.56          | ~ (v1_relat_1 @ X4))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.56  thf('3', plain,
% 0.21/0.56      (![X4 : $i]:
% 0.21/0.56         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.21/0.56          | ~ (v1_funct_1 @ X4)
% 0.21/0.56          | ~ (v1_relat_1 @ X4))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.56  thf('4', plain,
% 0.21/0.56      (![X5 : $i]:
% 0.21/0.56         (~ (v2_funct_1 @ X5)
% 0.21/0.56          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 0.21/0.56          | ~ (v1_funct_1 @ X5)
% 0.21/0.56          | ~ (v1_relat_1 @ X5))),
% 0.21/0.56      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.21/0.56  thf(t3_funct_2, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.56       ( ( v1_funct_1 @ A ) & 
% 0.21/0.56         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.21/0.56         ( m1_subset_1 @
% 0.21/0.56           A @ 
% 0.21/0.56           ( k1_zfmisc_1 @
% 0.21/0.56             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.21/0.56  thf('5', plain,
% 0.21/0.56      (![X20 : $i]:
% 0.21/0.56         ((m1_subset_1 @ X20 @ 
% 0.21/0.56           (k1_zfmisc_1 @ 
% 0.21/0.56            (k2_zfmisc_1 @ (k1_relat_1 @ X20) @ (k2_relat_1 @ X20))))
% 0.21/0.56          | ~ (v1_funct_1 @ X20)
% 0.21/0.56          | ~ (v1_relat_1 @ X20))),
% 0.21/0.56      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.21/0.56  thf('6', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.21/0.56           (k1_zfmisc_1 @ 
% 0.21/0.56            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 0.21/0.56          | ~ (v1_relat_1 @ X0)
% 0.21/0.56          | ~ (v1_funct_1 @ X0)
% 0.21/0.56          | ~ (v2_funct_1 @ X0)
% 0.21/0.56          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.21/0.56          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['4', '5'])).
% 0.21/0.56  thf('7', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (v1_relat_1 @ X0)
% 0.21/0.56          | ~ (v1_funct_1 @ X0)
% 0.21/0.56          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.56          | ~ (v2_funct_1 @ X0)
% 0.21/0.56          | ~ (v1_funct_1 @ X0)
% 0.21/0.56          | ~ (v1_relat_1 @ X0)
% 0.21/0.56          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.21/0.56             (k1_zfmisc_1 @ 
% 0.21/0.56              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 0.21/0.56               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['3', '6'])).
% 0.21/0.56  thf('8', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.21/0.56           (k1_zfmisc_1 @ 
% 0.21/0.56            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 0.21/0.56          | ~ (v2_funct_1 @ X0)
% 0.21/0.56          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.21/0.56          | ~ (v1_funct_1 @ X0)
% 0.21/0.56          | ~ (v1_relat_1 @ X0))),
% 0.21/0.56      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.56  thf('9', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (v1_relat_1 @ X0)
% 0.21/0.56          | ~ (v1_funct_1 @ X0)
% 0.21/0.56          | ~ (v1_relat_1 @ X0)
% 0.21/0.56          | ~ (v1_funct_1 @ X0)
% 0.21/0.56          | ~ (v2_funct_1 @ X0)
% 0.21/0.56          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.21/0.56             (k1_zfmisc_1 @ 
% 0.21/0.56              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 0.21/0.56               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['2', '8'])).
% 0.21/0.56  thf('10', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.21/0.56           (k1_zfmisc_1 @ 
% 0.21/0.56            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 0.21/0.56          | ~ (v2_funct_1 @ X0)
% 0.21/0.56          | ~ (v1_funct_1 @ X0)
% 0.21/0.56          | ~ (v1_relat_1 @ X0))),
% 0.21/0.56      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.56  thf('11', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.21/0.56           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 0.21/0.56          | ~ (v1_relat_1 @ X0)
% 0.21/0.56          | ~ (v1_funct_1 @ X0)
% 0.21/0.56          | ~ (v2_funct_1 @ X0)
% 0.21/0.56          | ~ (v1_relat_1 @ X0)
% 0.21/0.56          | ~ (v1_funct_1 @ X0)
% 0.21/0.56          | ~ (v2_funct_1 @ X0))),
% 0.21/0.56      inference('sup+', [status(thm)], ['1', '10'])).
% 0.21/0.56  thf('12', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (v2_funct_1 @ X0)
% 0.21/0.56          | ~ (v1_funct_1 @ X0)
% 0.21/0.56          | ~ (v1_relat_1 @ X0)
% 0.21/0.56          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.21/0.56             (k1_zfmisc_1 @ 
% 0.21/0.56              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 0.21/0.56      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.56  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.56       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.56  thf('13', plain,
% 0.21/0.56      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.56         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.21/0.56          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.21/0.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.56  thf('14', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (v1_relat_1 @ X0)
% 0.21/0.56          | ~ (v1_funct_1 @ X0)
% 0.21/0.56          | ~ (v2_funct_1 @ X0)
% 0.21/0.56          | ((k1_relset_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0) @ 
% 0.21/0.56              (k2_funct_1 @ X0)) = (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.56  thf('15', plain,
% 0.21/0.56      (![X20 : $i]:
% 0.21/0.56         ((m1_subset_1 @ X20 @ 
% 0.21/0.56           (k1_zfmisc_1 @ 
% 0.21/0.56            (k2_zfmisc_1 @ (k1_relat_1 @ X20) @ (k2_relat_1 @ X20))))
% 0.21/0.56          | ~ (v1_funct_1 @ X20)
% 0.21/0.56          | ~ (v1_relat_1 @ X20))),
% 0.21/0.56      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.21/0.56  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.56       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.56  thf('16', plain,
% 0.21/0.56      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.56         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.21/0.56          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.21/0.56      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.56  thf('17', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (v1_relat_1 @ X0)
% 0.21/0.56          | ~ (v1_funct_1 @ X0)
% 0.21/0.56          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.21/0.56              = (k2_relat_1 @ X0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.56  thf('18', plain,
% 0.21/0.56      (![X20 : $i]:
% 0.21/0.56         ((v1_funct_2 @ X20 @ (k1_relat_1 @ X20) @ (k2_relat_1 @ X20))
% 0.21/0.56          | ~ (v1_funct_1 @ X20)
% 0.21/0.56          | ~ (v1_relat_1 @ X20))),
% 0.21/0.56      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.21/0.56  thf('19', plain,
% 0.21/0.56      (![X20 : $i]:
% 0.21/0.56         ((m1_subset_1 @ X20 @ 
% 0.21/0.56           (k1_zfmisc_1 @ 
% 0.21/0.56            (k2_zfmisc_1 @ (k1_relat_1 @ X20) @ (k2_relat_1 @ X20))))
% 0.21/0.56          | ~ (v1_funct_1 @ X20)
% 0.21/0.56          | ~ (v1_relat_1 @ X20))),
% 0.21/0.56      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.21/0.56  thf(d4_tops_2, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.56       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.21/0.56         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.21/0.56  thf('20', plain,
% 0.21/0.56      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.56         (((k2_relset_1 @ X24 @ X23 @ X25) != (X23))
% 0.21/0.56          | ~ (v2_funct_1 @ X25)
% 0.21/0.56          | ((k2_tops_2 @ X24 @ X23 @ X25) = (k2_funct_1 @ X25))
% 0.21/0.56          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23)))
% 0.21/0.56          | ~ (v1_funct_2 @ X25 @ X24 @ X23)
% 0.21/0.56          | ~ (v1_funct_1 @ X25))),
% 0.21/0.56      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.21/0.56  thf('21', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (v1_relat_1 @ X0)
% 0.21/0.56          | ~ (v1_funct_1 @ X0)
% 0.21/0.56          | ~ (v1_funct_1 @ X0)
% 0.21/0.56          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.21/0.56          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.21/0.56              = (k2_funct_1 @ X0))
% 0.21/0.56          | ~ (v2_funct_1 @ X0)
% 0.21/0.56          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.21/0.56              != (k2_relat_1 @ X0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.56  thf('22', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.21/0.56            != (k2_relat_1 @ X0))
% 0.21/0.56          | ~ (v2_funct_1 @ X0)
% 0.21/0.56          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.21/0.56              = (k2_funct_1 @ X0))
% 0.21/0.56          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.21/0.56          | ~ (v1_funct_1 @ X0)
% 0.21/0.56          | ~ (v1_relat_1 @ X0))),
% 0.21/0.56      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.56  thf('23', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (v1_relat_1 @ X0)
% 0.21/0.56          | ~ (v1_funct_1 @ X0)
% 0.21/0.56          | ~ (v1_relat_1 @ X0)
% 0.21/0.56          | ~ (v1_funct_1 @ X0)
% 0.21/0.56          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.21/0.56              = (k2_funct_1 @ X0))
% 0.21/0.56          | ~ (v2_funct_1 @ X0)
% 0.21/0.56          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.21/0.56              != (k2_relat_1 @ X0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['18', '22'])).
% 0.21/0.56  thf('24', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.21/0.56            != (k2_relat_1 @ X0))
% 0.21/0.56          | ~ (v2_funct_1 @ X0)
% 0.21/0.56          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.21/0.56              = (k2_funct_1 @ X0))
% 0.21/0.56          | ~ (v1_funct_1 @ X0)
% 0.21/0.56          | ~ (v1_relat_1 @ X0))),
% 0.21/0.56      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.56  thf('25', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((k2_relat_1 @ X0) != (k2_relat_1 @ X0))
% 0.21/0.56          | ~ (v1_funct_1 @ X0)
% 0.21/0.56          | ~ (v1_relat_1 @ X0)
% 0.21/0.56          | ~ (v1_relat_1 @ X0)
% 0.21/0.56          | ~ (v1_funct_1 @ X0)
% 0.21/0.56          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.21/0.56              = (k2_funct_1 @ X0))
% 0.21/0.56          | ~ (v2_funct_1 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['17', '24'])).
% 0.21/0.56  thf('26', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (v2_funct_1 @ X0)
% 0.21/0.56          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.21/0.56              = (k2_funct_1 @ X0))
% 0.21/0.56          | ~ (v1_relat_1 @ X0)
% 0.21/0.56          | ~ (v1_funct_1 @ X0))),
% 0.21/0.56      inference('simplify', [status(thm)], ['25'])).
% 0.21/0.56  thf(d3_struct_0, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.56  thf('27', plain,
% 0.21/0.56      (![X21 : $i]:
% 0.21/0.56         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.56  thf('28', plain,
% 0.21/0.56      (![X21 : $i]:
% 0.21/0.56         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.56  thf('29', plain,
% 0.21/0.56      (![X21 : $i]:
% 0.21/0.56         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.56  thf(t62_tops_2, conjecture,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( l1_struct_0 @ A ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.21/0.56           ( ![C:$i]:
% 0.21/0.56             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.56                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.56                 ( m1_subset_1 @
% 0.21/0.56                   C @ 
% 0.21/0.56                   ( k1_zfmisc_1 @
% 0.21/0.56                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.56               ( ( ( ( k2_relset_1 @
% 0.21/0.56                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.21/0.56                     ( k2_struct_0 @ B ) ) & 
% 0.21/0.56                   ( v2_funct_1 @ C ) ) =>
% 0.21/0.56                 ( ( ( k1_relset_1 @
% 0.21/0.56                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.56                       ( k2_tops_2 @
% 0.21/0.56                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.21/0.56                     ( k2_struct_0 @ B ) ) & 
% 0.21/0.56                   ( ( k2_relset_1 @
% 0.21/0.56                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.56                       ( k2_tops_2 @
% 0.21/0.56                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.21/0.56                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.56    (~( ![A:$i]:
% 0.21/0.56        ( ( l1_struct_0 @ A ) =>
% 0.21/0.56          ( ![B:$i]:
% 0.21/0.56            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.21/0.56              ( ![C:$i]:
% 0.21/0.56                ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.56                    ( v1_funct_2 @
% 0.21/0.56                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.56                    ( m1_subset_1 @
% 0.21/0.56                      C @ 
% 0.21/0.56                      ( k1_zfmisc_1 @
% 0.21/0.56                        ( k2_zfmisc_1 @
% 0.21/0.56                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.56                  ( ( ( ( k2_relset_1 @
% 0.21/0.56                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.21/0.56                        ( k2_struct_0 @ B ) ) & 
% 0.21/0.56                      ( v2_funct_1 @ C ) ) =>
% 0.21/0.56                    ( ( ( k1_relset_1 @
% 0.21/0.56                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.56                          ( k2_tops_2 @
% 0.21/0.56                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.21/0.56                        ( k2_struct_0 @ B ) ) & 
% 0.21/0.56                      ( ( k2_relset_1 @
% 0.21/0.56                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.56                          ( k2_tops_2 @
% 0.21/0.56                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.21/0.56                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.21/0.56  thf('30', plain,
% 0.21/0.56      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56          != (k2_struct_0 @ sk_B))
% 0.21/0.56        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56            != (k2_struct_0 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('31', plain,
% 0.21/0.56      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56          != (k2_struct_0 @ sk_B)))
% 0.21/0.56         <= (~
% 0.21/0.56             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56                = (k2_struct_0 @ sk_B))))),
% 0.21/0.56      inference('split', [status(esa)], ['30'])).
% 0.21/0.56  thf('32', plain,
% 0.21/0.56      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56           != (k2_struct_0 @ sk_B))
% 0.21/0.56         | ~ (l1_struct_0 @ sk_B)))
% 0.21/0.56         <= (~
% 0.21/0.56             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56                = (k2_struct_0 @ sk_B))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['29', '31'])).
% 0.21/0.56  thf('33', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('34', plain,
% 0.21/0.56      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56          != (k2_struct_0 @ sk_B)))
% 0.21/0.56         <= (~
% 0.21/0.56             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56                = (k2_struct_0 @ sk_B))))),
% 0.21/0.56      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.56  thf('35', plain,
% 0.21/0.56      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.21/0.56           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56           != (k2_struct_0 @ sk_B))
% 0.21/0.56         | ~ (l1_struct_0 @ sk_A)))
% 0.21/0.56         <= (~
% 0.21/0.56             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56                = (k2_struct_0 @ sk_B))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['28', '34'])).
% 0.21/0.56  thf('36', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('37', plain,
% 0.21/0.56      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.21/0.56          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56          != (k2_struct_0 @ sk_B)))
% 0.21/0.56         <= (~
% 0.21/0.56             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56                = (k2_struct_0 @ sk_B))))),
% 0.21/0.56      inference('demod', [status(thm)], ['35', '36'])).
% 0.21/0.56  thf('38', plain,
% 0.21/0.56      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.21/0.56           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56           != (k2_struct_0 @ sk_B))
% 0.21/0.56         | ~ (l1_struct_0 @ sk_B)))
% 0.21/0.56         <= (~
% 0.21/0.56             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56                = (k2_struct_0 @ sk_B))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['27', '37'])).
% 0.21/0.56  thf('39', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('40', plain,
% 0.21/0.56      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.21/0.56          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56          != (k2_struct_0 @ sk_B)))
% 0.21/0.56         <= (~
% 0.21/0.56             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56                = (k2_struct_0 @ sk_B))))),
% 0.21/0.56      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.56  thf('41', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C @ 
% 0.21/0.56        (k1_zfmisc_1 @ 
% 0.21/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('42', plain,
% 0.21/0.56      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.56         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.21/0.56          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.21/0.56      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.56  thf('43', plain,
% 0.21/0.56      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.56         = (k2_relat_1 @ sk_C))),
% 0.21/0.56      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.56  thf('44', plain,
% 0.21/0.56      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.56         = (k2_struct_0 @ sk_B))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('45', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.21/0.56      inference('sup+', [status(thm)], ['43', '44'])).
% 0.21/0.56  thf('46', plain,
% 0.21/0.56      (![X21 : $i]:
% 0.21/0.56         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.56  thf('47', plain,
% 0.21/0.56      (![X21 : $i]:
% 0.21/0.56         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.56  thf('48', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C @ 
% 0.21/0.56        (k1_zfmisc_1 @ 
% 0.21/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('49', plain,
% 0.21/0.56      (((m1_subset_1 @ sk_C @ 
% 0.21/0.56         (k1_zfmisc_1 @ 
% 0.21/0.56          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.21/0.56        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.56      inference('sup+', [status(thm)], ['47', '48'])).
% 0.21/0.56  thf('50', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('51', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C @ 
% 0.21/0.56        (k1_zfmisc_1 @ 
% 0.21/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.21/0.56      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.56  thf(cc5_funct_2, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.56       ( ![C:$i]:
% 0.21/0.56         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.56           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.21/0.56             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.21/0.56  thf('52', plain,
% 0.21/0.56      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.21/0.56          | (v1_partfun1 @ X15 @ X16)
% 0.21/0.56          | ~ (v1_funct_2 @ X15 @ X16 @ X17)
% 0.21/0.56          | ~ (v1_funct_1 @ X15)
% 0.21/0.56          | (v1_xboole_0 @ X17))),
% 0.21/0.56      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.21/0.56  thf('53', plain,
% 0.21/0.56      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.21/0.56        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.56        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.21/0.56        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.56  thf('54', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('55', plain,
% 0.21/0.56      (![X21 : $i]:
% 0.21/0.56         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.56  thf('56', plain,
% 0.21/0.56      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('57', plain,
% 0.21/0.56      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.21/0.56        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.56      inference('sup+', [status(thm)], ['55', '56'])).
% 0.21/0.56  thf('58', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('59', plain,
% 0.21/0.56      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.21/0.56      inference('demod', [status(thm)], ['57', '58'])).
% 0.21/0.56  thf('60', plain,
% 0.21/0.56      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.21/0.56        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('demod', [status(thm)], ['53', '54', '59'])).
% 0.21/0.56  thf('61', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.21/0.56      inference('sup+', [status(thm)], ['43', '44'])).
% 0.21/0.56  thf('62', plain,
% 0.21/0.56      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.21/0.56        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('demod', [status(thm)], ['60', '61'])).
% 0.21/0.56  thf('63', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.21/0.56      inference('sup+', [status(thm)], ['43', '44'])).
% 0.21/0.56  thf('64', plain,
% 0.21/0.56      (![X21 : $i]:
% 0.21/0.56         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.56  thf(fc2_struct_0, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.56       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.56  thf('65', plain,
% 0.21/0.56      (![X22 : $i]:
% 0.21/0.56         (~ (v1_xboole_0 @ (u1_struct_0 @ X22))
% 0.21/0.56          | ~ (l1_struct_0 @ X22)
% 0.21/0.56          | (v2_struct_0 @ X22))),
% 0.21/0.56      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.56  thf('66', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.21/0.56          | ~ (l1_struct_0 @ X0)
% 0.21/0.56          | (v2_struct_0 @ X0)
% 0.21/0.56          | ~ (l1_struct_0 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.56  thf('67', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v2_struct_0 @ X0)
% 0.21/0.56          | ~ (l1_struct_0 @ X0)
% 0.21/0.56          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['66'])).
% 0.21/0.56  thf('68', plain,
% 0.21/0.56      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.21/0.56        | ~ (l1_struct_0 @ sk_B)
% 0.21/0.56        | (v2_struct_0 @ sk_B))),
% 0.21/0.56      inference('sup-', [status(thm)], ['63', '67'])).
% 0.21/0.56  thf('69', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('70', plain,
% 0.21/0.56      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.21/0.56      inference('demod', [status(thm)], ['68', '69'])).
% 0.21/0.56  thf('71', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('72', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.21/0.56      inference('clc', [status(thm)], ['70', '71'])).
% 0.21/0.56  thf('73', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.56      inference('clc', [status(thm)], ['62', '72'])).
% 0.21/0.56  thf('74', plain,
% 0.21/0.56      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.56      inference('sup+', [status(thm)], ['46', '73'])).
% 0.21/0.56  thf('75', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('76', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['74', '75'])).
% 0.21/0.56  thf(d4_partfun1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.21/0.56       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.21/0.56  thf('77', plain,
% 0.21/0.56      (![X18 : $i, X19 : $i]:
% 0.21/0.56         (~ (v1_partfun1 @ X19 @ X18)
% 0.21/0.56          | ((k1_relat_1 @ X19) = (X18))
% 0.21/0.56          | ~ (v4_relat_1 @ X19 @ X18)
% 0.21/0.56          | ~ (v1_relat_1 @ X19))),
% 0.21/0.56      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.21/0.56  thf('78', plain,
% 0.21/0.56      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.56        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.21/0.56        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['76', '77'])).
% 0.21/0.56  thf('79', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C @ 
% 0.21/0.56        (k1_zfmisc_1 @ 
% 0.21/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(cc2_relat_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( v1_relat_1 @ A ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.56  thf('80', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.21/0.56          | (v1_relat_1 @ X0)
% 0.21/0.56          | ~ (v1_relat_1 @ X1))),
% 0.21/0.56      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.56  thf('81', plain,
% 0.21/0.56      ((~ (v1_relat_1 @ 
% 0.21/0.56           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.21/0.56        | (v1_relat_1 @ sk_C))),
% 0.21/0.56      inference('sup-', [status(thm)], ['79', '80'])).
% 0.21/0.56  thf(fc6_relat_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.56  thf('82', plain,
% 0.21/0.56      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.21/0.56      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.56  thf('83', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.56      inference('demod', [status(thm)], ['81', '82'])).
% 0.21/0.56  thf('84', plain,
% 0.21/0.56      (![X21 : $i]:
% 0.21/0.56         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.56  thf('85', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C @ 
% 0.21/0.56        (k1_zfmisc_1 @ 
% 0.21/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('86', plain,
% 0.21/0.56      (((m1_subset_1 @ sk_C @ 
% 0.21/0.56         (k1_zfmisc_1 @ 
% 0.21/0.56          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.21/0.56        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.56      inference('sup+', [status(thm)], ['84', '85'])).
% 0.21/0.56  thf('87', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('88', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C @ 
% 0.21/0.56        (k1_zfmisc_1 @ 
% 0.21/0.56         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.56      inference('demod', [status(thm)], ['86', '87'])).
% 0.21/0.56  thf(cc2_relset_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.56       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.56  thf('89', plain,
% 0.21/0.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.56         ((v4_relat_1 @ X6 @ X7)
% 0.21/0.56          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.21/0.56      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.56  thf('90', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['88', '89'])).
% 0.21/0.56  thf('91', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['78', '83', '90'])).
% 0.21/0.56  thf('92', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.56      inference('clc', [status(thm)], ['62', '72'])).
% 0.21/0.56  thf('93', plain,
% 0.21/0.56      (![X18 : $i, X19 : $i]:
% 0.21/0.56         (~ (v1_partfun1 @ X19 @ X18)
% 0.21/0.56          | ((k1_relat_1 @ X19) = (X18))
% 0.21/0.56          | ~ (v4_relat_1 @ X19 @ X18)
% 0.21/0.56          | ~ (v1_relat_1 @ X19))),
% 0.21/0.56      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.21/0.56  thf('94', plain,
% 0.21/0.56      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.56        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.21/0.56        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['92', '93'])).
% 0.21/0.56  thf('95', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.56      inference('demod', [status(thm)], ['81', '82'])).
% 0.21/0.56  thf('96', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C @ 
% 0.21/0.56        (k1_zfmisc_1 @ 
% 0.21/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('97', plain,
% 0.21/0.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.56         ((v4_relat_1 @ X6 @ X7)
% 0.21/0.56          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.21/0.56      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.56  thf('98', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['96', '97'])).
% 0.21/0.56  thf('99', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['94', '95', '98'])).
% 0.21/0.56  thf('100', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.21/0.56      inference('sup+', [status(thm)], ['43', '44'])).
% 0.21/0.56  thf('101', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.21/0.56      inference('sup+', [status(thm)], ['43', '44'])).
% 0.21/0.56  thf('102', plain,
% 0.21/0.56      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.21/0.56          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.21/0.56          != (k2_relat_1 @ sk_C)))
% 0.21/0.56         <= (~
% 0.21/0.56             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56                = (k2_struct_0 @ sk_B))))),
% 0.21/0.56      inference('demod', [status(thm)], ['40', '45', '91', '99', '100', '101'])).
% 0.21/0.56  thf('103', plain,
% 0.21/0.56      (((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.21/0.56           (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C))
% 0.21/0.56         | ~ (v1_funct_1 @ sk_C)
% 0.21/0.56         | ~ (v1_relat_1 @ sk_C)
% 0.21/0.56         | ~ (v2_funct_1 @ sk_C)))
% 0.21/0.56         <= (~
% 0.21/0.56             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56                = (k2_struct_0 @ sk_B))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['26', '102'])).
% 0.21/0.56  thf('104', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('105', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.56      inference('demod', [status(thm)], ['81', '82'])).
% 0.21/0.56  thf('106', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('107', plain,
% 0.21/0.56      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.21/0.56          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.21/0.56         <= (~
% 0.21/0.56             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56                = (k2_struct_0 @ sk_B))))),
% 0.21/0.56      inference('demod', [status(thm)], ['103', '104', '105', '106'])).
% 0.21/0.56  thf('108', plain,
% 0.21/0.56      (![X5 : $i]:
% 0.21/0.56         (~ (v2_funct_1 @ X5)
% 0.21/0.56          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.21/0.56          | ~ (v1_funct_1 @ X5)
% 0.21/0.56          | ~ (v1_relat_1 @ X5))),
% 0.21/0.56      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.21/0.56  thf('109', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (v2_funct_1 @ X0)
% 0.21/0.56          | ~ (v1_funct_1 @ X0)
% 0.21/0.56          | ~ (v1_relat_1 @ X0)
% 0.21/0.56          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.21/0.56             (k1_zfmisc_1 @ 
% 0.21/0.56              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 0.21/0.56      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.56  thf('110', plain,
% 0.21/0.56      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.56         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.21/0.56          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.21/0.56      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.56  thf('111', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (v1_relat_1 @ X0)
% 0.21/0.56          | ~ (v1_funct_1 @ X0)
% 0.21/0.56          | ~ (v2_funct_1 @ X0)
% 0.21/0.56          | ((k2_relset_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0) @ 
% 0.21/0.56              (k2_funct_1 @ X0)) = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['109', '110'])).
% 0.21/0.56  thf('112', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C @ 
% 0.21/0.56        (k1_zfmisc_1 @ 
% 0.21/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.21/0.56      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.56  thf('113', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.21/0.56      inference('sup+', [status(thm)], ['43', '44'])).
% 0.21/0.56  thf('114', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C @ 
% 0.21/0.56        (k1_zfmisc_1 @ 
% 0.21/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.21/0.56      inference('demod', [status(thm)], ['112', '113'])).
% 0.21/0.56  thf('115', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['94', '95', '98'])).
% 0.21/0.56  thf('116', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C @ 
% 0.21/0.56        (k1_zfmisc_1 @ 
% 0.21/0.56         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.21/0.56      inference('demod', [status(thm)], ['114', '115'])).
% 0.21/0.56  thf('117', plain,
% 0.21/0.56      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.56         (((k2_relset_1 @ X24 @ X23 @ X25) != (X23))
% 0.21/0.56          | ~ (v2_funct_1 @ X25)
% 0.21/0.56          | ((k2_tops_2 @ X24 @ X23 @ X25) = (k2_funct_1 @ X25))
% 0.21/0.56          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23)))
% 0.21/0.56          | ~ (v1_funct_2 @ X25 @ X24 @ X23)
% 0.21/0.56          | ~ (v1_funct_1 @ X25))),
% 0.21/0.56      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.21/0.56  thf('118', plain,
% 0.21/0.56      ((~ (v1_funct_1 @ sk_C)
% 0.21/0.56        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.21/0.56        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.21/0.56            = (k2_funct_1 @ sk_C))
% 0.21/0.56        | ~ (v2_funct_1 @ sk_C)
% 0.21/0.56        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.21/0.56            != (k2_relat_1 @ sk_C)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['116', '117'])).
% 0.21/0.56  thf('119', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('120', plain,
% 0.21/0.56      (![X21 : $i]:
% 0.21/0.56         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.56  thf('121', plain,
% 0.21/0.56      (![X21 : $i]:
% 0.21/0.56         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.56  thf('122', plain,
% 0.21/0.56      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('123', plain,
% 0.21/0.56      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.21/0.56        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.56      inference('sup+', [status(thm)], ['121', '122'])).
% 0.21/0.56  thf('124', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('125', plain,
% 0.21/0.56      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.56      inference('demod', [status(thm)], ['123', '124'])).
% 0.21/0.56  thf('126', plain,
% 0.21/0.56      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.21/0.56        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.56      inference('sup+', [status(thm)], ['120', '125'])).
% 0.21/0.56  thf('127', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('128', plain,
% 0.21/0.56      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.21/0.56      inference('demod', [status(thm)], ['126', '127'])).
% 0.21/0.56  thf('129', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.21/0.56      inference('sup+', [status(thm)], ['43', '44'])).
% 0.21/0.56  thf('130', plain,
% 0.21/0.56      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.21/0.56      inference('demod', [status(thm)], ['128', '129'])).
% 0.21/0.56  thf('131', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['78', '83', '90'])).
% 0.21/0.56  thf('132', plain,
% 0.21/0.56      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.21/0.56      inference('demod', [status(thm)], ['130', '131'])).
% 0.21/0.56  thf('133', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('134', plain,
% 0.21/0.56      (![X21 : $i]:
% 0.21/0.56         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.56  thf('135', plain,
% 0.21/0.56      (![X21 : $i]:
% 0.21/0.56         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.56  thf('136', plain,
% 0.21/0.56      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.56         = (k2_struct_0 @ sk_B))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('137', plain,
% 0.21/0.56      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.21/0.56          = (k2_struct_0 @ sk_B))
% 0.21/0.56        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.56      inference('sup+', [status(thm)], ['135', '136'])).
% 0.21/0.56  thf('138', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('139', plain,
% 0.21/0.56      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.21/0.56         = (k2_struct_0 @ sk_B))),
% 0.21/0.56      inference('demod', [status(thm)], ['137', '138'])).
% 0.21/0.56  thf('140', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.21/0.56      inference('sup+', [status(thm)], ['43', '44'])).
% 0.21/0.56  thf('141', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.21/0.56      inference('sup+', [status(thm)], ['43', '44'])).
% 0.21/0.56  thf('142', plain,
% 0.21/0.56      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.21/0.56         = (k2_relat_1 @ sk_C))),
% 0.21/0.56      inference('demod', [status(thm)], ['139', '140', '141'])).
% 0.21/0.56  thf('143', plain,
% 0.21/0.56      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.21/0.56          = (k2_relat_1 @ sk_C))
% 0.21/0.56        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.56      inference('sup+', [status(thm)], ['134', '142'])).
% 0.21/0.56  thf('144', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('145', plain,
% 0.21/0.56      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.21/0.56         = (k2_relat_1 @ sk_C))),
% 0.21/0.56      inference('demod', [status(thm)], ['143', '144'])).
% 0.21/0.56  thf('146', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['78', '83', '90'])).
% 0.21/0.56  thf('147', plain,
% 0.21/0.56      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.21/0.56         = (k2_relat_1 @ sk_C))),
% 0.21/0.56      inference('demod', [status(thm)], ['145', '146'])).
% 0.21/0.56  thf('148', plain,
% 0.21/0.56      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.21/0.56          = (k2_funct_1 @ sk_C))
% 0.21/0.56        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.21/0.56      inference('demod', [status(thm)], ['118', '119', '132', '133', '147'])).
% 0.21/0.56  thf('149', plain,
% 0.21/0.56      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.21/0.56         = (k2_funct_1 @ sk_C))),
% 0.21/0.56      inference('simplify', [status(thm)], ['148'])).
% 0.21/0.56  thf('150', plain,
% 0.21/0.56      (![X21 : $i]:
% 0.21/0.56         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.56  thf('151', plain,
% 0.21/0.56      (![X21 : $i]:
% 0.21/0.56         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.56  thf('152', plain,
% 0.21/0.56      (![X21 : $i]:
% 0.21/0.56         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.56  thf('153', plain,
% 0.21/0.56      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56          != (k2_struct_0 @ sk_A)))
% 0.21/0.56         <= (~
% 0.21/0.56             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56                = (k2_struct_0 @ sk_A))))),
% 0.21/0.56      inference('split', [status(esa)], ['30'])).
% 0.21/0.56  thf('154', plain,
% 0.21/0.56      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56           != (k2_struct_0 @ sk_A))
% 0.21/0.56         | ~ (l1_struct_0 @ sk_A)))
% 0.21/0.56         <= (~
% 0.21/0.56             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56                = (k2_struct_0 @ sk_A))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['152', '153'])).
% 0.21/0.56  thf('155', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('156', plain,
% 0.21/0.56      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56          != (k2_struct_0 @ sk_A)))
% 0.21/0.56         <= (~
% 0.21/0.56             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56                = (k2_struct_0 @ sk_A))))),
% 0.21/0.56      inference('demod', [status(thm)], ['154', '155'])).
% 0.21/0.56  thf('157', plain,
% 0.21/0.56      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56           != (k2_struct_0 @ sk_A))
% 0.21/0.56         | ~ (l1_struct_0 @ sk_B)))
% 0.21/0.56         <= (~
% 0.21/0.56             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56                = (k2_struct_0 @ sk_A))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['151', '156'])).
% 0.21/0.56  thf('158', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('159', plain,
% 0.21/0.56      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56          != (k2_struct_0 @ sk_A)))
% 0.21/0.56         <= (~
% 0.21/0.56             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56                = (k2_struct_0 @ sk_A))))),
% 0.21/0.56      inference('demod', [status(thm)], ['157', '158'])).
% 0.21/0.56  thf('160', plain,
% 0.21/0.56      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56           != (k2_struct_0 @ sk_A))
% 0.21/0.56         | ~ (l1_struct_0 @ sk_B)))
% 0.21/0.56         <= (~
% 0.21/0.56             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56                = (k2_struct_0 @ sk_A))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['150', '159'])).
% 0.21/0.56  thf('161', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('162', plain,
% 0.21/0.56      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56          != (k2_struct_0 @ sk_A)))
% 0.21/0.56         <= (~
% 0.21/0.56             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56                = (k2_struct_0 @ sk_A))))),
% 0.21/0.56      inference('demod', [status(thm)], ['160', '161'])).
% 0.21/0.56  thf('163', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.21/0.56      inference('sup+', [status(thm)], ['43', '44'])).
% 0.21/0.56  thf('164', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['94', '95', '98'])).
% 0.21/0.56  thf('165', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['78', '83', '90'])).
% 0.21/0.56  thf('166', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.21/0.56      inference('sup+', [status(thm)], ['43', '44'])).
% 0.21/0.56  thf('167', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['78', '83', '90'])).
% 0.21/0.56  thf('168', plain,
% 0.21/0.56      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.21/0.56          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.21/0.56          != (k1_relat_1 @ sk_C)))
% 0.21/0.56         <= (~
% 0.21/0.56             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56                = (k2_struct_0 @ sk_A))))),
% 0.21/0.56      inference('demod', [status(thm)],
% 0.21/0.56                ['162', '163', '164', '165', '166', '167'])).
% 0.21/0.56  thf('169', plain,
% 0.21/0.56      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.21/0.56          (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 0.21/0.56         <= (~
% 0.21/0.56             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56                = (k2_struct_0 @ sk_A))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['149', '168'])).
% 0.21/0.56  thf('170', plain,
% 0.21/0.56      (((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.21/0.56         | ~ (v2_funct_1 @ sk_C)
% 0.21/0.56         | ~ (v1_funct_1 @ sk_C)
% 0.21/0.56         | ~ (v1_relat_1 @ sk_C)))
% 0.21/0.56         <= (~
% 0.21/0.56             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56                = (k2_struct_0 @ sk_A))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['111', '169'])).
% 0.21/0.56  thf('171', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('172', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('173', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.56      inference('demod', [status(thm)], ['81', '82'])).
% 0.21/0.56  thf('174', plain,
% 0.21/0.56      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 0.21/0.56         <= (~
% 0.21/0.56             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56                = (k2_struct_0 @ sk_A))))),
% 0.21/0.56      inference('demod', [status(thm)], ['170', '171', '172', '173'])).
% 0.21/0.56  thf('175', plain,
% 0.21/0.56      (((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 0.21/0.56         | ~ (v1_relat_1 @ sk_C)
% 0.21/0.56         | ~ (v1_funct_1 @ sk_C)
% 0.21/0.56         | ~ (v2_funct_1 @ sk_C)))
% 0.21/0.56         <= (~
% 0.21/0.56             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56                = (k2_struct_0 @ sk_A))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['108', '174'])).
% 0.21/0.56  thf('176', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.56      inference('demod', [status(thm)], ['81', '82'])).
% 0.21/0.56  thf('177', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('178', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('179', plain,
% 0.21/0.56      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))
% 0.21/0.56         <= (~
% 0.21/0.56             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56                = (k2_struct_0 @ sk_A))))),
% 0.21/0.56      inference('demod', [status(thm)], ['175', '176', '177', '178'])).
% 0.21/0.56  thf('180', plain,
% 0.21/0.56      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56          = (k2_struct_0 @ sk_A)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['179'])).
% 0.21/0.56  thf('181', plain,
% 0.21/0.56      (~
% 0.21/0.56       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56          = (k2_struct_0 @ sk_B))) | 
% 0.21/0.56       ~
% 0.21/0.56       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56          = (k2_struct_0 @ sk_A)))),
% 0.21/0.56      inference('split', [status(esa)], ['30'])).
% 0.21/0.56  thf('182', plain,
% 0.21/0.56      (~
% 0.21/0.56       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.56          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.56          = (k2_struct_0 @ sk_B)))),
% 0.21/0.56      inference('sat_resolution*', [status(thm)], ['180', '181'])).
% 0.21/0.56  thf('183', plain,
% 0.21/0.56      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.21/0.56         (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C))),
% 0.21/0.56      inference('simpl_trail', [status(thm)], ['107', '182'])).
% 0.21/0.56  thf('184', plain,
% 0.21/0.56      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C))
% 0.21/0.56        | ~ (v2_funct_1 @ sk_C)
% 0.21/0.56        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.56        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.56      inference('sup-', [status(thm)], ['14', '183'])).
% 0.21/0.56  thf('185', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('186', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('187', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.56      inference('demod', [status(thm)], ['81', '82'])).
% 0.21/0.56  thf('188', plain,
% 0.21/0.56      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C))),
% 0.21/0.56      inference('demod', [status(thm)], ['184', '185', '186', '187'])).
% 0.21/0.56  thf('189', plain,
% 0.21/0.56      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.21/0.56        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.56        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.56        | ~ (v2_funct_1 @ sk_C))),
% 0.21/0.56      inference('sup-', [status(thm)], ['0', '188'])).
% 0.21/0.56  thf('190', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.56      inference('demod', [status(thm)], ['81', '82'])).
% 0.21/0.56  thf('191', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('192', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('193', plain, (((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))),
% 0.21/0.56      inference('demod', [status(thm)], ['189', '190', '191', '192'])).
% 0.21/0.56  thf('194', plain, ($false), inference('simplify', [status(thm)], ['193'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.21/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
