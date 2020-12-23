%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Xa4oT23m7u

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:33 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  198 ( 512 expanded)
%              Number of leaves         :   23 ( 152 expanded)
%              Depth                    :   24
%              Number of atoms          : 3295 (7696 expanded)
%              Number of equality atoms :    8 (  30 expanded)
%              Maximal formula depth    :   21 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(m1_setfam_1_type,type,(
    m1_setfam_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf(d7_compts_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_compts_1 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ~ ( ( m1_setfam_1 @ C @ B )
                    & ( v1_tops_2 @ C @ A )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                       => ~ ( ( r1_tarski @ D @ C )
                            & ( m1_setfam_1 @ D @ B )
                            & ( v1_finset_1 @ D ) ) ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( v1_tops_2 @ ( sk_C_1 @ X6 @ X7 ) @ X7 )
      | ( v2_compts_1 @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_compts_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ( v1_tops_2 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( m1_setfam_1 @ ( sk_C_1 @ X6 @ X7 ) @ X6 )
      | ( v2_compts_1 @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_compts_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ( m1_setfam_1 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('7',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( m1_subset_1 @ ( sk_C_1 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ( v2_compts_1 @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_compts_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d3_compts_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_compts_1 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ~ ( ( m1_setfam_1 @ B @ ( u1_struct_0 @ A ) )
                & ( v1_tops_2 @ B @ A )
                & ! [C: $i] :
                    ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                   => ~ ( ( r1_tarski @ C @ B )
                        & ( m1_setfam_1 @ C @ ( u1_struct_0 @ A ) )
                        & ( v1_finset_1 @ C ) ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X3: $i,X5: $i] :
      ( ~ ( v1_compts_1 @ X3 )
      | ( v1_finset_1 @ ( sk_C @ X5 @ X3 ) )
      | ~ ( v1_tops_2 @ X5 @ X3 )
      | ~ ( m1_setfam_1 @ X5 @ ( u1_struct_0 @ X3 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_compts_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_setfam_1 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_tops_2 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ( v1_finset_1 @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) )
      | ~ ( v1_compts_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_compts_1 @ X0 )
      | ( v1_finset_1 @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) )
      | ~ ( v1_tops_2 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ~ ( m1_setfam_1 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( m1_setfam_1 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_tops_2 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ( v1_finset_1 @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) )
      | ~ ( v1_compts_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_compts_1 @ X0 )
      | ( v1_finset_1 @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) )
      | ~ ( v1_tops_2 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_setfam_1 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tops_2 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ( v1_finset_1 @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) )
      | ~ ( v1_compts_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_compts_1 @ X0 )
      | ( v1_finset_1 @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) )
      | ~ ( v1_tops_2 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_finset_1 @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) )
      | ~ ( v1_compts_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_compts_1 @ X0 )
      | ( v1_finset_1 @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ( v1_tops_2 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ( m1_setfam_1 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('25',plain,(
    ! [X3: $i,X5: $i] :
      ( ~ ( v1_compts_1 @ X3 )
      | ( m1_setfam_1 @ ( sk_C @ X5 @ X3 ) @ ( u1_struct_0 @ X3 ) )
      | ~ ( v1_tops_2 @ X5 @ X3 )
      | ~ ( m1_setfam_1 @ X5 @ ( u1_struct_0 @ X3 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_compts_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_setfam_1 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_tops_2 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ( m1_setfam_1 @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_compts_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_compts_1 @ X0 )
      | ( m1_setfam_1 @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_tops_2 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ~ ( m1_setfam_1 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_setfam_1 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_tops_2 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ( m1_setfam_1 @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_compts_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_compts_1 @ X0 )
      | ( m1_setfam_1 @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_tops_2 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_setfam_1 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tops_2 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ( m1_setfam_1 @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_compts_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_compts_1 @ X0 )
      | ( m1_setfam_1 @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_tops_2 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_setfam_1 @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_compts_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_compts_1 @ X0 )
      | ( m1_setfam_1 @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( m1_setfam_1 @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_compts_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_setfam_1 @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ( v1_tops_2 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ( m1_setfam_1 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('40',plain,(
    ! [X3: $i,X5: $i] :
      ( ~ ( v1_compts_1 @ X3 )
      | ( r1_tarski @ ( sk_C @ X5 @ X3 ) @ X5 )
      | ~ ( v1_tops_2 @ X5 @ X3 )
      | ~ ( m1_setfam_1 @ X5 @ ( u1_struct_0 @ X3 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_compts_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_setfam_1 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_tops_2 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ( r1_tarski @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) )
      | ~ ( v1_compts_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_compts_1 @ X0 )
      | ( r1_tarski @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) )
      | ~ ( v1_tops_2 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ~ ( m1_setfam_1 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( m1_setfam_1 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_tops_2 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ( r1_tarski @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) )
      | ~ ( v1_compts_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_compts_1 @ X0 )
      | ( r1_tarski @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) )
      | ~ ( v1_tops_2 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_setfam_1 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tops_2 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ( r1_tarski @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) )
      | ~ ( v1_compts_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_compts_1 @ X0 )
      | ( r1_tarski @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) )
      | ~ ( v1_tops_2 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( r1_tarski @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) )
      | ~ ( v1_compts_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_compts_1 @ X0 )
      | ( r1_tarski @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ( v1_tops_2 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ( m1_setfam_1 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('53',plain,(
    ! [X3: $i,X5: $i] :
      ( ~ ( v1_compts_1 @ X3 )
      | ( m1_subset_1 @ ( sk_C @ X5 @ X3 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) )
      | ~ ( v1_tops_2 @ X5 @ X3 )
      | ~ ( m1_setfam_1 @ X5 @ ( u1_struct_0 @ X3 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_compts_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_setfam_1 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_tops_2 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_compts_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_compts_1 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_tops_2 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ~ ( m1_setfam_1 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( m1_setfam_1 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_tops_2 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_compts_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_compts_1 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_tops_2 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_setfam_1 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tops_2 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_compts_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_compts_1 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_tops_2 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_compts_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_compts_1 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( r1_tarski @ X9 @ ( sk_C_1 @ X6 @ X7 ) )
      | ~ ( m1_setfam_1 @ X9 @ X6 )
      | ~ ( v1_finset_1 @ X9 )
      | ( v2_compts_1 @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_compts_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ X1 @ X0 )
      | ~ ( v1_finset_1 @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) )
      | ~ ( m1_setfam_1 @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) @ X1 )
      | ~ ( r1_tarski @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) @ ( sk_C_1 @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r1_tarski @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) @ ( sk_C_1 @ X1 @ X0 ) )
      | ~ ( m1_setfam_1 @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) @ X1 )
      | ~ ( v1_finset_1 @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) )
      | ( v2_compts_1 @ X1 @ X0 )
      | ~ ( v1_compts_1 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_compts_1 @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_compts_1 @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( v1_finset_1 @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) )
      | ~ ( m1_setfam_1 @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['48','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_setfam_1 @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( v1_finset_1 @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) )
      | ~ ( v1_compts_1 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_compts_1 @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_compts_1 @ X0 )
      | ~ ( v1_finset_1 @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['35','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_finset_1 @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) )
      | ~ ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_compts_1 @ X0 )
      | ~ ( v1_finset_1 @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_finset_1 @ ( sk_C @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) )
      | ~ ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_compts_1 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_compts_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_compts_1 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf(t10_compts_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_compts_1 @ A )
      <=> ( v2_compts_1 @ ( k2_struct_0 @ A ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ( ( v1_compts_1 @ A )
        <=> ( v2_compts_1 @ ( k2_struct_0 @ A ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t10_compts_1])).

thf('73',plain,
    ( ~ ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v1_compts_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ~ ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A )
   <= ~ ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference(split,[status(esa)],['73'])).

thf('75',plain,
    ( ~ ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['73'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('77',plain,
    ( ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ( v1_compts_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A )
   <= ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference(split,[status(esa)],['77'])).

thf('79',plain,(
    ! [X3: $i] :
      ( ( v1_tops_2 @ ( sk_B @ X3 ) @ X3 )
      | ( v1_compts_1 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_compts_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('81',plain,(
    ! [X3: $i] :
      ( ( m1_setfam_1 @ ( sk_B @ X3 ) @ ( u1_struct_0 @ X3 ) )
      | ( v1_compts_1 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_compts_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( m1_setfam_1 @ ( sk_B @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_compts_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('84',plain,(
    ! [X3: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X3 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) )
      | ( v1_compts_1 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_compts_1])).

thf('85',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( v2_compts_1 @ X6 @ X7 )
      | ( r1_tarski @ ( sk_D @ X8 @ X6 @ X7 ) @ X8 )
      | ~ ( v1_tops_2 @ X8 @ X7 )
      | ~ ( m1_setfam_1 @ X8 @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_compts_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_setfam_1 @ ( sk_B @ X0 ) @ X1 )
      | ~ ( v1_tops_2 @ ( sk_B @ X0 ) @ X0 )
      | ( r1_tarski @ ( sk_D @ ( sk_B @ X0 ) @ X1 @ X0 ) @ ( sk_B @ X0 ) )
      | ~ ( v2_compts_1 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_compts_1 @ X1 @ X0 )
      | ( r1_tarski @ ( sk_D @ ( sk_B @ X0 ) @ X1 @ X0 ) @ ( sk_B @ X0 ) )
      | ~ ( v1_tops_2 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( m1_setfam_1 @ ( sk_B @ X0 ) @ X1 )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_compts_1 @ X0 )
      | ~ ( m1_setfam_1 @ ( sk_B @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( v1_tops_2 @ ( sk_B @ X0 ) @ X0 )
      | ( r1_tarski @ ( sk_D @ ( sk_B @ X0 ) @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( sk_B @ X0 ) )
      | ~ ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ( r1_tarski @ ( sk_D @ ( sk_B @ X0 ) @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( sk_B @ X0 ) )
      | ~ ( v1_tops_2 @ ( sk_B @ X0 ) @ X0 )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tops_2 @ ( sk_B @ X0 ) @ X0 )
      | ( r1_tarski @ ( sk_D @ ( sk_B @ X0 ) @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( sk_B @ X0 ) )
      | ~ ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_compts_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_compts_1 @ X0 )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ( r1_tarski @ ( sk_D @ ( sk_B @ X0 ) @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['79','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D @ ( sk_B @ X0 ) @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( sk_B @ X0 ) )
      | ~ ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r1_tarski @ ( sk_D @ ( sk_B @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_A ) @ ( sk_B @ sk_A ) ) )
   <= ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['78','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('96',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('97',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( ( v1_compts_1 @ sk_A )
      | ( r1_tarski @ ( sk_D @ ( sk_B @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_A ) @ ( sk_B @ sk_A ) ) )
   <= ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['93','94','97'])).

thf('99',plain,
    ( ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A )
   <= ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference(split,[status(esa)],['77'])).

thf('100',plain,(
    ! [X3: $i] :
      ( ( v1_tops_2 @ ( sk_B @ X3 ) @ X3 )
      | ( v1_compts_1 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_compts_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( m1_setfam_1 @ ( sk_B @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_compts_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('102',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('103',plain,(
    ! [X3: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X3 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) )
      | ( v1_compts_1 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_compts_1])).

thf('104',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( v2_compts_1 @ X6 @ X7 )
      | ( m1_subset_1 @ ( sk_D @ X8 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( v1_tops_2 @ X8 @ X7 )
      | ~ ( m1_setfam_1 @ X8 @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_compts_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_setfam_1 @ ( sk_B @ X0 ) @ X1 )
      | ~ ( v1_tops_2 @ ( sk_B @ X0 ) @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( sk_B @ X0 ) @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v2_compts_1 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_compts_1 @ X1 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( sk_B @ X0 ) @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_tops_2 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( m1_setfam_1 @ ( sk_B @ X0 ) @ X1 )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_compts_1 @ X0 )
      | ~ ( m1_setfam_1 @ ( sk_B @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( v1_tops_2 @ ( sk_B @ X0 ) @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( sk_B @ X0 ) @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( sk_B @ X0 ) @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_tops_2 @ ( sk_B @ X0 ) @ X0 )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['101','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tops_2 @ ( sk_B @ X0 ) @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( sk_B @ X0 ) @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_compts_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_compts_1 @ X0 )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( sk_B @ X0 ) @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['100','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ ( sk_B @ X0 ) @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ ( sk_B @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) )
   <= ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['99','111'])).

thf('113',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['95','96'])).

thf('115',plain,
    ( ( ( v1_compts_1 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ ( sk_B @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) )
   <= ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) )
      | ~ ( r1_tarski @ X4 @ ( sk_B @ X3 ) )
      | ~ ( m1_setfam_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ~ ( v1_finset_1 @ X4 )
      | ( v1_compts_1 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_compts_1])).

thf('117',plain,
    ( ( ( v1_compts_1 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ~ ( v1_finset_1 @ ( sk_D @ ( sk_B @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_A ) )
      | ~ ( m1_setfam_1 @ ( sk_D @ ( sk_B @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ ( sk_D @ ( sk_B @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_A ) @ ( sk_B @ sk_A ) ) )
   <= ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( ( v1_compts_1 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ~ ( v1_finset_1 @ ( sk_D @ ( sk_B @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_A ) )
      | ~ ( m1_setfam_1 @ ( sk_D @ ( sk_B @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ ( sk_D @ ( sk_B @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_A ) @ ( sk_B @ sk_A ) ) )
   <= ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( ~ ( r1_tarski @ ( sk_D @ ( sk_B @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_A ) @ ( sk_B @ sk_A ) )
      | ~ ( m1_setfam_1 @ ( sk_D @ ( sk_B @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_finset_1 @ ( sk_D @ ( sk_B @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_A ) )
      | ( v1_compts_1 @ sk_A ) )
   <= ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,
    ( ( ( v1_compts_1 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ~ ( v1_finset_1 @ ( sk_D @ ( sk_B @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_A ) )
      | ~ ( m1_setfam_1 @ ( sk_D @ ( sk_B @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['98','120'])).

thf('122',plain,
    ( ( ~ ( m1_setfam_1 @ ( sk_D @ ( sk_B @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_finset_1 @ ( sk_D @ ( sk_B @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_A ) )
      | ( v1_compts_1 @ sk_A ) )
   <= ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,
    ( ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A )
   <= ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference(split,[status(esa)],['77'])).

thf('124',plain,(
    ! [X3: $i] :
      ( ( v1_tops_2 @ ( sk_B @ X3 ) @ X3 )
      | ( v1_compts_1 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_compts_1])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( m1_setfam_1 @ ( sk_B @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_compts_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('126',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('127',plain,(
    ! [X3: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X3 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) )
      | ( v1_compts_1 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_compts_1])).

thf('128',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( v2_compts_1 @ X6 @ X7 )
      | ( v1_finset_1 @ ( sk_D @ X8 @ X6 @ X7 ) )
      | ~ ( v1_tops_2 @ X8 @ X7 )
      | ~ ( m1_setfam_1 @ X8 @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_compts_1])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_setfam_1 @ ( sk_B @ X0 ) @ X1 )
      | ~ ( v1_tops_2 @ ( sk_B @ X0 ) @ X0 )
      | ( v1_finset_1 @ ( sk_D @ ( sk_B @ X0 ) @ X1 @ X0 ) )
      | ~ ( v2_compts_1 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_compts_1 @ X1 @ X0 )
      | ( v1_finset_1 @ ( sk_D @ ( sk_B @ X0 ) @ X1 @ X0 ) )
      | ~ ( v1_tops_2 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( m1_setfam_1 @ ( sk_B @ X0 ) @ X1 )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_compts_1 @ X0 )
      | ~ ( m1_setfam_1 @ ( sk_B @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( v1_tops_2 @ ( sk_B @ X0 ) @ X0 )
      | ( v1_finset_1 @ ( sk_D @ ( sk_B @ X0 ) @ ( k2_struct_0 @ X0 ) @ X0 ) )
      | ~ ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['126','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ( v1_finset_1 @ ( sk_D @ ( sk_B @ X0 ) @ ( k2_struct_0 @ X0 ) @ X0 ) )
      | ~ ( v1_tops_2 @ ( sk_B @ X0 ) @ X0 )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['125','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tops_2 @ ( sk_B @ X0 ) @ X0 )
      | ( v1_finset_1 @ ( sk_D @ ( sk_B @ X0 ) @ ( k2_struct_0 @ X0 ) @ X0 ) )
      | ~ ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_compts_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_compts_1 @ X0 )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ( v1_finset_1 @ ( sk_D @ ( sk_B @ X0 ) @ ( k2_struct_0 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['124','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( v1_finset_1 @ ( sk_D @ ( sk_B @ X0 ) @ ( k2_struct_0 @ X0 ) @ X0 ) )
      | ~ ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_finset_1 @ ( sk_D @ ( sk_B @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_A ) ) )
   <= ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['123','135'])).

thf('137',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['95','96'])).

thf('139',plain,
    ( ( ( v1_compts_1 @ sk_A )
      | ( v1_finset_1 @ ( sk_D @ ( sk_B @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_A ) ) )
   <= ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('140',plain,
    ( ( ( v1_compts_1 @ sk_A )
      | ~ ( m1_setfam_1 @ ( sk_D @ ( sk_B @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['122','139'])).

thf('141',plain,
    ( ( ~ ( m1_setfam_1 @ ( sk_D @ ( sk_B @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A ) )
   <= ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['76','140'])).

thf('142',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['95','96'])).

thf('143',plain,
    ( ( ~ ( m1_setfam_1 @ ( sk_D @ ( sk_B @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      | ( v1_compts_1 @ sk_A ) )
   <= ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,
    ( ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A )
   <= ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference(split,[status(esa)],['77'])).

thf('145',plain,(
    ! [X3: $i] :
      ( ( v1_tops_2 @ ( sk_B @ X3 ) @ X3 )
      | ( v1_compts_1 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_compts_1])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( m1_setfam_1 @ ( sk_B @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_compts_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('147',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('148',plain,(
    ! [X3: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X3 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) )
      | ( v1_compts_1 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_compts_1])).

thf('149',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( v2_compts_1 @ X6 @ X7 )
      | ( m1_setfam_1 @ ( sk_D @ X8 @ X6 @ X7 ) @ X6 )
      | ~ ( v1_tops_2 @ X8 @ X7 )
      | ~ ( m1_setfam_1 @ X8 @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_compts_1])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_setfam_1 @ ( sk_B @ X0 ) @ X1 )
      | ~ ( v1_tops_2 @ ( sk_B @ X0 ) @ X0 )
      | ( m1_setfam_1 @ ( sk_D @ ( sk_B @ X0 ) @ X1 @ X0 ) @ X1 )
      | ~ ( v2_compts_1 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_compts_1 @ X1 @ X0 )
      | ( m1_setfam_1 @ ( sk_D @ ( sk_B @ X0 ) @ X1 @ X0 ) @ X1 )
      | ~ ( v1_tops_2 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( m1_setfam_1 @ ( sk_B @ X0 ) @ X1 )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_compts_1 @ X0 )
      | ~ ( m1_setfam_1 @ ( sk_B @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( v1_tops_2 @ ( sk_B @ X0 ) @ X0 )
      | ( m1_setfam_1 @ ( sk_D @ ( sk_B @ X0 ) @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['147','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ( m1_setfam_1 @ ( sk_D @ ( sk_B @ X0 ) @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( v1_tops_2 @ ( sk_B @ X0 ) @ X0 )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['146','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tops_2 @ ( sk_B @ X0 ) @ X0 )
      | ( m1_setfam_1 @ ( sk_D @ ( sk_B @ X0 ) @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_compts_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_compts_1 @ X0 )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ( m1_setfam_1 @ ( sk_D @ ( sk_B @ X0 ) @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['145','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( m1_setfam_1 @ ( sk_D @ ( sk_B @ X0 ) @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( m1_setfam_1 @ ( sk_D @ ( sk_B @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['144','156'])).

thf('158',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['95','96'])).

thf('160',plain,
    ( ( ( v1_compts_1 @ sk_A )
      | ( m1_setfam_1 @ ( sk_D @ ( sk_B @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['157','158','159'])).

thf('161',plain,
    ( ( v1_compts_1 @ sk_A )
   <= ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['143','160'])).

thf('162',plain,
    ( ~ ( v1_compts_1 @ sk_A )
   <= ~ ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['73'])).

thf('163',plain,
    ( ( v1_compts_1 @ sk_A )
    | ~ ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    ~ ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['75','163'])).

thf('165',plain,(
    ~ ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['74','164'])).

thf('166',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( v1_compts_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['72','165'])).

thf('167',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['95','96'])).

thf('169',plain,
    ( ( v1_compts_1 @ sk_A )
   <= ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['77'])).

thf('170',plain,
    ( ( v1_compts_1 @ sk_A )
    | ( v2_compts_1 @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference(split,[status(esa)],['77'])).

thf('171',plain,(
    v1_compts_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['75','163','170'])).

thf('172',plain,(
    v1_compts_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['169','171'])).

thf('173',plain,(
    $false ),
    inference(demod,[status(thm)],['166','167','168','172'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Xa4oT23m7u
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:01:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.55  % Solved by: fo/fo7.sh
% 0.38/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.55  % done 134 iterations in 0.112s
% 0.38/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.55  % SZS output start Refutation
% 0.38/0.55  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 0.38/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.55  thf(v1_finset_1_type, type, v1_finset_1: $i > $o).
% 0.38/0.55  thf(m1_setfam_1_type, type, m1_setfam_1: $i > $i > $o).
% 0.38/0.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.38/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.38/0.55  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.38/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.55  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.38/0.55  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.38/0.55  thf(v1_compts_1_type, type, v1_compts_1: $i > $o).
% 0.38/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.55  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.38/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.55  thf(dt_k2_struct_0, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( l1_struct_0 @ A ) =>
% 0.38/0.55       ( m1_subset_1 @
% 0.38/0.55         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.38/0.55  thf('0', plain,
% 0.38/0.55      (![X1 : $i]:
% 0.38/0.55         ((m1_subset_1 @ (k2_struct_0 @ X1) @ 
% 0.38/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.38/0.55          | ~ (l1_struct_0 @ X1))),
% 0.38/0.55      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.38/0.55  thf(d7_compts_1, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( l1_pre_topc @ A ) =>
% 0.38/0.55       ( ![B:$i]:
% 0.38/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.55           ( ( v2_compts_1 @ B @ A ) <=>
% 0.38/0.55             ( ![C:$i]:
% 0.38/0.55               ( ( m1_subset_1 @
% 0.38/0.55                   C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.55                 ( ~( ( m1_setfam_1 @ C @ B ) & ( v1_tops_2 @ C @ A ) & 
% 0.38/0.55                      ( ![D:$i]:
% 0.38/0.55                        ( ( m1_subset_1 @
% 0.38/0.55                            D @ 
% 0.38/0.55                            ( k1_zfmisc_1 @
% 0.38/0.55                              ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.55                          ( ~( ( r1_tarski @ D @ C ) & 
% 0.38/0.55                               ( m1_setfam_1 @ D @ B ) & ( v1_finset_1 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.55  thf('1', plain,
% 0.38/0.55      (![X6 : $i, X7 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.38/0.55          | (v1_tops_2 @ (sk_C_1 @ X6 @ X7) @ X7)
% 0.38/0.55          | (v2_compts_1 @ X6 @ X7)
% 0.38/0.55          | ~ (l1_pre_topc @ X7))),
% 0.38/0.55      inference('cnf', [status(esa)], [d7_compts_1])).
% 0.38/0.55  thf('2', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | (v1_tops_2 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.38/0.55  thf('3', plain,
% 0.38/0.55      (![X1 : $i]:
% 0.38/0.55         ((m1_subset_1 @ (k2_struct_0 @ X1) @ 
% 0.38/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.38/0.55          | ~ (l1_struct_0 @ X1))),
% 0.38/0.55      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.38/0.55  thf('4', plain,
% 0.38/0.55      (![X6 : $i, X7 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.38/0.55          | (m1_setfam_1 @ (sk_C_1 @ X6 @ X7) @ X6)
% 0.38/0.55          | (v2_compts_1 @ X6 @ X7)
% 0.38/0.55          | ~ (l1_pre_topc @ X7))),
% 0.38/0.55      inference('cnf', [status(esa)], [d7_compts_1])).
% 0.38/0.55  thf('5', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | (m1_setfam_1 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ 
% 0.38/0.55             (k2_struct_0 @ X0)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.38/0.55  thf(d3_struct_0, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.38/0.55  thf('6', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0)) | ~ (l1_struct_0 @ X0))),
% 0.38/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.55  thf('7', plain,
% 0.38/0.55      (![X1 : $i]:
% 0.38/0.55         ((m1_subset_1 @ (k2_struct_0 @ X1) @ 
% 0.38/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.38/0.55          | ~ (l1_struct_0 @ X1))),
% 0.38/0.55      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.38/0.55  thf('8', plain,
% 0.38/0.55      (![X6 : $i, X7 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.38/0.55          | (m1_subset_1 @ (sk_C_1 @ X6 @ X7) @ 
% 0.38/0.55             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.38/0.55          | (v2_compts_1 @ X6 @ X7)
% 0.38/0.55          | ~ (l1_pre_topc @ X7))),
% 0.38/0.55      inference('cnf', [status(esa)], [d7_compts_1])).
% 0.38/0.55  thf('9', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | (m1_subset_1 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ 
% 0.38/0.55             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.38/0.55  thf(d3_compts_1, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( l1_pre_topc @ A ) =>
% 0.38/0.55       ( ( v1_compts_1 @ A ) <=>
% 0.38/0.55         ( ![B:$i]:
% 0.38/0.55           ( ( m1_subset_1 @
% 0.38/0.55               B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.55             ( ~( ( m1_setfam_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.38/0.55                  ( v1_tops_2 @ B @ A ) & 
% 0.38/0.55                  ( ![C:$i]:
% 0.38/0.55                    ( ( m1_subset_1 @
% 0.38/0.55                        C @ 
% 0.38/0.55                        ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.55                      ( ~( ( r1_tarski @ C @ B ) & 
% 0.38/0.55                           ( m1_setfam_1 @ C @ ( u1_struct_0 @ A ) ) & 
% 0.38/0.55                           ( v1_finset_1 @ C ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.55  thf('10', plain,
% 0.38/0.55      (![X3 : $i, X5 : $i]:
% 0.38/0.55         (~ (v1_compts_1 @ X3)
% 0.38/0.55          | (v1_finset_1 @ (sk_C @ X5 @ X3))
% 0.38/0.55          | ~ (v1_tops_2 @ X5 @ X3)
% 0.38/0.55          | ~ (m1_setfam_1 @ X5 @ (u1_struct_0 @ X3))
% 0.38/0.55          | ~ (m1_subset_1 @ X5 @ 
% 0.38/0.55               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3))))
% 0.38/0.55          | ~ (l1_pre_topc @ X3))),
% 0.38/0.55      inference('cnf', [status(esa)], [d3_compts_1])).
% 0.38/0.55  thf('11', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (m1_setfam_1 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ 
% 0.38/0.55               (u1_struct_0 @ X0))
% 0.38/0.55          | ~ (v1_tops_2 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0)
% 0.38/0.55          | (v1_finset_1 @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0))
% 0.38/0.55          | ~ (v1_compts_1 @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.38/0.55  thf('12', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (v1_compts_1 @ X0)
% 0.38/0.55          | (v1_finset_1 @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0))
% 0.38/0.55          | ~ (v1_tops_2 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0)
% 0.38/0.55          | ~ (m1_setfam_1 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ 
% 0.38/0.55               (u1_struct_0 @ X0))
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0))),
% 0.38/0.55      inference('simplify', [status(thm)], ['11'])).
% 0.38/0.55  thf('13', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (m1_setfam_1 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ 
% 0.38/0.55             (k2_struct_0 @ X0))
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (v1_tops_2 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0)
% 0.38/0.55          | (v1_finset_1 @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0))
% 0.38/0.55          | ~ (v1_compts_1 @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['6', '12'])).
% 0.38/0.55  thf('14', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (v1_compts_1 @ X0)
% 0.38/0.55          | (v1_finset_1 @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0))
% 0.38/0.55          | ~ (v1_tops_2 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (m1_setfam_1 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ 
% 0.38/0.55               (k2_struct_0 @ X0)))),
% 0.38/0.55      inference('simplify', [status(thm)], ['13'])).
% 0.38/0.55  thf('15', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (v1_tops_2 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0)
% 0.38/0.55          | (v1_finset_1 @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0))
% 0.38/0.55          | ~ (v1_compts_1 @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['5', '14'])).
% 0.38/0.55  thf('16', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (v1_compts_1 @ X0)
% 0.38/0.55          | (v1_finset_1 @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0))
% 0.38/0.55          | ~ (v1_tops_2 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0))),
% 0.38/0.55      inference('simplify', [status(thm)], ['15'])).
% 0.38/0.55  thf('17', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | (v1_finset_1 @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0))
% 0.38/0.55          | ~ (v1_compts_1 @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['2', '16'])).
% 0.38/0.55  thf('18', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (v1_compts_1 @ X0)
% 0.38/0.55          | (v1_finset_1 @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0))
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0))),
% 0.38/0.55      inference('simplify', [status(thm)], ['17'])).
% 0.38/0.55  thf('19', plain,
% 0.38/0.55      (![X1 : $i]:
% 0.38/0.55         ((m1_subset_1 @ (k2_struct_0 @ X1) @ 
% 0.38/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.38/0.55          | ~ (l1_struct_0 @ X1))),
% 0.38/0.55      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.38/0.55  thf('20', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0)) | ~ (l1_struct_0 @ X0))),
% 0.38/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.55  thf('21', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | (v1_tops_2 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.38/0.55  thf('22', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | (m1_setfam_1 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ 
% 0.38/0.55             (k2_struct_0 @ X0)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.38/0.55  thf('23', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0)) | ~ (l1_struct_0 @ X0))),
% 0.38/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.55  thf('24', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | (m1_subset_1 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ 
% 0.38/0.55             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.38/0.55  thf('25', plain,
% 0.38/0.55      (![X3 : $i, X5 : $i]:
% 0.38/0.55         (~ (v1_compts_1 @ X3)
% 0.38/0.55          | (m1_setfam_1 @ (sk_C @ X5 @ X3) @ (u1_struct_0 @ X3))
% 0.38/0.55          | ~ (v1_tops_2 @ X5 @ X3)
% 0.38/0.55          | ~ (m1_setfam_1 @ X5 @ (u1_struct_0 @ X3))
% 0.38/0.55          | ~ (m1_subset_1 @ X5 @ 
% 0.38/0.55               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3))))
% 0.38/0.55          | ~ (l1_pre_topc @ X3))),
% 0.38/0.55      inference('cnf', [status(esa)], [d3_compts_1])).
% 0.38/0.55  thf('26', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (m1_setfam_1 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ 
% 0.38/0.55               (u1_struct_0 @ X0))
% 0.38/0.55          | ~ (v1_tops_2 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0)
% 0.38/0.55          | (m1_setfam_1 @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0) @ 
% 0.38/0.55             (u1_struct_0 @ X0))
% 0.38/0.55          | ~ (v1_compts_1 @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.55  thf('27', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (v1_compts_1 @ X0)
% 0.38/0.55          | (m1_setfam_1 @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0) @ 
% 0.38/0.55             (u1_struct_0 @ X0))
% 0.38/0.55          | ~ (v1_tops_2 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0)
% 0.38/0.55          | ~ (m1_setfam_1 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ 
% 0.38/0.55               (u1_struct_0 @ X0))
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0))),
% 0.38/0.55      inference('simplify', [status(thm)], ['26'])).
% 0.38/0.55  thf('28', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (m1_setfam_1 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ 
% 0.38/0.55             (k2_struct_0 @ X0))
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (v1_tops_2 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0)
% 0.38/0.55          | (m1_setfam_1 @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0) @ 
% 0.38/0.55             (u1_struct_0 @ X0))
% 0.38/0.55          | ~ (v1_compts_1 @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['23', '27'])).
% 0.38/0.55  thf('29', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (v1_compts_1 @ X0)
% 0.38/0.55          | (m1_setfam_1 @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0) @ 
% 0.38/0.55             (u1_struct_0 @ X0))
% 0.38/0.55          | ~ (v1_tops_2 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (m1_setfam_1 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ 
% 0.38/0.55               (k2_struct_0 @ X0)))),
% 0.38/0.55      inference('simplify', [status(thm)], ['28'])).
% 0.38/0.55  thf('30', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (v1_tops_2 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0)
% 0.38/0.55          | (m1_setfam_1 @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0) @ 
% 0.38/0.55             (u1_struct_0 @ X0))
% 0.38/0.55          | ~ (v1_compts_1 @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['22', '29'])).
% 0.38/0.55  thf('31', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (v1_compts_1 @ X0)
% 0.38/0.55          | (m1_setfam_1 @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0) @ 
% 0.38/0.55             (u1_struct_0 @ X0))
% 0.38/0.55          | ~ (v1_tops_2 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0))),
% 0.38/0.55      inference('simplify', [status(thm)], ['30'])).
% 0.38/0.55  thf('32', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | (m1_setfam_1 @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0) @ 
% 0.38/0.55             (u1_struct_0 @ X0))
% 0.38/0.55          | ~ (v1_compts_1 @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['21', '31'])).
% 0.38/0.55  thf('33', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (v1_compts_1 @ X0)
% 0.38/0.55          | (m1_setfam_1 @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0) @ 
% 0.38/0.55             (u1_struct_0 @ X0))
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0))),
% 0.38/0.55      inference('simplify', [status(thm)], ['32'])).
% 0.38/0.55  thf('34', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((m1_setfam_1 @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0) @ 
% 0.38/0.55           (k2_struct_0 @ X0))
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (v1_compts_1 @ X0))),
% 0.38/0.55      inference('sup+', [status(thm)], ['20', '33'])).
% 0.38/0.55  thf('35', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (v1_compts_1 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | (m1_setfam_1 @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0) @ 
% 0.38/0.55             (k2_struct_0 @ X0)))),
% 0.38/0.55      inference('simplify', [status(thm)], ['34'])).
% 0.38/0.55  thf('36', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | (v1_tops_2 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.38/0.55  thf('37', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | (m1_setfam_1 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ 
% 0.38/0.55             (k2_struct_0 @ X0)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.38/0.55  thf('38', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0)) | ~ (l1_struct_0 @ X0))),
% 0.38/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.55  thf('39', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | (m1_subset_1 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ 
% 0.38/0.55             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.38/0.55  thf('40', plain,
% 0.38/0.55      (![X3 : $i, X5 : $i]:
% 0.38/0.55         (~ (v1_compts_1 @ X3)
% 0.38/0.55          | (r1_tarski @ (sk_C @ X5 @ X3) @ X5)
% 0.38/0.55          | ~ (v1_tops_2 @ X5 @ X3)
% 0.38/0.55          | ~ (m1_setfam_1 @ X5 @ (u1_struct_0 @ X3))
% 0.38/0.55          | ~ (m1_subset_1 @ X5 @ 
% 0.38/0.55               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3))))
% 0.38/0.55          | ~ (l1_pre_topc @ X3))),
% 0.38/0.55      inference('cnf', [status(esa)], [d3_compts_1])).
% 0.38/0.55  thf('41', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (m1_setfam_1 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ 
% 0.38/0.55               (u1_struct_0 @ X0))
% 0.38/0.55          | ~ (v1_tops_2 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0)
% 0.38/0.55          | (r1_tarski @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0) @ 
% 0.38/0.55             (sk_C_1 @ (k2_struct_0 @ X0) @ X0))
% 0.38/0.55          | ~ (v1_compts_1 @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['39', '40'])).
% 0.38/0.55  thf('42', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (v1_compts_1 @ X0)
% 0.38/0.55          | (r1_tarski @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0) @ 
% 0.38/0.55             (sk_C_1 @ (k2_struct_0 @ X0) @ X0))
% 0.38/0.55          | ~ (v1_tops_2 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0)
% 0.38/0.55          | ~ (m1_setfam_1 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ 
% 0.38/0.55               (u1_struct_0 @ X0))
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0))),
% 0.38/0.55      inference('simplify', [status(thm)], ['41'])).
% 0.38/0.55  thf('43', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (m1_setfam_1 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ 
% 0.38/0.55             (k2_struct_0 @ X0))
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (v1_tops_2 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0)
% 0.38/0.55          | (r1_tarski @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0) @ 
% 0.38/0.55             (sk_C_1 @ (k2_struct_0 @ X0) @ X0))
% 0.38/0.55          | ~ (v1_compts_1 @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['38', '42'])).
% 0.38/0.55  thf('44', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (v1_compts_1 @ X0)
% 0.38/0.55          | (r1_tarski @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0) @ 
% 0.38/0.55             (sk_C_1 @ (k2_struct_0 @ X0) @ X0))
% 0.38/0.55          | ~ (v1_tops_2 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (m1_setfam_1 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ 
% 0.38/0.55               (k2_struct_0 @ X0)))),
% 0.38/0.55      inference('simplify', [status(thm)], ['43'])).
% 0.38/0.55  thf('45', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (v1_tops_2 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0)
% 0.38/0.55          | (r1_tarski @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0) @ 
% 0.38/0.55             (sk_C_1 @ (k2_struct_0 @ X0) @ X0))
% 0.38/0.55          | ~ (v1_compts_1 @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['37', '44'])).
% 0.38/0.55  thf('46', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (v1_compts_1 @ X0)
% 0.38/0.55          | (r1_tarski @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0) @ 
% 0.38/0.55             (sk_C_1 @ (k2_struct_0 @ X0) @ X0))
% 0.38/0.55          | ~ (v1_tops_2 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0))),
% 0.38/0.55      inference('simplify', [status(thm)], ['45'])).
% 0.38/0.55  thf('47', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | (r1_tarski @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0) @ 
% 0.38/0.55             (sk_C_1 @ (k2_struct_0 @ X0) @ X0))
% 0.38/0.55          | ~ (v1_compts_1 @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['36', '46'])).
% 0.38/0.55  thf('48', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (v1_compts_1 @ X0)
% 0.38/0.55          | (r1_tarski @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0) @ 
% 0.38/0.55             (sk_C_1 @ (k2_struct_0 @ X0) @ X0))
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0))),
% 0.38/0.55      inference('simplify', [status(thm)], ['47'])).
% 0.38/0.55  thf('49', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | (v1_tops_2 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.38/0.55  thf('50', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | (m1_setfam_1 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ 
% 0.38/0.55             (k2_struct_0 @ X0)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.38/0.55  thf('51', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0)) | ~ (l1_struct_0 @ X0))),
% 0.38/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.55  thf('52', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | (m1_subset_1 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ 
% 0.38/0.55             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.38/0.55  thf('53', plain,
% 0.38/0.55      (![X3 : $i, X5 : $i]:
% 0.38/0.55         (~ (v1_compts_1 @ X3)
% 0.38/0.55          | (m1_subset_1 @ (sk_C @ X5 @ X3) @ 
% 0.38/0.55             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3))))
% 0.38/0.55          | ~ (v1_tops_2 @ X5 @ X3)
% 0.38/0.55          | ~ (m1_setfam_1 @ X5 @ (u1_struct_0 @ X3))
% 0.38/0.55          | ~ (m1_subset_1 @ X5 @ 
% 0.38/0.55               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3))))
% 0.38/0.55          | ~ (l1_pre_topc @ X3))),
% 0.38/0.55      inference('cnf', [status(esa)], [d3_compts_1])).
% 0.38/0.55  thf('54', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (m1_setfam_1 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ 
% 0.38/0.55               (u1_struct_0 @ X0))
% 0.38/0.55          | ~ (v1_tops_2 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0)
% 0.38/0.55          | (m1_subset_1 @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0) @ 
% 0.38/0.55             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.38/0.55          | ~ (v1_compts_1 @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['52', '53'])).
% 0.38/0.55  thf('55', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (v1_compts_1 @ X0)
% 0.38/0.55          | (m1_subset_1 @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0) @ 
% 0.38/0.55             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.38/0.55          | ~ (v1_tops_2 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0)
% 0.38/0.55          | ~ (m1_setfam_1 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ 
% 0.38/0.55               (u1_struct_0 @ X0))
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0))),
% 0.38/0.55      inference('simplify', [status(thm)], ['54'])).
% 0.38/0.55  thf('56', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (m1_setfam_1 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ 
% 0.38/0.55             (k2_struct_0 @ X0))
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (v1_tops_2 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0)
% 0.38/0.55          | (m1_subset_1 @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0) @ 
% 0.38/0.55             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.38/0.55          | ~ (v1_compts_1 @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['51', '55'])).
% 0.38/0.55  thf('57', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (v1_compts_1 @ X0)
% 0.38/0.55          | (m1_subset_1 @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0) @ 
% 0.38/0.55             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.38/0.55          | ~ (v1_tops_2 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (m1_setfam_1 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ 
% 0.38/0.55               (k2_struct_0 @ X0)))),
% 0.38/0.55      inference('simplify', [status(thm)], ['56'])).
% 0.38/0.55  thf('58', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (v1_tops_2 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0)
% 0.38/0.55          | (m1_subset_1 @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0) @ 
% 0.38/0.55             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.38/0.55          | ~ (v1_compts_1 @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['50', '57'])).
% 0.38/0.55  thf('59', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (v1_compts_1 @ X0)
% 0.38/0.55          | (m1_subset_1 @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0) @ 
% 0.38/0.55             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.38/0.55          | ~ (v1_tops_2 @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0))),
% 0.38/0.55      inference('simplify', [status(thm)], ['58'])).
% 0.38/0.55  thf('60', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | (m1_subset_1 @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0) @ 
% 0.38/0.55             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.38/0.55          | ~ (v1_compts_1 @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['49', '59'])).
% 0.38/0.55  thf('61', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (v1_compts_1 @ X0)
% 0.38/0.55          | (m1_subset_1 @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0) @ 
% 0.38/0.55             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0))),
% 0.38/0.55      inference('simplify', [status(thm)], ['60'])).
% 0.38/0.55  thf('62', plain,
% 0.38/0.55      (![X6 : $i, X7 : $i, X9 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.38/0.55          | ~ (m1_subset_1 @ X9 @ 
% 0.38/0.55               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.38/0.55          | ~ (r1_tarski @ X9 @ (sk_C_1 @ X6 @ X7))
% 0.38/0.55          | ~ (m1_setfam_1 @ X9 @ X6)
% 0.38/0.55          | ~ (v1_finset_1 @ X9)
% 0.38/0.55          | (v2_compts_1 @ X6 @ X7)
% 0.38/0.55          | ~ (l1_pre_topc @ X7))),
% 0.38/0.55      inference('cnf', [status(esa)], [d7_compts_1])).
% 0.38/0.55  thf('63', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         ((v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (v1_compts_1 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_compts_1 @ X1 @ X0)
% 0.38/0.55          | ~ (v1_finset_1 @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0))
% 0.38/0.55          | ~ (m1_setfam_1 @ 
% 0.38/0.55               (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0) @ X1)
% 0.38/0.55          | ~ (r1_tarski @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0) @ 
% 0.38/0.55               (sk_C_1 @ X1 @ X0))
% 0.38/0.55          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['61', '62'])).
% 0.38/0.55  thf('64', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.38/0.55          | ~ (r1_tarski @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0) @ 
% 0.38/0.55               (sk_C_1 @ X1 @ X0))
% 0.38/0.55          | ~ (m1_setfam_1 @ 
% 0.38/0.55               (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0) @ X1)
% 0.38/0.55          | ~ (v1_finset_1 @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0))
% 0.38/0.55          | (v2_compts_1 @ X1 @ X0)
% 0.38/0.55          | ~ (v1_compts_1 @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0))),
% 0.38/0.55      inference('simplify', [status(thm)], ['63'])).
% 0.38/0.55  thf('65', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (v1_compts_1 @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (v1_compts_1 @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | ~ (v1_finset_1 @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0))
% 0.38/0.55          | ~ (m1_setfam_1 @ 
% 0.38/0.55               (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0) @ 
% 0.38/0.55               (k2_struct_0 @ X0))
% 0.38/0.55          | ~ (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 0.38/0.55               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['48', '64'])).
% 0.38/0.55  thf('66', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 0.38/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.38/0.55          | ~ (m1_setfam_1 @ 
% 0.38/0.55               (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0) @ 
% 0.38/0.55               (k2_struct_0 @ X0))
% 0.38/0.55          | ~ (v1_finset_1 @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0))
% 0.38/0.55          | ~ (v1_compts_1 @ X0)
% 0.38/0.55          | ~ (l1_struct_0 @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0))),
% 0.38/0.55      inference('simplify', [status(thm)], ['65'])).
% 0.38/0.55  thf('67', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (~ (l1_struct_0 @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | ~ (v1_compts_1 @ X0)
% 0.38/0.55          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | ~ (l1_struct_0 @ X0)
% 0.38/0.56          | ~ (v1_compts_1 @ X0)
% 0.38/0.56          | ~ (v1_finset_1 @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0))
% 0.38/0.56          | ~ (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 0.38/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['35', '66'])).
% 0.38/0.56  thf('68', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 0.38/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.38/0.56          | ~ (v1_finset_1 @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0))
% 0.38/0.56          | ~ (v1_compts_1 @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.56          | ~ (l1_struct_0 @ X0))),
% 0.38/0.56      inference('simplify', [status(thm)], ['67'])).
% 0.38/0.56  thf('69', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (l1_struct_0 @ X0)
% 0.38/0.56          | ~ (l1_struct_0 @ X0)
% 0.38/0.56          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | ~ (v1_compts_1 @ X0)
% 0.38/0.56          | ~ (v1_finset_1 @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['19', '68'])).
% 0.38/0.56  thf('70', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (v1_finset_1 @ (sk_C @ (sk_C_1 @ (k2_struct_0 @ X0) @ X0) @ X0))
% 0.38/0.56          | ~ (v1_compts_1 @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.56          | ~ (l1_struct_0 @ X0))),
% 0.38/0.56      inference('simplify', [status(thm)], ['69'])).
% 0.38/0.56  thf('71', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | ~ (l1_struct_0 @ X0)
% 0.38/0.56          | ~ (v1_compts_1 @ X0)
% 0.38/0.56          | ~ (l1_struct_0 @ X0)
% 0.38/0.56          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | ~ (v1_compts_1 @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['18', '70'])).
% 0.38/0.56  thf('72', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (v1_compts_1 @ X0)
% 0.38/0.56          | ~ (l1_struct_0 @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | (v2_compts_1 @ (k2_struct_0 @ X0) @ X0))),
% 0.38/0.56      inference('simplify', [status(thm)], ['71'])).
% 0.38/0.56  thf(t10_compts_1, conjecture,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( l1_pre_topc @ A ) =>
% 0.38/0.56       ( ( v1_compts_1 @ A ) <=> ( v2_compts_1 @ ( k2_struct_0 @ A ) @ A ) ) ))).
% 0.38/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.56    (~( ![A:$i]:
% 0.38/0.56        ( ( l1_pre_topc @ A ) =>
% 0.38/0.56          ( ( v1_compts_1 @ A ) <=> ( v2_compts_1 @ ( k2_struct_0 @ A ) @ A ) ) ) )),
% 0.38/0.56    inference('cnf.neg', [status(esa)], [t10_compts_1])).
% 0.38/0.56  thf('73', plain,
% 0.38/0.56      ((~ (v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A) | ~ (v1_compts_1 @ sk_A))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('74', plain,
% 0.38/0.56      ((~ (v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A))
% 0.38/0.56         <= (~ ((v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A)))),
% 0.38/0.56      inference('split', [status(esa)], ['73'])).
% 0.38/0.56  thf('75', plain,
% 0.38/0.56      (~ ((v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A)) | 
% 0.38/0.56       ~ ((v1_compts_1 @ sk_A))),
% 0.38/0.56      inference('split', [status(esa)], ['73'])).
% 0.38/0.56  thf('76', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0)) | ~ (l1_struct_0 @ X0))),
% 0.38/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.56  thf('77', plain,
% 0.38/0.56      (((v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A) | (v1_compts_1 @ sk_A))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('78', plain,
% 0.38/0.56      (((v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A))
% 0.38/0.56         <= (((v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A)))),
% 0.38/0.56      inference('split', [status(esa)], ['77'])).
% 0.38/0.56  thf('79', plain,
% 0.38/0.56      (![X3 : $i]:
% 0.38/0.56         ((v1_tops_2 @ (sk_B @ X3) @ X3)
% 0.38/0.56          | (v1_compts_1 @ X3)
% 0.38/0.56          | ~ (l1_pre_topc @ X3))),
% 0.38/0.56      inference('cnf', [status(esa)], [d3_compts_1])).
% 0.38/0.56  thf('80', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0)) | ~ (l1_struct_0 @ X0))),
% 0.38/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.56  thf('81', plain,
% 0.38/0.56      (![X3 : $i]:
% 0.38/0.56         ((m1_setfam_1 @ (sk_B @ X3) @ (u1_struct_0 @ X3))
% 0.38/0.56          | (v1_compts_1 @ X3)
% 0.38/0.56          | ~ (l1_pre_topc @ X3))),
% 0.38/0.56      inference('cnf', [status(esa)], [d3_compts_1])).
% 0.38/0.56  thf('82', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((m1_setfam_1 @ (sk_B @ X0) @ (k2_struct_0 @ X0))
% 0.38/0.56          | ~ (l1_struct_0 @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | (v1_compts_1 @ X0))),
% 0.38/0.56      inference('sup+', [status(thm)], ['80', '81'])).
% 0.38/0.56  thf('83', plain,
% 0.38/0.56      (![X1 : $i]:
% 0.38/0.56         ((m1_subset_1 @ (k2_struct_0 @ X1) @ 
% 0.38/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.38/0.56          | ~ (l1_struct_0 @ X1))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.38/0.56  thf('84', plain,
% 0.38/0.56      (![X3 : $i]:
% 0.38/0.56         ((m1_subset_1 @ (sk_B @ X3) @ 
% 0.38/0.56           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3))))
% 0.38/0.56          | (v1_compts_1 @ X3)
% 0.38/0.56          | ~ (l1_pre_topc @ X3))),
% 0.38/0.56      inference('cnf', [status(esa)], [d3_compts_1])).
% 0.38/0.56  thf('85', plain,
% 0.38/0.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.38/0.56          | ~ (v2_compts_1 @ X6 @ X7)
% 0.38/0.56          | (r1_tarski @ (sk_D @ X8 @ X6 @ X7) @ X8)
% 0.38/0.56          | ~ (v1_tops_2 @ X8 @ X7)
% 0.38/0.56          | ~ (m1_setfam_1 @ X8 @ X6)
% 0.38/0.56          | ~ (m1_subset_1 @ X8 @ 
% 0.38/0.56               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.38/0.56          | ~ (l1_pre_topc @ X7))),
% 0.38/0.56      inference('cnf', [status(esa)], [d7_compts_1])).
% 0.38/0.56  thf('86', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (~ (l1_pre_topc @ X0)
% 0.38/0.56          | (v1_compts_1 @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | ~ (m1_setfam_1 @ (sk_B @ X0) @ X1)
% 0.38/0.56          | ~ (v1_tops_2 @ (sk_B @ X0) @ X0)
% 0.38/0.56          | (r1_tarski @ (sk_D @ (sk_B @ X0) @ X1 @ X0) @ (sk_B @ X0))
% 0.38/0.56          | ~ (v2_compts_1 @ X1 @ X0)
% 0.38/0.56          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['84', '85'])).
% 0.38/0.56  thf('87', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.38/0.56          | ~ (v2_compts_1 @ X1 @ X0)
% 0.38/0.56          | (r1_tarski @ (sk_D @ (sk_B @ X0) @ X1 @ X0) @ (sk_B @ X0))
% 0.38/0.56          | ~ (v1_tops_2 @ (sk_B @ X0) @ X0)
% 0.38/0.56          | ~ (m1_setfam_1 @ (sk_B @ X0) @ X1)
% 0.38/0.56          | (v1_compts_1 @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0))),
% 0.38/0.56      inference('simplify', [status(thm)], ['86'])).
% 0.38/0.56  thf('88', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (l1_struct_0 @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | (v1_compts_1 @ X0)
% 0.38/0.56          | ~ (m1_setfam_1 @ (sk_B @ X0) @ (k2_struct_0 @ X0))
% 0.38/0.56          | ~ (v1_tops_2 @ (sk_B @ X0) @ X0)
% 0.38/0.56          | (r1_tarski @ (sk_D @ (sk_B @ X0) @ (k2_struct_0 @ X0) @ X0) @ 
% 0.38/0.56             (sk_B @ X0))
% 0.38/0.56          | ~ (v2_compts_1 @ (k2_struct_0 @ X0) @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['83', '87'])).
% 0.38/0.56  thf('89', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((v1_compts_1 @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | ~ (l1_struct_0 @ X0)
% 0.38/0.56          | ~ (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.56          | (r1_tarski @ (sk_D @ (sk_B @ X0) @ (k2_struct_0 @ X0) @ X0) @ 
% 0.38/0.56             (sk_B @ X0))
% 0.38/0.56          | ~ (v1_tops_2 @ (sk_B @ X0) @ X0)
% 0.38/0.56          | (v1_compts_1 @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | ~ (l1_struct_0 @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['82', '88'])).
% 0.38/0.56  thf('90', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (v1_tops_2 @ (sk_B @ X0) @ X0)
% 0.38/0.56          | (r1_tarski @ (sk_D @ (sk_B @ X0) @ (k2_struct_0 @ X0) @ X0) @ 
% 0.38/0.56             (sk_B @ X0))
% 0.38/0.56          | ~ (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.56          | ~ (l1_struct_0 @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | (v1_compts_1 @ X0))),
% 0.38/0.56      inference('simplify', [status(thm)], ['89'])).
% 0.38/0.56  thf('91', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (l1_pre_topc @ X0)
% 0.38/0.56          | (v1_compts_1 @ X0)
% 0.38/0.56          | (v1_compts_1 @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | ~ (l1_struct_0 @ X0)
% 0.38/0.56          | ~ (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.56          | (r1_tarski @ (sk_D @ (sk_B @ X0) @ (k2_struct_0 @ X0) @ X0) @ 
% 0.38/0.56             (sk_B @ X0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['79', '90'])).
% 0.38/0.56  thf('92', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((r1_tarski @ (sk_D @ (sk_B @ X0) @ (k2_struct_0 @ X0) @ X0) @ 
% 0.38/0.56           (sk_B @ X0))
% 0.38/0.56          | ~ (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.56          | ~ (l1_struct_0 @ X0)
% 0.38/0.56          | (v1_compts_1 @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0))),
% 0.38/0.56      inference('simplify', [status(thm)], ['91'])).
% 0.38/0.56  thf('93', plain,
% 0.38/0.56      (((~ (l1_pre_topc @ sk_A)
% 0.38/0.56         | (v1_compts_1 @ sk_A)
% 0.38/0.56         | ~ (l1_struct_0 @ sk_A)
% 0.38/0.56         | (r1_tarski @ (sk_D @ (sk_B @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_A) @ 
% 0.38/0.56            (sk_B @ sk_A))))
% 0.38/0.56         <= (((v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['78', '92'])).
% 0.38/0.56  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(dt_l1_pre_topc, axiom,
% 0.38/0.56    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.38/0.56  thf('96', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.56  thf('97', plain, ((l1_struct_0 @ sk_A)),
% 0.38/0.56      inference('sup-', [status(thm)], ['95', '96'])).
% 0.38/0.56  thf('98', plain,
% 0.38/0.56      ((((v1_compts_1 @ sk_A)
% 0.38/0.56         | (r1_tarski @ (sk_D @ (sk_B @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_A) @ 
% 0.38/0.56            (sk_B @ sk_A))))
% 0.38/0.56         <= (((v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A)))),
% 0.38/0.56      inference('demod', [status(thm)], ['93', '94', '97'])).
% 0.38/0.56  thf('99', plain,
% 0.38/0.56      (((v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A))
% 0.38/0.56         <= (((v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A)))),
% 0.38/0.56      inference('split', [status(esa)], ['77'])).
% 0.38/0.56  thf('100', plain,
% 0.38/0.56      (![X3 : $i]:
% 0.38/0.56         ((v1_tops_2 @ (sk_B @ X3) @ X3)
% 0.38/0.56          | (v1_compts_1 @ X3)
% 0.38/0.56          | ~ (l1_pre_topc @ X3))),
% 0.38/0.56      inference('cnf', [status(esa)], [d3_compts_1])).
% 0.38/0.56  thf('101', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((m1_setfam_1 @ (sk_B @ X0) @ (k2_struct_0 @ X0))
% 0.38/0.56          | ~ (l1_struct_0 @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | (v1_compts_1 @ X0))),
% 0.38/0.56      inference('sup+', [status(thm)], ['80', '81'])).
% 0.38/0.56  thf('102', plain,
% 0.38/0.56      (![X1 : $i]:
% 0.38/0.56         ((m1_subset_1 @ (k2_struct_0 @ X1) @ 
% 0.38/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.38/0.56          | ~ (l1_struct_0 @ X1))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.38/0.56  thf('103', plain,
% 0.38/0.56      (![X3 : $i]:
% 0.38/0.56         ((m1_subset_1 @ (sk_B @ X3) @ 
% 0.38/0.56           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3))))
% 0.38/0.56          | (v1_compts_1 @ X3)
% 0.38/0.56          | ~ (l1_pre_topc @ X3))),
% 0.38/0.56      inference('cnf', [status(esa)], [d3_compts_1])).
% 0.38/0.56  thf('104', plain,
% 0.38/0.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.38/0.56          | ~ (v2_compts_1 @ X6 @ X7)
% 0.38/0.56          | (m1_subset_1 @ (sk_D @ X8 @ X6 @ X7) @ 
% 0.38/0.56             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.38/0.56          | ~ (v1_tops_2 @ X8 @ X7)
% 0.38/0.56          | ~ (m1_setfam_1 @ X8 @ X6)
% 0.38/0.56          | ~ (m1_subset_1 @ X8 @ 
% 0.38/0.56               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.38/0.56          | ~ (l1_pre_topc @ X7))),
% 0.38/0.56      inference('cnf', [status(esa)], [d7_compts_1])).
% 0.38/0.56  thf('105', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (~ (l1_pre_topc @ X0)
% 0.38/0.56          | (v1_compts_1 @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | ~ (m1_setfam_1 @ (sk_B @ X0) @ X1)
% 0.38/0.56          | ~ (v1_tops_2 @ (sk_B @ X0) @ X0)
% 0.38/0.56          | (m1_subset_1 @ (sk_D @ (sk_B @ X0) @ X1 @ X0) @ 
% 0.38/0.56             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.38/0.56          | ~ (v2_compts_1 @ X1 @ X0)
% 0.38/0.56          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['103', '104'])).
% 0.38/0.56  thf('106', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.38/0.56          | ~ (v2_compts_1 @ X1 @ X0)
% 0.38/0.56          | (m1_subset_1 @ (sk_D @ (sk_B @ X0) @ X1 @ X0) @ 
% 0.38/0.56             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.38/0.56          | ~ (v1_tops_2 @ (sk_B @ X0) @ X0)
% 0.38/0.56          | ~ (m1_setfam_1 @ (sk_B @ X0) @ X1)
% 0.38/0.56          | (v1_compts_1 @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0))),
% 0.38/0.56      inference('simplify', [status(thm)], ['105'])).
% 0.38/0.56  thf('107', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (l1_struct_0 @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | (v1_compts_1 @ X0)
% 0.38/0.56          | ~ (m1_setfam_1 @ (sk_B @ X0) @ (k2_struct_0 @ X0))
% 0.38/0.56          | ~ (v1_tops_2 @ (sk_B @ X0) @ X0)
% 0.38/0.56          | (m1_subset_1 @ (sk_D @ (sk_B @ X0) @ (k2_struct_0 @ X0) @ X0) @ 
% 0.38/0.56             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.38/0.56          | ~ (v2_compts_1 @ (k2_struct_0 @ X0) @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['102', '106'])).
% 0.38/0.56  thf('108', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((v1_compts_1 @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | ~ (l1_struct_0 @ X0)
% 0.38/0.56          | ~ (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.56          | (m1_subset_1 @ (sk_D @ (sk_B @ X0) @ (k2_struct_0 @ X0) @ X0) @ 
% 0.38/0.56             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.38/0.56          | ~ (v1_tops_2 @ (sk_B @ X0) @ X0)
% 0.38/0.56          | (v1_compts_1 @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | ~ (l1_struct_0 @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['101', '107'])).
% 0.38/0.56  thf('109', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (v1_tops_2 @ (sk_B @ X0) @ X0)
% 0.38/0.56          | (m1_subset_1 @ (sk_D @ (sk_B @ X0) @ (k2_struct_0 @ X0) @ X0) @ 
% 0.38/0.56             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.38/0.56          | ~ (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.56          | ~ (l1_struct_0 @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | (v1_compts_1 @ X0))),
% 0.38/0.56      inference('simplify', [status(thm)], ['108'])).
% 0.38/0.56  thf('110', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (l1_pre_topc @ X0)
% 0.38/0.56          | (v1_compts_1 @ X0)
% 0.38/0.56          | (v1_compts_1 @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | ~ (l1_struct_0 @ X0)
% 0.38/0.56          | ~ (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.56          | (m1_subset_1 @ (sk_D @ (sk_B @ X0) @ (k2_struct_0 @ X0) @ X0) @ 
% 0.38/0.56             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['100', '109'])).
% 0.38/0.56  thf('111', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((m1_subset_1 @ (sk_D @ (sk_B @ X0) @ (k2_struct_0 @ X0) @ X0) @ 
% 0.38/0.56           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.38/0.56          | ~ (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.56          | ~ (l1_struct_0 @ X0)
% 0.38/0.56          | (v1_compts_1 @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0))),
% 0.38/0.56      inference('simplify', [status(thm)], ['110'])).
% 0.38/0.56  thf('112', plain,
% 0.38/0.56      (((~ (l1_pre_topc @ sk_A)
% 0.38/0.56         | (v1_compts_1 @ sk_A)
% 0.38/0.56         | ~ (l1_struct_0 @ sk_A)
% 0.38/0.56         | (m1_subset_1 @ 
% 0.38/0.56            (sk_D @ (sk_B @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_A) @ 
% 0.38/0.56            (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))
% 0.38/0.56         <= (((v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['99', '111'])).
% 0.38/0.56  thf('113', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('114', plain, ((l1_struct_0 @ sk_A)),
% 0.38/0.56      inference('sup-', [status(thm)], ['95', '96'])).
% 0.38/0.56  thf('115', plain,
% 0.38/0.56      ((((v1_compts_1 @ sk_A)
% 0.38/0.56         | (m1_subset_1 @ 
% 0.38/0.56            (sk_D @ (sk_B @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_A) @ 
% 0.38/0.56            (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))))
% 0.38/0.56         <= (((v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A)))),
% 0.38/0.56      inference('demod', [status(thm)], ['112', '113', '114'])).
% 0.38/0.56  thf('116', plain,
% 0.38/0.56      (![X3 : $i, X4 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X4 @ 
% 0.38/0.56             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3))))
% 0.38/0.56          | ~ (r1_tarski @ X4 @ (sk_B @ X3))
% 0.38/0.56          | ~ (m1_setfam_1 @ X4 @ (u1_struct_0 @ X3))
% 0.38/0.56          | ~ (v1_finset_1 @ X4)
% 0.38/0.56          | (v1_compts_1 @ X3)
% 0.38/0.56          | ~ (l1_pre_topc @ X3))),
% 0.38/0.56      inference('cnf', [status(esa)], [d3_compts_1])).
% 0.38/0.56  thf('117', plain,
% 0.38/0.56      ((((v1_compts_1 @ sk_A)
% 0.38/0.56         | ~ (l1_pre_topc @ sk_A)
% 0.38/0.56         | (v1_compts_1 @ sk_A)
% 0.38/0.56         | ~ (v1_finset_1 @ 
% 0.38/0.56              (sk_D @ (sk_B @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_A))
% 0.38/0.56         | ~ (m1_setfam_1 @ 
% 0.38/0.56              (sk_D @ (sk_B @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_A) @ 
% 0.38/0.56              (u1_struct_0 @ sk_A))
% 0.38/0.56         | ~ (r1_tarski @ 
% 0.38/0.56              (sk_D @ (sk_B @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_A) @ 
% 0.38/0.56              (sk_B @ sk_A))))
% 0.38/0.56         <= (((v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['115', '116'])).
% 0.38/0.56  thf('118', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('119', plain,
% 0.38/0.56      ((((v1_compts_1 @ sk_A)
% 0.38/0.56         | (v1_compts_1 @ sk_A)
% 0.38/0.56         | ~ (v1_finset_1 @ 
% 0.38/0.56              (sk_D @ (sk_B @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_A))
% 0.38/0.56         | ~ (m1_setfam_1 @ 
% 0.38/0.56              (sk_D @ (sk_B @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_A) @ 
% 0.38/0.56              (u1_struct_0 @ sk_A))
% 0.38/0.56         | ~ (r1_tarski @ 
% 0.38/0.56              (sk_D @ (sk_B @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_A) @ 
% 0.38/0.56              (sk_B @ sk_A))))
% 0.38/0.56         <= (((v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A)))),
% 0.38/0.56      inference('demod', [status(thm)], ['117', '118'])).
% 0.38/0.56  thf('120', plain,
% 0.38/0.56      (((~ (r1_tarski @ (sk_D @ (sk_B @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_A) @ 
% 0.38/0.56            (sk_B @ sk_A))
% 0.38/0.56         | ~ (m1_setfam_1 @ 
% 0.38/0.56              (sk_D @ (sk_B @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_A) @ 
% 0.38/0.56              (u1_struct_0 @ sk_A))
% 0.38/0.56         | ~ (v1_finset_1 @ 
% 0.38/0.56              (sk_D @ (sk_B @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_A))
% 0.38/0.56         | (v1_compts_1 @ sk_A)))
% 0.38/0.56         <= (((v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['119'])).
% 0.38/0.56  thf('121', plain,
% 0.38/0.56      ((((v1_compts_1 @ sk_A)
% 0.38/0.56         | (v1_compts_1 @ sk_A)
% 0.38/0.56         | ~ (v1_finset_1 @ 
% 0.38/0.56              (sk_D @ (sk_B @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_A))
% 0.38/0.56         | ~ (m1_setfam_1 @ 
% 0.38/0.56              (sk_D @ (sk_B @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_A) @ 
% 0.38/0.56              (u1_struct_0 @ sk_A))))
% 0.38/0.56         <= (((v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['98', '120'])).
% 0.38/0.56  thf('122', plain,
% 0.38/0.56      (((~ (m1_setfam_1 @ 
% 0.38/0.56            (sk_D @ (sk_B @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_A) @ 
% 0.38/0.56            (u1_struct_0 @ sk_A))
% 0.38/0.56         | ~ (v1_finset_1 @ 
% 0.38/0.56              (sk_D @ (sk_B @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_A))
% 0.38/0.56         | (v1_compts_1 @ sk_A)))
% 0.38/0.56         <= (((v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['121'])).
% 0.38/0.56  thf('123', plain,
% 0.38/0.56      (((v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A))
% 0.38/0.56         <= (((v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A)))),
% 0.38/0.56      inference('split', [status(esa)], ['77'])).
% 0.38/0.56  thf('124', plain,
% 0.38/0.56      (![X3 : $i]:
% 0.38/0.56         ((v1_tops_2 @ (sk_B @ X3) @ X3)
% 0.38/0.56          | (v1_compts_1 @ X3)
% 0.38/0.56          | ~ (l1_pre_topc @ X3))),
% 0.38/0.56      inference('cnf', [status(esa)], [d3_compts_1])).
% 0.38/0.56  thf('125', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((m1_setfam_1 @ (sk_B @ X0) @ (k2_struct_0 @ X0))
% 0.38/0.56          | ~ (l1_struct_0 @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | (v1_compts_1 @ X0))),
% 0.38/0.56      inference('sup+', [status(thm)], ['80', '81'])).
% 0.38/0.56  thf('126', plain,
% 0.38/0.56      (![X1 : $i]:
% 0.38/0.56         ((m1_subset_1 @ (k2_struct_0 @ X1) @ 
% 0.38/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.38/0.56          | ~ (l1_struct_0 @ X1))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.38/0.56  thf('127', plain,
% 0.38/0.56      (![X3 : $i]:
% 0.38/0.56         ((m1_subset_1 @ (sk_B @ X3) @ 
% 0.38/0.56           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3))))
% 0.38/0.56          | (v1_compts_1 @ X3)
% 0.38/0.56          | ~ (l1_pre_topc @ X3))),
% 0.38/0.56      inference('cnf', [status(esa)], [d3_compts_1])).
% 0.38/0.56  thf('128', plain,
% 0.38/0.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.38/0.56          | ~ (v2_compts_1 @ X6 @ X7)
% 0.38/0.56          | (v1_finset_1 @ (sk_D @ X8 @ X6 @ X7))
% 0.38/0.56          | ~ (v1_tops_2 @ X8 @ X7)
% 0.38/0.56          | ~ (m1_setfam_1 @ X8 @ X6)
% 0.38/0.56          | ~ (m1_subset_1 @ X8 @ 
% 0.38/0.56               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.38/0.56          | ~ (l1_pre_topc @ X7))),
% 0.38/0.56      inference('cnf', [status(esa)], [d7_compts_1])).
% 0.38/0.56  thf('129', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (~ (l1_pre_topc @ X0)
% 0.38/0.56          | (v1_compts_1 @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | ~ (m1_setfam_1 @ (sk_B @ X0) @ X1)
% 0.38/0.56          | ~ (v1_tops_2 @ (sk_B @ X0) @ X0)
% 0.38/0.56          | (v1_finset_1 @ (sk_D @ (sk_B @ X0) @ X1 @ X0))
% 0.38/0.56          | ~ (v2_compts_1 @ X1 @ X0)
% 0.38/0.56          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['127', '128'])).
% 0.38/0.56  thf('130', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.38/0.56          | ~ (v2_compts_1 @ X1 @ X0)
% 0.38/0.56          | (v1_finset_1 @ (sk_D @ (sk_B @ X0) @ X1 @ X0))
% 0.38/0.56          | ~ (v1_tops_2 @ (sk_B @ X0) @ X0)
% 0.38/0.56          | ~ (m1_setfam_1 @ (sk_B @ X0) @ X1)
% 0.38/0.56          | (v1_compts_1 @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0))),
% 0.38/0.56      inference('simplify', [status(thm)], ['129'])).
% 0.38/0.56  thf('131', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (l1_struct_0 @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | (v1_compts_1 @ X0)
% 0.38/0.56          | ~ (m1_setfam_1 @ (sk_B @ X0) @ (k2_struct_0 @ X0))
% 0.38/0.56          | ~ (v1_tops_2 @ (sk_B @ X0) @ X0)
% 0.38/0.56          | (v1_finset_1 @ (sk_D @ (sk_B @ X0) @ (k2_struct_0 @ X0) @ X0))
% 0.38/0.56          | ~ (v2_compts_1 @ (k2_struct_0 @ X0) @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['126', '130'])).
% 0.38/0.56  thf('132', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((v1_compts_1 @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | ~ (l1_struct_0 @ X0)
% 0.38/0.56          | ~ (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.56          | (v1_finset_1 @ (sk_D @ (sk_B @ X0) @ (k2_struct_0 @ X0) @ X0))
% 0.38/0.56          | ~ (v1_tops_2 @ (sk_B @ X0) @ X0)
% 0.38/0.56          | (v1_compts_1 @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | ~ (l1_struct_0 @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['125', '131'])).
% 0.38/0.56  thf('133', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (v1_tops_2 @ (sk_B @ X0) @ X0)
% 0.38/0.56          | (v1_finset_1 @ (sk_D @ (sk_B @ X0) @ (k2_struct_0 @ X0) @ X0))
% 0.38/0.56          | ~ (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.56          | ~ (l1_struct_0 @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | (v1_compts_1 @ X0))),
% 0.38/0.56      inference('simplify', [status(thm)], ['132'])).
% 0.38/0.56  thf('134', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (l1_pre_topc @ X0)
% 0.38/0.56          | (v1_compts_1 @ X0)
% 0.38/0.56          | (v1_compts_1 @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | ~ (l1_struct_0 @ X0)
% 0.38/0.56          | ~ (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.56          | (v1_finset_1 @ (sk_D @ (sk_B @ X0) @ (k2_struct_0 @ X0) @ X0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['124', '133'])).
% 0.38/0.56  thf('135', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((v1_finset_1 @ (sk_D @ (sk_B @ X0) @ (k2_struct_0 @ X0) @ X0))
% 0.38/0.56          | ~ (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.56          | ~ (l1_struct_0 @ X0)
% 0.38/0.56          | (v1_compts_1 @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0))),
% 0.38/0.56      inference('simplify', [status(thm)], ['134'])).
% 0.38/0.56  thf('136', plain,
% 0.38/0.56      (((~ (l1_pre_topc @ sk_A)
% 0.38/0.56         | (v1_compts_1 @ sk_A)
% 0.38/0.56         | ~ (l1_struct_0 @ sk_A)
% 0.38/0.56         | (v1_finset_1 @ (sk_D @ (sk_B @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_A))))
% 0.38/0.56         <= (((v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['123', '135'])).
% 0.38/0.56  thf('137', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('138', plain, ((l1_struct_0 @ sk_A)),
% 0.38/0.56      inference('sup-', [status(thm)], ['95', '96'])).
% 0.38/0.56  thf('139', plain,
% 0.38/0.56      ((((v1_compts_1 @ sk_A)
% 0.38/0.56         | (v1_finset_1 @ (sk_D @ (sk_B @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_A))))
% 0.38/0.56         <= (((v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A)))),
% 0.38/0.56      inference('demod', [status(thm)], ['136', '137', '138'])).
% 0.38/0.56  thf('140', plain,
% 0.38/0.56      ((((v1_compts_1 @ sk_A)
% 0.38/0.56         | ~ (m1_setfam_1 @ 
% 0.38/0.56              (sk_D @ (sk_B @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_A) @ 
% 0.38/0.56              (u1_struct_0 @ sk_A))))
% 0.38/0.56         <= (((v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A)))),
% 0.38/0.56      inference('clc', [status(thm)], ['122', '139'])).
% 0.38/0.56  thf('141', plain,
% 0.38/0.56      (((~ (m1_setfam_1 @ 
% 0.38/0.56            (sk_D @ (sk_B @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_A) @ 
% 0.38/0.56            (k2_struct_0 @ sk_A))
% 0.38/0.56         | ~ (l1_struct_0 @ sk_A)
% 0.38/0.56         | (v1_compts_1 @ sk_A)))
% 0.38/0.56         <= (((v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['76', '140'])).
% 0.38/0.56  thf('142', plain, ((l1_struct_0 @ sk_A)),
% 0.38/0.56      inference('sup-', [status(thm)], ['95', '96'])).
% 0.38/0.56  thf('143', plain,
% 0.38/0.56      (((~ (m1_setfam_1 @ 
% 0.38/0.56            (sk_D @ (sk_B @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_A) @ 
% 0.38/0.56            (k2_struct_0 @ sk_A))
% 0.38/0.56         | (v1_compts_1 @ sk_A)))
% 0.38/0.56         <= (((v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A)))),
% 0.38/0.56      inference('demod', [status(thm)], ['141', '142'])).
% 0.38/0.56  thf('144', plain,
% 0.38/0.56      (((v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A))
% 0.38/0.56         <= (((v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A)))),
% 0.38/0.56      inference('split', [status(esa)], ['77'])).
% 0.38/0.56  thf('145', plain,
% 0.38/0.56      (![X3 : $i]:
% 0.38/0.56         ((v1_tops_2 @ (sk_B @ X3) @ X3)
% 0.38/0.56          | (v1_compts_1 @ X3)
% 0.38/0.56          | ~ (l1_pre_topc @ X3))),
% 0.38/0.56      inference('cnf', [status(esa)], [d3_compts_1])).
% 0.38/0.56  thf('146', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((m1_setfam_1 @ (sk_B @ X0) @ (k2_struct_0 @ X0))
% 0.38/0.56          | ~ (l1_struct_0 @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | (v1_compts_1 @ X0))),
% 0.38/0.56      inference('sup+', [status(thm)], ['80', '81'])).
% 0.38/0.56  thf('147', plain,
% 0.38/0.56      (![X1 : $i]:
% 0.38/0.56         ((m1_subset_1 @ (k2_struct_0 @ X1) @ 
% 0.38/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.38/0.56          | ~ (l1_struct_0 @ X1))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.38/0.56  thf('148', plain,
% 0.38/0.56      (![X3 : $i]:
% 0.38/0.56         ((m1_subset_1 @ (sk_B @ X3) @ 
% 0.38/0.56           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3))))
% 0.38/0.56          | (v1_compts_1 @ X3)
% 0.38/0.56          | ~ (l1_pre_topc @ X3))),
% 0.38/0.56      inference('cnf', [status(esa)], [d3_compts_1])).
% 0.38/0.56  thf('149', plain,
% 0.38/0.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.38/0.56          | ~ (v2_compts_1 @ X6 @ X7)
% 0.38/0.56          | (m1_setfam_1 @ (sk_D @ X8 @ X6 @ X7) @ X6)
% 0.38/0.56          | ~ (v1_tops_2 @ X8 @ X7)
% 0.38/0.56          | ~ (m1_setfam_1 @ X8 @ X6)
% 0.38/0.56          | ~ (m1_subset_1 @ X8 @ 
% 0.38/0.56               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.38/0.56          | ~ (l1_pre_topc @ X7))),
% 0.38/0.56      inference('cnf', [status(esa)], [d7_compts_1])).
% 0.38/0.56  thf('150', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (~ (l1_pre_topc @ X0)
% 0.38/0.56          | (v1_compts_1 @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | ~ (m1_setfam_1 @ (sk_B @ X0) @ X1)
% 0.38/0.56          | ~ (v1_tops_2 @ (sk_B @ X0) @ X0)
% 0.38/0.56          | (m1_setfam_1 @ (sk_D @ (sk_B @ X0) @ X1 @ X0) @ X1)
% 0.38/0.56          | ~ (v2_compts_1 @ X1 @ X0)
% 0.38/0.56          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['148', '149'])).
% 0.38/0.56  thf('151', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.38/0.56          | ~ (v2_compts_1 @ X1 @ X0)
% 0.38/0.56          | (m1_setfam_1 @ (sk_D @ (sk_B @ X0) @ X1 @ X0) @ X1)
% 0.38/0.56          | ~ (v1_tops_2 @ (sk_B @ X0) @ X0)
% 0.38/0.56          | ~ (m1_setfam_1 @ (sk_B @ X0) @ X1)
% 0.38/0.56          | (v1_compts_1 @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0))),
% 0.38/0.56      inference('simplify', [status(thm)], ['150'])).
% 0.38/0.56  thf('152', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (l1_struct_0 @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | (v1_compts_1 @ X0)
% 0.38/0.56          | ~ (m1_setfam_1 @ (sk_B @ X0) @ (k2_struct_0 @ X0))
% 0.38/0.56          | ~ (v1_tops_2 @ (sk_B @ X0) @ X0)
% 0.38/0.56          | (m1_setfam_1 @ (sk_D @ (sk_B @ X0) @ (k2_struct_0 @ X0) @ X0) @ 
% 0.38/0.56             (k2_struct_0 @ X0))
% 0.38/0.56          | ~ (v2_compts_1 @ (k2_struct_0 @ X0) @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['147', '151'])).
% 0.38/0.56  thf('153', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((v1_compts_1 @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | ~ (l1_struct_0 @ X0)
% 0.38/0.56          | ~ (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.56          | (m1_setfam_1 @ (sk_D @ (sk_B @ X0) @ (k2_struct_0 @ X0) @ X0) @ 
% 0.38/0.56             (k2_struct_0 @ X0))
% 0.38/0.56          | ~ (v1_tops_2 @ (sk_B @ X0) @ X0)
% 0.38/0.56          | (v1_compts_1 @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | ~ (l1_struct_0 @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['146', '152'])).
% 0.38/0.56  thf('154', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (v1_tops_2 @ (sk_B @ X0) @ X0)
% 0.38/0.56          | (m1_setfam_1 @ (sk_D @ (sk_B @ X0) @ (k2_struct_0 @ X0) @ X0) @ 
% 0.38/0.56             (k2_struct_0 @ X0))
% 0.38/0.56          | ~ (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.56          | ~ (l1_struct_0 @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | (v1_compts_1 @ X0))),
% 0.38/0.56      inference('simplify', [status(thm)], ['153'])).
% 0.38/0.56  thf('155', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (l1_pre_topc @ X0)
% 0.38/0.56          | (v1_compts_1 @ X0)
% 0.38/0.56          | (v1_compts_1 @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | ~ (l1_struct_0 @ X0)
% 0.38/0.56          | ~ (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.56          | (m1_setfam_1 @ (sk_D @ (sk_B @ X0) @ (k2_struct_0 @ X0) @ X0) @ 
% 0.38/0.56             (k2_struct_0 @ X0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['145', '154'])).
% 0.38/0.56  thf('156', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((m1_setfam_1 @ (sk_D @ (sk_B @ X0) @ (k2_struct_0 @ X0) @ X0) @ 
% 0.38/0.56           (k2_struct_0 @ X0))
% 0.38/0.56          | ~ (v2_compts_1 @ (k2_struct_0 @ X0) @ X0)
% 0.38/0.56          | ~ (l1_struct_0 @ X0)
% 0.38/0.56          | (v1_compts_1 @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0))),
% 0.38/0.56      inference('simplify', [status(thm)], ['155'])).
% 0.38/0.56  thf('157', plain,
% 0.38/0.56      (((~ (l1_pre_topc @ sk_A)
% 0.38/0.56         | (v1_compts_1 @ sk_A)
% 0.38/0.56         | ~ (l1_struct_0 @ sk_A)
% 0.38/0.56         | (m1_setfam_1 @ 
% 0.38/0.56            (sk_D @ (sk_B @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_A) @ 
% 0.38/0.56            (k2_struct_0 @ sk_A))))
% 0.38/0.56         <= (((v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['144', '156'])).
% 0.38/0.56  thf('158', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('159', plain, ((l1_struct_0 @ sk_A)),
% 0.38/0.56      inference('sup-', [status(thm)], ['95', '96'])).
% 0.38/0.56  thf('160', plain,
% 0.38/0.56      ((((v1_compts_1 @ sk_A)
% 0.38/0.56         | (m1_setfam_1 @ 
% 0.38/0.56            (sk_D @ (sk_B @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_A) @ 
% 0.38/0.56            (k2_struct_0 @ sk_A))))
% 0.38/0.56         <= (((v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A)))),
% 0.38/0.56      inference('demod', [status(thm)], ['157', '158', '159'])).
% 0.38/0.56  thf('161', plain,
% 0.38/0.56      (((v1_compts_1 @ sk_A))
% 0.38/0.56         <= (((v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A)))),
% 0.38/0.56      inference('clc', [status(thm)], ['143', '160'])).
% 0.38/0.56  thf('162', plain, ((~ (v1_compts_1 @ sk_A)) <= (~ ((v1_compts_1 @ sk_A)))),
% 0.38/0.56      inference('split', [status(esa)], ['73'])).
% 0.38/0.56  thf('163', plain,
% 0.38/0.56      (((v1_compts_1 @ sk_A)) | ~ ((v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['161', '162'])).
% 0.38/0.56  thf('164', plain, (~ ((v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A))),
% 0.38/0.56      inference('sat_resolution*', [status(thm)], ['75', '163'])).
% 0.38/0.56  thf('165', plain, (~ (v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A)),
% 0.38/0.56      inference('simpl_trail', [status(thm)], ['74', '164'])).
% 0.38/0.56  thf('166', plain,
% 0.38/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.56        | ~ (l1_struct_0 @ sk_A)
% 0.38/0.56        | ~ (v1_compts_1 @ sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['72', '165'])).
% 0.38/0.56  thf('167', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('168', plain, ((l1_struct_0 @ sk_A)),
% 0.38/0.56      inference('sup-', [status(thm)], ['95', '96'])).
% 0.38/0.56  thf('169', plain, (((v1_compts_1 @ sk_A)) <= (((v1_compts_1 @ sk_A)))),
% 0.38/0.56      inference('split', [status(esa)], ['77'])).
% 0.38/0.56  thf('170', plain,
% 0.38/0.56      (((v1_compts_1 @ sk_A)) | ((v2_compts_1 @ (k2_struct_0 @ sk_A) @ sk_A))),
% 0.38/0.56      inference('split', [status(esa)], ['77'])).
% 0.38/0.56  thf('171', plain, (((v1_compts_1 @ sk_A))),
% 0.38/0.56      inference('sat_resolution*', [status(thm)], ['75', '163', '170'])).
% 0.38/0.56  thf('172', plain, ((v1_compts_1 @ sk_A)),
% 0.38/0.56      inference('simpl_trail', [status(thm)], ['169', '171'])).
% 0.38/0.56  thf('173', plain, ($false),
% 0.38/0.56      inference('demod', [status(thm)], ['166', '167', '168', '172'])).
% 0.38/0.56  
% 0.38/0.56  % SZS output end Refutation
% 0.38/0.56  
% 0.38/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
