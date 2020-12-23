%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1355+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YwP7InRgJD

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:33 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :  198 ( 512 expanded)
%              Number of leaves         :   23 ( 152 expanded)
%              Depth                    :   24
%              Number of atoms          : 3295 (7696 expanded)
%              Number of equality atoms :    8 (  30 expanded)
%              Maximal formula depth    :   21 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_setfam_1_type,type,(
    m1_setfam_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( v1_tops_2 @ ( sk_C_1 @ X4 @ X5 ) @ X5 )
      | ( v2_compts_1 @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_compts_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ( v1_tops_2 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( m1_setfam_1 @ ( sk_C_1 @ X4 @ X5 ) @ X4 )
      | ( v2_compts_1 @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
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
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('7',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( m1_subset_1 @ ( sk_C_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ( v2_compts_1 @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
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
    ! [X0: $i,X2: $i] :
      ( ~ ( v1_compts_1 @ X0 )
      | ( v1_finset_1 @ ( sk_C @ X2 @ X0 ) )
      | ~ ( v1_tops_2 @ X2 @ X0 )
      | ~ ( m1_setfam_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
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
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('20',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
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
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('25',plain,(
    ! [X0: $i,X2: $i] :
      ( ~ ( v1_compts_1 @ X0 )
      | ( m1_setfam_1 @ ( sk_C @ X2 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_tops_2 @ X2 @ X0 )
      | ~ ( m1_setfam_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
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
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('40',plain,(
    ! [X0: $i,X2: $i] :
      ( ~ ( v1_compts_1 @ X0 )
      | ( r1_tarski @ ( sk_C @ X2 @ X0 ) @ X2 )
      | ~ ( v1_tops_2 @ X2 @ X0 )
      | ~ ( m1_setfam_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
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
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X0 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ ( k2_struct_0 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('53',plain,(
    ! [X0: $i,X2: $i] :
      ( ~ ( v1_compts_1 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X2 @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_tops_2 @ X2 @ X0 )
      | ~ ( m1_setfam_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
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
    ! [X4: $i,X5: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( r1_tarski @ X7 @ ( sk_C_1 @ X4 @ X5 ) )
      | ~ ( m1_setfam_1 @ X7 @ X4 )
      | ~ ( v1_finset_1 @ X7 )
      | ( v2_compts_1 @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
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
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
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
    ! [X0: $i] :
      ( ( v1_tops_2 @ ( sk_B @ X0 ) @ X0 )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_compts_1])).

thf('80',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( m1_setfam_1 @ ( sk_B @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_compts_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( m1_setfam_1 @ ( sk_B @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_compts_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_compts_1])).

thf('85',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( v2_compts_1 @ X4 @ X5 )
      | ( r1_tarski @ ( sk_D @ X6 @ X4 @ X5 ) @ X6 )
      | ~ ( v1_tops_2 @ X6 @ X5 )
      | ~ ( m1_setfam_1 @ X6 @ X4 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
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
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
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
    ! [X0: $i] :
      ( ( v1_tops_2 @ ( sk_B @ X0 ) @ X0 )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_compts_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( m1_setfam_1 @ ( sk_B @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_compts_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('102',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_compts_1])).

thf('104',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( v2_compts_1 @ X4 @ X5 )
      | ( m1_subset_1 @ ( sk_D @ X6 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_tops_2 @ X6 @ X5 )
      | ~ ( m1_setfam_1 @ X6 @ X4 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( r1_tarski @ X1 @ ( sk_B @ X0 ) )
      | ~ ( m1_setfam_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_finset_1 @ X1 )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
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
    ! [X0: $i] :
      ( ( v1_tops_2 @ ( sk_B @ X0 ) @ X0 )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_compts_1])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( m1_setfam_1 @ ( sk_B @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_compts_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('126',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_compts_1])).

thf('128',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( v2_compts_1 @ X4 @ X5 )
      | ( v1_finset_1 @ ( sk_D @ X6 @ X4 @ X5 ) )
      | ~ ( v1_tops_2 @ X6 @ X5 )
      | ~ ( m1_setfam_1 @ X6 @ X4 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
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
    ! [X0: $i] :
      ( ( v1_tops_2 @ ( sk_B @ X0 ) @ X0 )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_compts_1])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( m1_setfam_1 @ ( sk_B @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_compts_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('147',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_compts_1])).

thf('149',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( v2_compts_1 @ X4 @ X5 )
      | ( m1_setfam_1 @ ( sk_D @ X6 @ X4 @ X5 ) @ X4 )
      | ~ ( v1_tops_2 @ X6 @ X5 )
      | ~ ( m1_setfam_1 @ X6 @ X4 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
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
