%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1297+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZrJCjYz0fa

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:25 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   41 (  66 expanded)
%              Number of leaves         :   12 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :  286 ( 629 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(t13_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) )
          <=> ( v1_finset_1 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) )
            <=> ( v1_finset_1 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t13_tops_2])).

thf('0',plain,
    ( ~ ( v1_finset_1 @ sk_B )
    | ~ ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_finset_1 @ sk_B )
    | ~ ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v1_finset_1 @ sk_B )
    | ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
   <= ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) )
           => ( v1_finset_1 @ B ) ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ( v1_finset_1 @ X4 )
      | ~ ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ X5 ) @ X4 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l13_tops_2])).

thf('6',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_finset_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_finset_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( v1_finset_1 @ sk_B )
   <= ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,
    ( ~ ( v1_finset_1 @ sk_B )
   <= ~ ( v1_finset_1 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('11',plain,
    ( ( v1_finset_1 @ sk_B )
    | ~ ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( v1_finset_1 @ sk_B )
    | ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('13',plain,
    ( ( v1_finset_1 @ sk_B )
   <= ( v1_finset_1 @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('16',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ( v1_finset_1 @ X4 )
      | ~ ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ X5 ) @ X4 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l13_tops_2])).

thf('18',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
        = B ) ) )).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k7_setfam_1 @ X3 @ ( k7_setfam_1 @ X3 @ X2 ) )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('22',plain,
    ( ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( v1_finset_1 @ sk_B )
    | ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','19','22'])).

thf('24',plain,
    ( ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
   <= ( v1_finset_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','23'])).

thf('25',plain,
    ( ~ ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
   <= ~ ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,
    ( ~ ( v1_finset_1 @ sk_B )
    | ( v1_finset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','11','12','26'])).


%------------------------------------------------------------------------------
