%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Vb54py659P

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:44 EST 2020

% Result     : Theorem 12.22s
% Output     : Refutation 12.22s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 279 expanded)
%              Number of leaves         :   33 ( 100 expanded)
%              Depth                    :   22
%              Number of atoms          : 2283 (3968 expanded)
%              Number of equality atoms :   81 ( 185 expanded)
%              Maximal formula depth    :   23 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(a_2_1_orders_2_type,type,(
    a_2_1_orders_2: $i > $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k2_orders_2_type,type,(
    k2_orders_2: $i > $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(t46_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t46_orders_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) )).

thf('1',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('4',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('5',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(d13_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_orders_2 @ A @ B )
            = ( a_2_1_orders_2 @ A @ B ) ) ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( ( k2_orders_2 @ X17 @ X16 )
        = ( a_2_1_orders_2 @ X17 @ X16 ) )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v3_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d13_orders_2])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ X1 )
        = ( a_2_1_orders_2 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( a_2_1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('10',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fraenkel_a_2_1_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( v3_orders_2 @ B )
        & ( v4_orders_2 @ B )
        & ( v5_orders_2 @ B )
        & ( l1_orders_2 @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
     => ( ( r2_hidden @ A @ ( a_2_1_orders_2 @ B @ C ) )
      <=> ? [D: $i] :
            ( ! [E: $i] :
                ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
               => ( ( r2_hidden @ E @ C )
                 => ( r2_orders_2 @ B @ D @ E ) ) )
            & ( A = D )
            & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X19: $i,X20: $i,X22: $i] :
      ( ~ ( l1_orders_2 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v3_orders_2 @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( X22
        = ( sk_D @ X20 @ X19 @ X22 ) )
      | ~ ( r2_hidden @ X22 @ ( a_2_1_orders_2 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( a_2_1_orders_2 @ X0 @ X1 ) )
      | ( X2
        = ( sk_D @ X1 @ X0 @ X2 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( X1
        = ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( a_2_1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( X1
        = ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','15'])).

thf('17',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('18',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( a_2_1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('20',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('21',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('22',plain,(
    ! [X19: $i,X20: $i,X22: $i] :
      ( ~ ( l1_orders_2 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v3_orders_2 @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( m1_subset_1 @ ( sk_D @ X20 @ X19 @ X22 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( r2_hidden @ X22 @ ( a_2_1_orders_2 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( a_2_1_orders_2 @ X0 @ X1 ) )
      | ( m1_subset_1 @ ( sk_D @ X1 @ X0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( a_2_1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['17','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['16','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','15'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','26'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('39',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( a_2_1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('41',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('42',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('43',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( l1_orders_2 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v3_orders_2 @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X19 ) )
      | ( r2_orders_2 @ X19 @ ( sk_D @ X20 @ X19 @ X22 ) @ X21 )
      | ~ ( r2_hidden @ X21 @ X20 )
      | ~ ( r2_hidden @ X22 @ ( a_2_1_orders_2 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( a_2_1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ X2 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ X1 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( r2_hidden @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( k2_struct_0 @ X0 ) )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['33','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('56',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('57',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('58',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( ( k2_orders_2 @ X17 @ X16 )
        = ( a_2_1_orders_2 @ X17 @ X16 ) )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v3_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d13_orders_2])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('61',plain,(
    ! [X19: $i,X20: $i,X22: $i] :
      ( ~ ( l1_orders_2 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v3_orders_2 @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( X22
        = ( sk_D @ X20 @ X19 @ X22 ) )
      | ~ ( r2_hidden @ X22 @ ( a_2_1_orders_2 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( X1
        = ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( X1
        = ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( X1
        = ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['56','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','65'])).

thf('67',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('68',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('70',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('71',plain,(
    ! [X19: $i,X20: $i,X22: $i] :
      ( ~ ( l1_orders_2 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v3_orders_2 @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( m1_subset_1 @ ( sk_D @ X20 @ X19 @ X22 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( r2_hidden @ X22 @ ( a_2_1_orders_2 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['68','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','75'])).

thf(d10_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_orders_2 @ A @ B @ C )
              <=> ( ( r1_orders_2 @ A @ B @ C )
                  & ( B != C ) ) ) ) ) ) )).

thf('77',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( r2_orders_2 @ X14 @ X13 @ X15 )
      | ( X13 != X15 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('78',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X14 )
      | ~ ( r2_orders_2 @ X14 @ X15 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['66','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('88',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('89',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['86','89','90','91','92','93'])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('99',plain,(
    ! [X12: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['97','101'])).

thf('103',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['87','88'])).

thf('104',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    $false ),
    inference(demod,[status(thm)],['0','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Vb54py659P
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:01:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 12.22/12.41  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 12.22/12.41  % Solved by: fo/fo7.sh
% 12.22/12.41  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 12.22/12.41  % done 7734 iterations in 11.940s
% 12.22/12.41  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 12.22/12.41  % SZS output start Refutation
% 12.22/12.41  thf(sk_A_type, type, sk_A: $i).
% 12.22/12.41  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 12.22/12.41  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 12.22/12.41  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 12.22/12.41  thf(sk_B_type, type, sk_B: $i > $i).
% 12.22/12.41  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 12.22/12.41  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 12.22/12.41  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 12.22/12.41  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 12.22/12.41  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 12.22/12.41  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 12.22/12.41  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 12.22/12.41  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 12.22/12.41  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 12.22/12.41  thf(a_2_1_orders_2_type, type, a_2_1_orders_2: $i > $i > $i).
% 12.22/12.41  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 12.22/12.41  thf(k2_orders_2_type, type, k2_orders_2: $i > $i > $i).
% 12.22/12.41  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 12.22/12.41  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 12.22/12.41  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 12.22/12.41  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 12.22/12.41  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 12.22/12.41  thf(t46_orders_2, conjecture,
% 12.22/12.41    (![A:$i]:
% 12.22/12.41     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 12.22/12.41         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 12.22/12.41       ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ))).
% 12.22/12.41  thf(zf_stmt_0, negated_conjecture,
% 12.22/12.41    (~( ![A:$i]:
% 12.22/12.41        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 12.22/12.41            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 12.22/12.41          ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ) )),
% 12.22/12.41    inference('cnf.neg', [status(esa)], [t46_orders_2])).
% 12.22/12.41  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 12.22/12.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.22/12.41  thf(t29_mcart_1, axiom,
% 12.22/12.41    (![A:$i]:
% 12.22/12.41     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 12.22/12.41          ( ![B:$i]:
% 12.22/12.41            ( ~( ( r2_hidden @ B @ A ) & 
% 12.22/12.41                 ( ![C:$i,D:$i,E:$i]:
% 12.22/12.41                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 12.22/12.41                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 12.22/12.41  thf('1', plain,
% 12.22/12.41      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 12.22/12.41      inference('cnf', [status(esa)], [t29_mcart_1])).
% 12.22/12.41  thf(dt_k2_subset_1, axiom,
% 12.22/12.41    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 12.22/12.41  thf('2', plain,
% 12.22/12.41      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 12.22/12.41      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 12.22/12.41  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 12.22/12.41  thf('3', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 12.22/12.41      inference('cnf', [status(esa)], [d4_subset_1])).
% 12.22/12.41  thf('4', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 12.22/12.41      inference('demod', [status(thm)], ['2', '3'])).
% 12.22/12.41  thf(d3_struct_0, axiom,
% 12.22/12.41    (![A:$i]:
% 12.22/12.41     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 12.22/12.41  thf('5', plain,
% 12.22/12.41      (![X11 : $i]:
% 12.22/12.41         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 12.22/12.41      inference('cnf', [status(esa)], [d3_struct_0])).
% 12.22/12.41  thf(d13_orders_2, axiom,
% 12.22/12.41    (![A:$i]:
% 12.22/12.41     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 12.22/12.41         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 12.22/12.41       ( ![B:$i]:
% 12.22/12.41         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.22/12.41           ( ( k2_orders_2 @ A @ B ) = ( a_2_1_orders_2 @ A @ B ) ) ) ) ))).
% 12.22/12.41  thf('6', plain,
% 12.22/12.41      (![X16 : $i, X17 : $i]:
% 12.22/12.41         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 12.22/12.41          | ((k2_orders_2 @ X17 @ X16) = (a_2_1_orders_2 @ X17 @ X16))
% 12.22/12.41          | ~ (l1_orders_2 @ X17)
% 12.22/12.41          | ~ (v5_orders_2 @ X17)
% 12.22/12.41          | ~ (v4_orders_2 @ X17)
% 12.22/12.41          | ~ (v3_orders_2 @ X17)
% 12.22/12.41          | (v2_struct_0 @ X17))),
% 12.22/12.41      inference('cnf', [status(esa)], [d13_orders_2])).
% 12.22/12.41  thf('7', plain,
% 12.22/12.41      (![X0 : $i, X1 : $i]:
% 12.22/12.41         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ((k2_orders_2 @ X0 @ X1) = (a_2_1_orders_2 @ X0 @ X1)))),
% 12.22/12.41      inference('sup-', [status(thm)], ['5', '6'])).
% 12.22/12.41  thf('8', plain,
% 12.22/12.41      (![X0 : $i]:
% 12.22/12.41         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 12.22/12.41            = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (l1_struct_0 @ X0))),
% 12.22/12.41      inference('sup-', [status(thm)], ['4', '7'])).
% 12.22/12.41  thf('9', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 12.22/12.41      inference('demod', [status(thm)], ['2', '3'])).
% 12.22/12.41  thf('10', plain,
% 12.22/12.41      (![X11 : $i]:
% 12.22/12.41         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 12.22/12.41      inference('cnf', [status(esa)], [d3_struct_0])).
% 12.22/12.41  thf(fraenkel_a_2_1_orders_2, axiom,
% 12.22/12.41    (![A:$i,B:$i,C:$i]:
% 12.22/12.41     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 12.22/12.41         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 12.22/12.41         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 12.22/12.41       ( ( r2_hidden @ A @ ( a_2_1_orders_2 @ B @ C ) ) <=>
% 12.22/12.41         ( ?[D:$i]:
% 12.22/12.41           ( ( ![E:$i]:
% 12.22/12.41               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 12.22/12.41                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ D @ E ) ) ) ) & 
% 12.22/12.41             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 12.22/12.41  thf('11', plain,
% 12.22/12.41      (![X19 : $i, X20 : $i, X22 : $i]:
% 12.22/12.41         (~ (l1_orders_2 @ X19)
% 12.22/12.41          | ~ (v5_orders_2 @ X19)
% 12.22/12.41          | ~ (v4_orders_2 @ X19)
% 12.22/12.41          | ~ (v3_orders_2 @ X19)
% 12.22/12.41          | (v2_struct_0 @ X19)
% 12.22/12.41          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 12.22/12.41          | ((X22) = (sk_D @ X20 @ X19 @ X22))
% 12.22/12.41          | ~ (r2_hidden @ X22 @ (a_2_1_orders_2 @ X19 @ X20)))),
% 12.22/12.41      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 12.22/12.41  thf('12', plain,
% 12.22/12.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.22/12.41         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | ~ (r2_hidden @ X2 @ (a_2_1_orders_2 @ X0 @ X1))
% 12.22/12.41          | ((X2) = (sk_D @ X1 @ X0 @ X2))
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0))),
% 12.22/12.41      inference('sup-', [status(thm)], ['10', '11'])).
% 12.22/12.41  thf('13', plain,
% 12.22/12.41      (![X0 : $i, X1 : $i]:
% 12.22/12.41         (~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 12.22/12.41          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 12.22/12.41          | ~ (l1_struct_0 @ X0))),
% 12.22/12.41      inference('sup-', [status(thm)], ['9', '12'])).
% 12.22/12.41  thf('14', plain,
% 12.22/12.41      (![X0 : $i, X1 : $i]:
% 12.22/12.41         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | ((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0))),
% 12.22/12.41      inference('sup-', [status(thm)], ['8', '13'])).
% 12.22/12.41  thf('15', plain,
% 12.22/12.41      (![X0 : $i, X1 : $i]:
% 12.22/12.41         (((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 12.22/12.41      inference('simplify', [status(thm)], ['14'])).
% 12.22/12.41  thf('16', plain,
% 12.22/12.41      (![X0 : $i]:
% 12.22/12.41         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ((sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 12.22/12.41              = (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 12.22/12.41                 (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))))),
% 12.22/12.41      inference('sup-', [status(thm)], ['1', '15'])).
% 12.22/12.41  thf('17', plain,
% 12.22/12.41      (![X11 : $i]:
% 12.22/12.41         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 12.22/12.41      inference('cnf', [status(esa)], [d3_struct_0])).
% 12.22/12.41  thf('18', plain,
% 12.22/12.41      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 12.22/12.41      inference('cnf', [status(esa)], [t29_mcart_1])).
% 12.22/12.41  thf('19', plain,
% 12.22/12.41      (![X0 : $i]:
% 12.22/12.41         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 12.22/12.41            = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (l1_struct_0 @ X0))),
% 12.22/12.41      inference('sup-', [status(thm)], ['4', '7'])).
% 12.22/12.41  thf('20', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 12.22/12.41      inference('demod', [status(thm)], ['2', '3'])).
% 12.22/12.41  thf('21', plain,
% 12.22/12.41      (![X11 : $i]:
% 12.22/12.41         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 12.22/12.41      inference('cnf', [status(esa)], [d3_struct_0])).
% 12.22/12.41  thf('22', plain,
% 12.22/12.41      (![X19 : $i, X20 : $i, X22 : $i]:
% 12.22/12.41         (~ (l1_orders_2 @ X19)
% 12.22/12.41          | ~ (v5_orders_2 @ X19)
% 12.22/12.41          | ~ (v4_orders_2 @ X19)
% 12.22/12.41          | ~ (v3_orders_2 @ X19)
% 12.22/12.41          | (v2_struct_0 @ X19)
% 12.22/12.41          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 12.22/12.41          | (m1_subset_1 @ (sk_D @ X20 @ X19 @ X22) @ (u1_struct_0 @ X19))
% 12.22/12.41          | ~ (r2_hidden @ X22 @ (a_2_1_orders_2 @ X19 @ X20)))),
% 12.22/12.41      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 12.22/12.41  thf('23', plain,
% 12.22/12.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.22/12.41         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | ~ (r2_hidden @ X2 @ (a_2_1_orders_2 @ X0 @ X1))
% 12.22/12.41          | (m1_subset_1 @ (sk_D @ X1 @ X0 @ X2) @ (u1_struct_0 @ X0))
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0))),
% 12.22/12.41      inference('sup-', [status(thm)], ['21', '22'])).
% 12.22/12.41  thf('24', plain,
% 12.22/12.41      (![X0 : $i, X1 : $i]:
% 12.22/12.41         (~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 12.22/12.41             (u1_struct_0 @ X0))
% 12.22/12.41          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 12.22/12.41          | ~ (l1_struct_0 @ X0))),
% 12.22/12.41      inference('sup-', [status(thm)], ['20', '23'])).
% 12.22/12.41  thf('25', plain,
% 12.22/12.41      (![X0 : $i, X1 : $i]:
% 12.22/12.41         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 12.22/12.41             (u1_struct_0 @ X0))
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0))),
% 12.22/12.41      inference('sup-', [status(thm)], ['19', '24'])).
% 12.22/12.41  thf('26', plain,
% 12.22/12.41      (![X0 : $i, X1 : $i]:
% 12.22/12.41         ((m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 12.22/12.41           (u1_struct_0 @ X0))
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 12.22/12.41      inference('simplify', [status(thm)], ['25'])).
% 12.22/12.41  thf('27', plain,
% 12.22/12.41      (![X0 : $i]:
% 12.22/12.41         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | (m1_subset_1 @ 
% 12.22/12.41             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 12.22/12.41              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 12.22/12.41             (u1_struct_0 @ X0)))),
% 12.22/12.41      inference('sup-', [status(thm)], ['18', '26'])).
% 12.22/12.41  thf('28', plain,
% 12.22/12.41      (![X0 : $i]:
% 12.22/12.41         ((m1_subset_1 @ 
% 12.22/12.41           (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 12.22/12.41            (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 12.22/12.41           (k2_struct_0 @ X0))
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 12.22/12.41      inference('sup+', [status(thm)], ['17', '27'])).
% 12.22/12.41  thf('29', plain,
% 12.22/12.41      (![X0 : $i]:
% 12.22/12.41         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | (m1_subset_1 @ 
% 12.22/12.41             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 12.22/12.41              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 12.22/12.41             (k2_struct_0 @ X0)))),
% 12.22/12.41      inference('simplify', [status(thm)], ['28'])).
% 12.22/12.41  thf('30', plain,
% 12.22/12.41      (![X0 : $i]:
% 12.22/12.41         ((m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 12.22/12.41           (k2_struct_0 @ X0))
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 12.22/12.41      inference('sup+', [status(thm)], ['16', '29'])).
% 12.22/12.41  thf('31', plain,
% 12.22/12.41      (![X0 : $i]:
% 12.22/12.41         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | (m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 12.22/12.41             (k2_struct_0 @ X0)))),
% 12.22/12.41      inference('simplify', [status(thm)], ['30'])).
% 12.22/12.41  thf(t2_subset, axiom,
% 12.22/12.41    (![A:$i,B:$i]:
% 12.22/12.41     ( ( m1_subset_1 @ A @ B ) =>
% 12.22/12.41       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 12.22/12.41  thf('32', plain,
% 12.22/12.41      (![X2 : $i, X3 : $i]:
% 12.22/12.41         ((r2_hidden @ X2 @ X3)
% 12.22/12.41          | (v1_xboole_0 @ X3)
% 12.22/12.41          | ~ (m1_subset_1 @ X2 @ X3))),
% 12.22/12.41      inference('cnf', [status(esa)], [t2_subset])).
% 12.22/12.41  thf('33', plain,
% 12.22/12.41      (![X0 : $i]:
% 12.22/12.41         (~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 12.22/12.41          | (v1_xboole_0 @ (k2_struct_0 @ X0))
% 12.22/12.41          | (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 12.22/12.41             (k2_struct_0 @ X0)))),
% 12.22/12.41      inference('sup-', [status(thm)], ['31', '32'])).
% 12.22/12.41  thf('34', plain,
% 12.22/12.41      (![X0 : $i]:
% 12.22/12.41         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ((sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 12.22/12.41              = (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 12.22/12.41                 (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))))),
% 12.22/12.41      inference('sup-', [status(thm)], ['1', '15'])).
% 12.22/12.41  thf('35', plain,
% 12.22/12.41      (![X0 : $i]:
% 12.22/12.41         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | (m1_subset_1 @ 
% 12.22/12.41             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 12.22/12.41              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 12.22/12.41             (u1_struct_0 @ X0)))),
% 12.22/12.41      inference('sup-', [status(thm)], ['18', '26'])).
% 12.22/12.41  thf('36', plain,
% 12.22/12.41      (![X0 : $i]:
% 12.22/12.41         ((m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 12.22/12.41           (u1_struct_0 @ X0))
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 12.22/12.41      inference('sup+', [status(thm)], ['34', '35'])).
% 12.22/12.41  thf('37', plain,
% 12.22/12.41      (![X0 : $i]:
% 12.22/12.41         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | (m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 12.22/12.41             (u1_struct_0 @ X0)))),
% 12.22/12.41      inference('simplify', [status(thm)], ['36'])).
% 12.22/12.41  thf('38', plain,
% 12.22/12.41      (![X11 : $i]:
% 12.22/12.41         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 12.22/12.41      inference('cnf', [status(esa)], [d3_struct_0])).
% 12.22/12.41  thf('39', plain,
% 12.22/12.41      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 12.22/12.41      inference('cnf', [status(esa)], [t29_mcart_1])).
% 12.22/12.41  thf('40', plain,
% 12.22/12.41      (![X0 : $i]:
% 12.22/12.41         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 12.22/12.41            = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (l1_struct_0 @ X0))),
% 12.22/12.41      inference('sup-', [status(thm)], ['4', '7'])).
% 12.22/12.41  thf('41', plain,
% 12.22/12.41      (![X11 : $i]:
% 12.22/12.41         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 12.22/12.41      inference('cnf', [status(esa)], [d3_struct_0])).
% 12.22/12.41  thf('42', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 12.22/12.41      inference('demod', [status(thm)], ['2', '3'])).
% 12.22/12.41  thf('43', plain,
% 12.22/12.41      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 12.22/12.41         (~ (l1_orders_2 @ X19)
% 12.22/12.41          | ~ (v5_orders_2 @ X19)
% 12.22/12.41          | ~ (v4_orders_2 @ X19)
% 12.22/12.41          | ~ (v3_orders_2 @ X19)
% 12.22/12.41          | (v2_struct_0 @ X19)
% 12.22/12.41          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 12.22/12.41          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X19))
% 12.22/12.41          | (r2_orders_2 @ X19 @ (sk_D @ X20 @ X19 @ X22) @ X21)
% 12.22/12.41          | ~ (r2_hidden @ X21 @ X20)
% 12.22/12.41          | ~ (r2_hidden @ X22 @ (a_2_1_orders_2 @ X19 @ X20)))),
% 12.22/12.41      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 12.22/12.41  thf('44', plain,
% 12.22/12.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.22/12.41         (~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 12.22/12.41          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X0))
% 12.22/12.41          | (r2_orders_2 @ X0 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ X2)
% 12.22/12.41          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0))),
% 12.22/12.41      inference('sup-', [status(thm)], ['42', '43'])).
% 12.22/12.41  thf('45', plain,
% 12.22/12.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.22/12.41         (~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 12.22/12.41          | (r2_orders_2 @ X0 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ X2)
% 12.22/12.41          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X0)))),
% 12.22/12.41      inference('sup-', [status(thm)], ['41', '44'])).
% 12.22/12.41  thf('46', plain,
% 12.22/12.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.22/12.41         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X0))
% 12.22/12.41          | (r2_orders_2 @ X0 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ X2)
% 12.22/12.41          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_struct_0 @ X0))),
% 12.22/12.41      inference('sup-', [status(thm)], ['40', '45'])).
% 12.22/12.41  thf('47', plain,
% 12.22/12.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.22/12.41         (~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 12.22/12.41          | (r2_orders_2 @ X0 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ X2)
% 12.22/12.41          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X0))
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 12.22/12.41      inference('simplify', [status(thm)], ['46'])).
% 12.22/12.41  thf('48', plain,
% 12.22/12.41      (![X0 : $i, X1 : $i]:
% 12.22/12.41         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 12.22/12.41          | (r2_orders_2 @ X0 @ 
% 12.22/12.41             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 12.22/12.41              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 12.22/12.41             X1)
% 12.22/12.41          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0)))),
% 12.22/12.41      inference('sup-', [status(thm)], ['39', '47'])).
% 12.22/12.41  thf('49', plain,
% 12.22/12.41      (![X0 : $i, X1 : $i]:
% 12.22/12.41         (~ (r2_hidden @ X1 @ (k2_struct_0 @ X0))
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 12.22/12.41          | (r2_orders_2 @ X0 @ 
% 12.22/12.41             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 12.22/12.41              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 12.22/12.41             X1)
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 12.22/12.41      inference('sup-', [status(thm)], ['38', '48'])).
% 12.22/12.41  thf('50', plain,
% 12.22/12.41      (![X0 : $i, X1 : $i]:
% 12.22/12.41         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | (r2_orders_2 @ X0 @ 
% 12.22/12.41             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 12.22/12.41              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 12.22/12.41             X1)
% 12.22/12.41          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | ~ (r2_hidden @ X1 @ (k2_struct_0 @ X0)))),
% 12.22/12.41      inference('simplify', [status(thm)], ['49'])).
% 12.22/12.41  thf('51', plain,
% 12.22/12.41      (![X0 : $i]:
% 12.22/12.41         (~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 12.22/12.41          | ~ (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 12.22/12.41               (k2_struct_0 @ X0))
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | (r2_orders_2 @ X0 @ 
% 12.22/12.41             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 12.22/12.41              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 12.22/12.41             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 12.22/12.41      inference('sup-', [status(thm)], ['37', '50'])).
% 12.22/12.41  thf('52', plain,
% 12.22/12.41      (![X0 : $i]:
% 12.22/12.41         ((r2_orders_2 @ X0 @ 
% 12.22/12.41           (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 12.22/12.41            (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 12.22/12.41           (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 12.22/12.41          | ~ (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 12.22/12.41               (k2_struct_0 @ X0))
% 12.22/12.41          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0))),
% 12.22/12.41      inference('simplify', [status(thm)], ['51'])).
% 12.22/12.41  thf('53', plain,
% 12.22/12.41      (![X0 : $i]:
% 12.22/12.41         ((v1_xboole_0 @ (k2_struct_0 @ X0))
% 12.22/12.41          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 12.22/12.41          | (r2_orders_2 @ X0 @ 
% 12.22/12.41             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 12.22/12.41              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 12.22/12.41             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))),
% 12.22/12.41      inference('sup-', [status(thm)], ['33', '52'])).
% 12.22/12.41  thf('54', plain,
% 12.22/12.41      (![X0 : $i]:
% 12.22/12.41         ((r2_orders_2 @ X0 @ 
% 12.22/12.41           (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 12.22/12.41            (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 12.22/12.41           (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 12.22/12.41          | (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 12.22/12.41      inference('simplify', [status(thm)], ['53'])).
% 12.22/12.41  thf('55', plain,
% 12.22/12.41      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 12.22/12.41      inference('cnf', [status(esa)], [t29_mcart_1])).
% 12.22/12.41  thf('56', plain,
% 12.22/12.41      (![X11 : $i]:
% 12.22/12.41         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 12.22/12.41      inference('cnf', [status(esa)], [d3_struct_0])).
% 12.22/12.41  thf('57', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 12.22/12.41      inference('demod', [status(thm)], ['2', '3'])).
% 12.22/12.41  thf('58', plain,
% 12.22/12.41      (![X16 : $i, X17 : $i]:
% 12.22/12.41         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 12.22/12.41          | ((k2_orders_2 @ X17 @ X16) = (a_2_1_orders_2 @ X17 @ X16))
% 12.22/12.41          | ~ (l1_orders_2 @ X17)
% 12.22/12.41          | ~ (v5_orders_2 @ X17)
% 12.22/12.41          | ~ (v4_orders_2 @ X17)
% 12.22/12.41          | ~ (v3_orders_2 @ X17)
% 12.22/12.41          | (v2_struct_0 @ X17))),
% 12.22/12.41      inference('cnf', [status(esa)], [d13_orders_2])).
% 12.22/12.41  thf('59', plain,
% 12.22/12.41      (![X0 : $i]:
% 12.22/12.41         ((v2_struct_0 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ((k2_orders_2 @ X0 @ (u1_struct_0 @ X0))
% 12.22/12.41              = (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0))))),
% 12.22/12.41      inference('sup-', [status(thm)], ['57', '58'])).
% 12.22/12.41  thf('60', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 12.22/12.41      inference('demod', [status(thm)], ['2', '3'])).
% 12.22/12.41  thf('61', plain,
% 12.22/12.41      (![X19 : $i, X20 : $i, X22 : $i]:
% 12.22/12.41         (~ (l1_orders_2 @ X19)
% 12.22/12.41          | ~ (v5_orders_2 @ X19)
% 12.22/12.41          | ~ (v4_orders_2 @ X19)
% 12.22/12.41          | ~ (v3_orders_2 @ X19)
% 12.22/12.41          | (v2_struct_0 @ X19)
% 12.22/12.41          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 12.22/12.41          | ((X22) = (sk_D @ X20 @ X19 @ X22))
% 12.22/12.41          | ~ (r2_hidden @ X22 @ (a_2_1_orders_2 @ X19 @ X20)))),
% 12.22/12.41      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 12.22/12.41  thf('62', plain,
% 12.22/12.41      (![X0 : $i, X1 : $i]:
% 12.22/12.41         (~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 12.22/12.41          | ((X1) = (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1))
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0))),
% 12.22/12.41      inference('sup-', [status(thm)], ['60', '61'])).
% 12.22/12.41  thf('63', plain,
% 12.22/12.41      (![X0 : $i, X1 : $i]:
% 12.22/12.41         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ((X1) = (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1)))),
% 12.22/12.41      inference('sup-', [status(thm)], ['59', '62'])).
% 12.22/12.41  thf('64', plain,
% 12.22/12.41      (![X0 : $i, X1 : $i]:
% 12.22/12.41         (((X1) = (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1))
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (u1_struct_0 @ X0))))),
% 12.22/12.41      inference('simplify', [status(thm)], ['63'])).
% 12.22/12.41  thf('65', plain,
% 12.22/12.41      (![X0 : $i, X1 : $i]:
% 12.22/12.41         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ((X1) = (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1)))),
% 12.22/12.41      inference('sup-', [status(thm)], ['56', '64'])).
% 12.22/12.41  thf('66', plain,
% 12.22/12.41      (![X0 : $i]:
% 12.22/12.41         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 12.22/12.41          | ((sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 12.22/12.41              = (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 12.22/12.41                 (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_struct_0 @ X0))),
% 12.22/12.41      inference('sup-', [status(thm)], ['55', '65'])).
% 12.22/12.41  thf('67', plain,
% 12.22/12.41      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 12.22/12.41      inference('cnf', [status(esa)], [t29_mcart_1])).
% 12.22/12.41  thf('68', plain,
% 12.22/12.41      (![X11 : $i]:
% 12.22/12.41         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 12.22/12.41      inference('cnf', [status(esa)], [d3_struct_0])).
% 12.22/12.41  thf('69', plain,
% 12.22/12.41      (![X0 : $i]:
% 12.22/12.41         ((v2_struct_0 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ((k2_orders_2 @ X0 @ (u1_struct_0 @ X0))
% 12.22/12.41              = (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0))))),
% 12.22/12.41      inference('sup-', [status(thm)], ['57', '58'])).
% 12.22/12.41  thf('70', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 12.22/12.41      inference('demod', [status(thm)], ['2', '3'])).
% 12.22/12.41  thf('71', plain,
% 12.22/12.41      (![X19 : $i, X20 : $i, X22 : $i]:
% 12.22/12.41         (~ (l1_orders_2 @ X19)
% 12.22/12.41          | ~ (v5_orders_2 @ X19)
% 12.22/12.41          | ~ (v4_orders_2 @ X19)
% 12.22/12.41          | ~ (v3_orders_2 @ X19)
% 12.22/12.41          | (v2_struct_0 @ X19)
% 12.22/12.41          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 12.22/12.41          | (m1_subset_1 @ (sk_D @ X20 @ X19 @ X22) @ (u1_struct_0 @ X19))
% 12.22/12.41          | ~ (r2_hidden @ X22 @ (a_2_1_orders_2 @ X19 @ X20)))),
% 12.22/12.41      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 12.22/12.41  thf('72', plain,
% 12.22/12.41      (![X0 : $i, X1 : $i]:
% 12.22/12.41         (~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 12.22/12.41          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ 
% 12.22/12.41             (u1_struct_0 @ X0))
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0))),
% 12.22/12.41      inference('sup-', [status(thm)], ['70', '71'])).
% 12.22/12.41  thf('73', plain,
% 12.22/12.41      (![X0 : $i, X1 : $i]:
% 12.22/12.41         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ 
% 12.22/12.41             (u1_struct_0 @ X0)))),
% 12.22/12.41      inference('sup-', [status(thm)], ['69', '72'])).
% 12.22/12.41  thf('74', plain,
% 12.22/12.41      (![X0 : $i, X1 : $i]:
% 12.22/12.41         ((m1_subset_1 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ 
% 12.22/12.41           (u1_struct_0 @ X0))
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (u1_struct_0 @ X0))))),
% 12.22/12.41      inference('simplify', [status(thm)], ['73'])).
% 12.22/12.41  thf('75', plain,
% 12.22/12.41      (![X0 : $i, X1 : $i]:
% 12.22/12.41         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ 
% 12.22/12.41             (u1_struct_0 @ X0)))),
% 12.22/12.41      inference('sup-', [status(thm)], ['68', '74'])).
% 12.22/12.41  thf('76', plain,
% 12.22/12.41      (![X0 : $i]:
% 12.22/12.41         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 12.22/12.41          | (m1_subset_1 @ 
% 12.22/12.41             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 12.22/12.41              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 12.22/12.41             (u1_struct_0 @ X0))
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_struct_0 @ X0))),
% 12.22/12.41      inference('sup-', [status(thm)], ['67', '75'])).
% 12.22/12.41  thf(d10_orders_2, axiom,
% 12.22/12.41    (![A:$i]:
% 12.22/12.41     ( ( l1_orders_2 @ A ) =>
% 12.22/12.41       ( ![B:$i]:
% 12.22/12.41         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 12.22/12.41           ( ![C:$i]:
% 12.22/12.41             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 12.22/12.41               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 12.22/12.41                 ( ( r1_orders_2 @ A @ B @ C ) & ( ( B ) != ( C ) ) ) ) ) ) ) ) ))).
% 12.22/12.41  thf('77', plain,
% 12.22/12.41      (![X13 : $i, X14 : $i, X15 : $i]:
% 12.22/12.41         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 12.22/12.41          | ~ (r2_orders_2 @ X14 @ X13 @ X15)
% 12.22/12.41          | ((X13) != (X15))
% 12.22/12.41          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 12.22/12.41          | ~ (l1_orders_2 @ X14))),
% 12.22/12.41      inference('cnf', [status(esa)], [d10_orders_2])).
% 12.22/12.41  thf('78', plain,
% 12.22/12.41      (![X14 : $i, X15 : $i]:
% 12.22/12.41         (~ (l1_orders_2 @ X14)
% 12.22/12.41          | ~ (r2_orders_2 @ X14 @ X15 @ X15)
% 12.22/12.41          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14)))),
% 12.22/12.41      inference('simplify', [status(thm)], ['77'])).
% 12.22/12.41  thf('79', plain,
% 12.22/12.41      (![X0 : $i]:
% 12.22/12.41         (~ (l1_struct_0 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 12.22/12.41          | ~ (r2_orders_2 @ X0 @ 
% 12.22/12.41               (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 12.22/12.41                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 12.22/12.41               (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 12.22/12.41                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 12.22/12.41          | ~ (l1_orders_2 @ X0))),
% 12.22/12.41      inference('sup-', [status(thm)], ['76', '78'])).
% 12.22/12.41  thf('80', plain,
% 12.22/12.41      (![X0 : $i]:
% 12.22/12.41         (~ (r2_orders_2 @ X0 @ 
% 12.22/12.41             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 12.22/12.41              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 12.22/12.41             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 12.22/12.41              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 12.22/12.41          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_struct_0 @ X0))),
% 12.22/12.41      inference('simplify', [status(thm)], ['79'])).
% 12.22/12.41  thf('81', plain,
% 12.22/12.41      (![X0 : $i]:
% 12.22/12.41         (~ (r2_orders_2 @ X0 @ 
% 12.22/12.41             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 12.22/12.41              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 12.22/12.41             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 12.22/12.41      inference('sup-', [status(thm)], ['66', '80'])).
% 12.22/12.41  thf('82', plain,
% 12.22/12.41      (![X0 : $i]:
% 12.22/12.41         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | ~ (r2_orders_2 @ X0 @ 
% 12.22/12.41               (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 12.22/12.41                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 12.22/12.41               (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))),
% 12.22/12.41      inference('simplify', [status(thm)], ['81'])).
% 12.22/12.41  thf('83', plain,
% 12.22/12.41      (![X0 : $i]:
% 12.22/12.41         ((v1_xboole_0 @ (k2_struct_0 @ X0))
% 12.22/12.41          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | ~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 12.22/12.41      inference('sup-', [status(thm)], ['54', '82'])).
% 12.22/12.41  thf('84', plain,
% 12.22/12.41      (![X0 : $i]:
% 12.22/12.41         (~ (l1_orders_2 @ X0)
% 12.22/12.41          | ~ (v5_orders_2 @ X0)
% 12.22/12.41          | ~ (v4_orders_2 @ X0)
% 12.22/12.41          | ~ (v3_orders_2 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 12.22/12.41          | (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 12.22/12.41      inference('simplify', [status(thm)], ['83'])).
% 12.22/12.41  thf('85', plain,
% 12.22/12.41      (((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) != (k1_xboole_0))),
% 12.22/12.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.22/12.41  thf('86', plain,
% 12.22/12.41      ((((k1_xboole_0) != (k1_xboole_0))
% 12.22/12.41        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 12.22/12.41        | ~ (l1_struct_0 @ sk_A)
% 12.22/12.41        | (v2_struct_0 @ sk_A)
% 12.22/12.41        | ~ (v3_orders_2 @ sk_A)
% 12.22/12.41        | ~ (v4_orders_2 @ sk_A)
% 12.22/12.41        | ~ (v5_orders_2 @ sk_A)
% 12.22/12.41        | ~ (l1_orders_2 @ sk_A))),
% 12.22/12.41      inference('sup-', [status(thm)], ['84', '85'])).
% 12.22/12.41  thf('87', plain, ((l1_orders_2 @ sk_A)),
% 12.22/12.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.22/12.41  thf(dt_l1_orders_2, axiom,
% 12.22/12.41    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 12.22/12.41  thf('88', plain,
% 12.22/12.41      (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_orders_2 @ X18))),
% 12.22/12.41      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 12.22/12.41  thf('89', plain, ((l1_struct_0 @ sk_A)),
% 12.22/12.41      inference('sup-', [status(thm)], ['87', '88'])).
% 12.22/12.41  thf('90', plain, ((v3_orders_2 @ sk_A)),
% 12.22/12.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.22/12.41  thf('91', plain, ((v4_orders_2 @ sk_A)),
% 12.22/12.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.22/12.41  thf('92', plain, ((v5_orders_2 @ sk_A)),
% 12.22/12.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.22/12.41  thf('93', plain, ((l1_orders_2 @ sk_A)),
% 12.22/12.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.22/12.41  thf('94', plain,
% 12.22/12.41      ((((k1_xboole_0) != (k1_xboole_0))
% 12.22/12.41        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 12.22/12.41        | (v2_struct_0 @ sk_A))),
% 12.22/12.41      inference('demod', [status(thm)], ['86', '89', '90', '91', '92', '93'])).
% 12.22/12.41  thf('95', plain,
% 12.22/12.41      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 12.22/12.41      inference('simplify', [status(thm)], ['94'])).
% 12.22/12.41  thf('96', plain, (~ (v2_struct_0 @ sk_A)),
% 12.22/12.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.22/12.41  thf('97', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 12.22/12.41      inference('clc', [status(thm)], ['95', '96'])).
% 12.22/12.41  thf('98', plain,
% 12.22/12.41      (![X11 : $i]:
% 12.22/12.41         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 12.22/12.41      inference('cnf', [status(esa)], [d3_struct_0])).
% 12.22/12.41  thf(fc2_struct_0, axiom,
% 12.22/12.41    (![A:$i]:
% 12.22/12.41     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 12.22/12.41       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 12.22/12.41  thf('99', plain,
% 12.22/12.41      (![X12 : $i]:
% 12.22/12.41         (~ (v1_xboole_0 @ (u1_struct_0 @ X12))
% 12.22/12.41          | ~ (l1_struct_0 @ X12)
% 12.22/12.41          | (v2_struct_0 @ X12))),
% 12.22/12.41      inference('cnf', [status(esa)], [fc2_struct_0])).
% 12.22/12.41  thf('100', plain,
% 12.22/12.41      (![X0 : $i]:
% 12.22/12.41         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | (v2_struct_0 @ X0)
% 12.22/12.41          | ~ (l1_struct_0 @ X0))),
% 12.22/12.41      inference('sup-', [status(thm)], ['98', '99'])).
% 12.22/12.41  thf('101', plain,
% 12.22/12.41      (![X0 : $i]:
% 12.22/12.41         ((v2_struct_0 @ X0)
% 12.22/12.41          | ~ (l1_struct_0 @ X0)
% 12.22/12.41          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 12.22/12.41      inference('simplify', [status(thm)], ['100'])).
% 12.22/12.41  thf('102', plain, ((~ (l1_struct_0 @ sk_A) | (v2_struct_0 @ sk_A))),
% 12.22/12.41      inference('sup-', [status(thm)], ['97', '101'])).
% 12.22/12.41  thf('103', plain, ((l1_struct_0 @ sk_A)),
% 12.22/12.41      inference('sup-', [status(thm)], ['87', '88'])).
% 12.22/12.41  thf('104', plain, ((v2_struct_0 @ sk_A)),
% 12.22/12.41      inference('demod', [status(thm)], ['102', '103'])).
% 12.22/12.41  thf('105', plain, ($false), inference('demod', [status(thm)], ['0', '104'])).
% 12.22/12.41  
% 12.22/12.41  % SZS output end Refutation
% 12.22/12.41  
% 12.22/12.41  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
