%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YEMvMbu9cM

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:44 EST 2020

% Result     : Theorem 10.63s
% Output     : Refutation 10.63s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 267 expanded)
%              Number of leaves         :   33 (  96 expanded)
%              Depth                    :   23
%              Number of atoms          : 1918 (3764 expanded)
%              Number of equality atoms :   69 ( 166 expanded)
%              Maximal formula depth    :   23 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(a_2_1_orders_2_type,type,(
    a_2_1_orders_2: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k2_orders_2_type,type,(
    k2_orders_2: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

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

thf(t4_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i] :
                  ( ( ( r2_hidden @ C @ D )
                    & ( r2_hidden @ D @ E )
                    & ( r2_hidden @ E @ B ) )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('1',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_mcart_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('5',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

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
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

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

thf('9',plain,(
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

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( X1
        = ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
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
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
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
    inference('sup-',[status(thm)],['2','12'])).

thf('14',plain,(
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
    inference('sup-',[status(thm)],['1','13'])).

thf('15',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('16',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_mcart_1])).

thf('17',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('19',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('20',plain,(
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

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
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
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,(
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
    inference('sup-',[status(thm)],['16','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['15','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( k2_struct_0 @ X0 ) )
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
    inference('sup+',[status(thm)],['14','27'])).

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
      | ( m1_subset_1 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
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
    inference('sup-',[status(thm)],['1','13'])).

thf('33',plain,(
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
    inference('sup-',[status(thm)],['16','24'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) )
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
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('37',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_mcart_1])).

thf('38',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('39',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('40',plain,(
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

thf('41',plain,(
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
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( a_2_1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('44',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('45',plain,(
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

thf('46',plain,(
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
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
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
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
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
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,(
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
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
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
    inference('sup-',[status(thm)],['37','49'])).

thf('51',plain,(
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
    inference('sup-',[status(thm)],['36','50'])).

thf('52',plain,(
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
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
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
    inference('sup-',[status(thm)],['35','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( r2_hidden @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( k2_struct_0 @ X0 ) )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['31','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
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
    inference('sup-',[status(thm)],['1','13'])).

thf('58',plain,(
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
    inference('sup-',[status(thm)],['16','24'])).

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

thf('59',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( r2_orders_2 @ X14 @ X13 @ X15 )
      | ( X13 != X15 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('60',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X14 )
      | ~ ( r2_orders_2 @ X14 @ X15 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
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
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,(
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
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
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
    inference('sup-',[status(thm)],['57','62'])).

thf('64',plain,(
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
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('74',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('75',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69','70','71','72','75'])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
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

thf('81',plain,(
    ! [X12: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['79','83'])).

thf('85',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['73','74'])).

thf('86',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    $false ),
    inference(demod,[status(thm)],['0','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YEMvMbu9cM
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:43:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 10.63/10.81  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 10.63/10.81  % Solved by: fo/fo7.sh
% 10.63/10.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 10.63/10.81  % done 7563 iterations in 10.363s
% 10.63/10.81  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 10.63/10.81  % SZS output start Refutation
% 10.63/10.81  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 10.63/10.81  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 10.63/10.81  thf(a_2_1_orders_2_type, type, a_2_1_orders_2: $i > $i > $i).
% 10.63/10.81  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 10.63/10.81  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 10.63/10.81  thf(sk_A_type, type, sk_A: $i).
% 10.63/10.81  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 10.63/10.81  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 10.63/10.81  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 10.63/10.81  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 10.63/10.81  thf(sk_B_type, type, sk_B: $i > $i).
% 10.63/10.81  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 10.63/10.81  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 10.63/10.81  thf(k2_orders_2_type, type, k2_orders_2: $i > $i > $i).
% 10.63/10.81  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 10.63/10.81  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 10.63/10.81  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 10.63/10.81  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 10.63/10.81  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 10.63/10.81  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 10.63/10.81  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 10.63/10.81  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 10.63/10.81  thf(t46_orders_2, conjecture,
% 10.63/10.81    (![A:$i]:
% 10.63/10.81     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 10.63/10.81         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 10.63/10.81       ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ))).
% 10.63/10.81  thf(zf_stmt_0, negated_conjecture,
% 10.63/10.81    (~( ![A:$i]:
% 10.63/10.81        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 10.63/10.81            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 10.63/10.81          ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ) )),
% 10.63/10.81    inference('cnf.neg', [status(esa)], [t46_orders_2])).
% 10.63/10.81  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 10.63/10.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.63/10.81  thf(t4_mcart_1, axiom,
% 10.63/10.81    (![A:$i]:
% 10.63/10.81     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 10.63/10.81          ( ![B:$i]:
% 10.63/10.81            ( ~( ( r2_hidden @ B @ A ) & 
% 10.63/10.81                 ( ![C:$i,D:$i,E:$i]:
% 10.63/10.81                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 10.63/10.81                       ( r2_hidden @ E @ B ) ) =>
% 10.63/10.81                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 10.63/10.81  thf('1', plain,
% 10.63/10.81      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 10.63/10.81      inference('cnf', [status(esa)], [t4_mcart_1])).
% 10.63/10.81  thf(d3_struct_0, axiom,
% 10.63/10.81    (![A:$i]:
% 10.63/10.81     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 10.63/10.81  thf('2', plain,
% 10.63/10.81      (![X11 : $i]:
% 10.63/10.81         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 10.63/10.81      inference('cnf', [status(esa)], [d3_struct_0])).
% 10.63/10.81  thf(dt_k2_subset_1, axiom,
% 10.63/10.81    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 10.63/10.81  thf('3', plain,
% 10.63/10.81      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 10.63/10.81      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 10.63/10.81  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 10.63/10.81  thf('4', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 10.63/10.81      inference('cnf', [status(esa)], [d4_subset_1])).
% 10.63/10.81  thf('5', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 10.63/10.81      inference('demod', [status(thm)], ['3', '4'])).
% 10.63/10.81  thf(d13_orders_2, axiom,
% 10.63/10.81    (![A:$i]:
% 10.63/10.81     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 10.63/10.81         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 10.63/10.81       ( ![B:$i]:
% 10.63/10.81         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 10.63/10.81           ( ( k2_orders_2 @ A @ B ) = ( a_2_1_orders_2 @ A @ B ) ) ) ) ))).
% 10.63/10.81  thf('6', plain,
% 10.63/10.81      (![X16 : $i, X17 : $i]:
% 10.63/10.81         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 10.63/10.81          | ((k2_orders_2 @ X17 @ X16) = (a_2_1_orders_2 @ X17 @ X16))
% 10.63/10.81          | ~ (l1_orders_2 @ X17)
% 10.63/10.81          | ~ (v5_orders_2 @ X17)
% 10.63/10.81          | ~ (v4_orders_2 @ X17)
% 10.63/10.81          | ~ (v3_orders_2 @ X17)
% 10.63/10.81          | (v2_struct_0 @ X17))),
% 10.63/10.81      inference('cnf', [status(esa)], [d13_orders_2])).
% 10.63/10.81  thf('7', plain,
% 10.63/10.81      (![X0 : $i]:
% 10.63/10.81         ((v2_struct_0 @ X0)
% 10.63/10.81          | ~ (v3_orders_2 @ X0)
% 10.63/10.81          | ~ (v4_orders_2 @ X0)
% 10.63/10.81          | ~ (v5_orders_2 @ X0)
% 10.63/10.81          | ~ (l1_orders_2 @ X0)
% 10.63/10.81          | ((k2_orders_2 @ X0 @ (u1_struct_0 @ X0))
% 10.63/10.81              = (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0))))),
% 10.63/10.81      inference('sup-', [status(thm)], ['5', '6'])).
% 10.63/10.81  thf('8', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 10.63/10.81      inference('demod', [status(thm)], ['3', '4'])).
% 10.63/10.81  thf(fraenkel_a_2_1_orders_2, axiom,
% 10.63/10.81    (![A:$i,B:$i,C:$i]:
% 10.63/10.81     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 10.63/10.81         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 10.63/10.81         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 10.63/10.81       ( ( r2_hidden @ A @ ( a_2_1_orders_2 @ B @ C ) ) <=>
% 10.63/10.81         ( ?[D:$i]:
% 10.63/10.81           ( ( ![E:$i]:
% 10.63/10.81               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 10.63/10.81                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ D @ E ) ) ) ) & 
% 10.63/10.81             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 10.63/10.81  thf('9', plain,
% 10.63/10.81      (![X19 : $i, X20 : $i, X22 : $i]:
% 10.63/10.81         (~ (l1_orders_2 @ X19)
% 10.63/10.81          | ~ (v5_orders_2 @ X19)
% 10.63/10.81          | ~ (v4_orders_2 @ X19)
% 10.63/10.81          | ~ (v3_orders_2 @ X19)
% 10.63/10.81          | (v2_struct_0 @ X19)
% 10.63/10.81          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 10.63/10.81          | ((X22) = (sk_D @ X20 @ X19 @ X22))
% 10.63/10.81          | ~ (r2_hidden @ X22 @ (a_2_1_orders_2 @ X19 @ X20)))),
% 10.63/10.81      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 10.63/10.81  thf('10', plain,
% 10.63/10.81      (![X0 : $i, X1 : $i]:
% 10.63/10.81         (~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 10.63/10.81          | ((X1) = (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1))
% 10.63/10.81          | (v2_struct_0 @ X0)
% 10.63/10.81          | ~ (v3_orders_2 @ X0)
% 10.63/10.81          | ~ (v4_orders_2 @ X0)
% 10.63/10.81          | ~ (v5_orders_2 @ X0)
% 10.63/10.81          | ~ (l1_orders_2 @ X0))),
% 10.63/10.81      inference('sup-', [status(thm)], ['8', '9'])).
% 10.63/10.81  thf('11', plain,
% 10.63/10.81      (![X0 : $i, X1 : $i]:
% 10.63/10.81         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 10.63/10.81          | ~ (l1_orders_2 @ X0)
% 10.63/10.81          | ~ (v5_orders_2 @ X0)
% 10.63/10.81          | ~ (v4_orders_2 @ X0)
% 10.63/10.81          | ~ (v3_orders_2 @ X0)
% 10.63/10.81          | (v2_struct_0 @ X0)
% 10.63/10.81          | ~ (l1_orders_2 @ X0)
% 10.63/10.81          | ~ (v5_orders_2 @ X0)
% 10.63/10.81          | ~ (v4_orders_2 @ X0)
% 10.63/10.81          | ~ (v3_orders_2 @ X0)
% 10.63/10.81          | (v2_struct_0 @ X0)
% 10.63/10.81          | ((X1) = (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1)))),
% 10.63/10.81      inference('sup-', [status(thm)], ['7', '10'])).
% 10.63/10.81  thf('12', plain,
% 10.63/10.81      (![X0 : $i, X1 : $i]:
% 10.63/10.81         (((X1) = (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1))
% 10.63/10.81          | (v2_struct_0 @ X0)
% 10.63/10.81          | ~ (v3_orders_2 @ X0)
% 10.63/10.81          | ~ (v4_orders_2 @ X0)
% 10.63/10.81          | ~ (v5_orders_2 @ X0)
% 10.63/10.81          | ~ (l1_orders_2 @ X0)
% 10.63/10.81          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (u1_struct_0 @ X0))))),
% 10.63/10.81      inference('simplify', [status(thm)], ['11'])).
% 10.63/10.81  thf('13', plain,
% 10.63/10.81      (![X0 : $i, X1 : $i]:
% 10.63/10.81         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 10.63/10.81          | ~ (l1_struct_0 @ X0)
% 10.63/10.81          | ~ (l1_orders_2 @ X0)
% 10.63/10.81          | ~ (v5_orders_2 @ X0)
% 10.63/10.81          | ~ (v4_orders_2 @ X0)
% 10.63/10.81          | ~ (v3_orders_2 @ X0)
% 10.63/10.81          | (v2_struct_0 @ X0)
% 10.63/10.81          | ((X1) = (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1)))),
% 10.63/10.81      inference('sup-', [status(thm)], ['2', '12'])).
% 10.63/10.81  thf('14', plain,
% 10.63/10.81      (![X0 : $i]:
% 10.63/10.81         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.63/10.81          | ((sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 10.63/10.81              = (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 10.63/10.81                 (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 10.63/10.81          | (v2_struct_0 @ X0)
% 10.63/10.81          | ~ (v3_orders_2 @ X0)
% 10.63/10.81          | ~ (v4_orders_2 @ X0)
% 10.63/10.81          | ~ (v5_orders_2 @ X0)
% 10.63/10.81          | ~ (l1_orders_2 @ X0)
% 10.63/10.81          | ~ (l1_struct_0 @ X0))),
% 10.63/10.81      inference('sup-', [status(thm)], ['1', '13'])).
% 10.63/10.81  thf('15', plain,
% 10.63/10.81      (![X11 : $i]:
% 10.63/10.81         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 10.63/10.81      inference('cnf', [status(esa)], [d3_struct_0])).
% 10.63/10.81  thf('16', plain,
% 10.63/10.81      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 10.63/10.81      inference('cnf', [status(esa)], [t4_mcart_1])).
% 10.63/10.81  thf('17', plain,
% 10.63/10.81      (![X11 : $i]:
% 10.63/10.81         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 10.63/10.81      inference('cnf', [status(esa)], [d3_struct_0])).
% 10.63/10.81  thf('18', plain,
% 10.63/10.81      (![X0 : $i]:
% 10.63/10.81         ((v2_struct_0 @ X0)
% 10.63/10.81          | ~ (v3_orders_2 @ X0)
% 10.63/10.81          | ~ (v4_orders_2 @ X0)
% 10.63/10.81          | ~ (v5_orders_2 @ X0)
% 10.63/10.81          | ~ (l1_orders_2 @ X0)
% 10.63/10.81          | ((k2_orders_2 @ X0 @ (u1_struct_0 @ X0))
% 10.63/10.81              = (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0))))),
% 10.63/10.81      inference('sup-', [status(thm)], ['5', '6'])).
% 10.63/10.81  thf('19', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 10.63/10.81      inference('demod', [status(thm)], ['3', '4'])).
% 10.63/10.81  thf('20', plain,
% 10.63/10.81      (![X19 : $i, X20 : $i, X22 : $i]:
% 10.63/10.81         (~ (l1_orders_2 @ X19)
% 10.63/10.81          | ~ (v5_orders_2 @ X19)
% 10.63/10.81          | ~ (v4_orders_2 @ X19)
% 10.63/10.81          | ~ (v3_orders_2 @ X19)
% 10.63/10.81          | (v2_struct_0 @ X19)
% 10.63/10.81          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 10.63/10.81          | (m1_subset_1 @ (sk_D @ X20 @ X19 @ X22) @ (u1_struct_0 @ X19))
% 10.63/10.81          | ~ (r2_hidden @ X22 @ (a_2_1_orders_2 @ X19 @ X20)))),
% 10.63/10.81      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 10.63/10.81  thf('21', plain,
% 10.63/10.81      (![X0 : $i, X1 : $i]:
% 10.63/10.81         (~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 10.63/10.81          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ 
% 10.63/10.81             (u1_struct_0 @ X0))
% 10.63/10.81          | (v2_struct_0 @ X0)
% 10.63/10.81          | ~ (v3_orders_2 @ X0)
% 10.63/10.81          | ~ (v4_orders_2 @ X0)
% 10.63/10.81          | ~ (v5_orders_2 @ X0)
% 10.63/10.81          | ~ (l1_orders_2 @ X0))),
% 10.63/10.81      inference('sup-', [status(thm)], ['19', '20'])).
% 10.63/10.81  thf('22', plain,
% 10.63/10.81      (![X0 : $i, X1 : $i]:
% 10.63/10.81         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 10.63/10.81          | ~ (l1_orders_2 @ X0)
% 10.63/10.81          | ~ (v5_orders_2 @ X0)
% 10.63/10.81          | ~ (v4_orders_2 @ X0)
% 10.63/10.81          | ~ (v3_orders_2 @ X0)
% 10.63/10.81          | (v2_struct_0 @ X0)
% 10.63/10.81          | ~ (l1_orders_2 @ X0)
% 10.63/10.81          | ~ (v5_orders_2 @ X0)
% 10.63/10.81          | ~ (v4_orders_2 @ X0)
% 10.63/10.81          | ~ (v3_orders_2 @ X0)
% 10.63/10.81          | (v2_struct_0 @ X0)
% 10.63/10.81          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ 
% 10.63/10.81             (u1_struct_0 @ X0)))),
% 10.63/10.81      inference('sup-', [status(thm)], ['18', '21'])).
% 10.63/10.81  thf('23', plain,
% 10.63/10.81      (![X0 : $i, X1 : $i]:
% 10.63/10.81         ((m1_subset_1 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ 
% 10.63/10.81           (u1_struct_0 @ X0))
% 10.63/10.81          | (v2_struct_0 @ X0)
% 10.63/10.81          | ~ (v3_orders_2 @ X0)
% 10.63/10.81          | ~ (v4_orders_2 @ X0)
% 10.63/10.81          | ~ (v5_orders_2 @ X0)
% 10.63/10.81          | ~ (l1_orders_2 @ X0)
% 10.63/10.81          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (u1_struct_0 @ X0))))),
% 10.63/10.81      inference('simplify', [status(thm)], ['22'])).
% 10.63/10.81  thf('24', plain,
% 10.63/10.81      (![X0 : $i, X1 : $i]:
% 10.63/10.81         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 10.63/10.81          | ~ (l1_struct_0 @ X0)
% 10.63/10.81          | ~ (l1_orders_2 @ X0)
% 10.63/10.81          | ~ (v5_orders_2 @ X0)
% 10.63/10.81          | ~ (v4_orders_2 @ X0)
% 10.63/10.81          | ~ (v3_orders_2 @ X0)
% 10.63/10.81          | (v2_struct_0 @ X0)
% 10.63/10.81          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ 
% 10.63/10.81             (u1_struct_0 @ X0)))),
% 10.63/10.81      inference('sup-', [status(thm)], ['17', '23'])).
% 10.63/10.81  thf('25', plain,
% 10.63/10.81      (![X0 : $i]:
% 10.63/10.81         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.63/10.81          | (m1_subset_1 @ 
% 10.63/10.81             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 10.63/10.81              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 10.63/10.81             (u1_struct_0 @ X0))
% 10.63/10.81          | (v2_struct_0 @ X0)
% 10.63/10.81          | ~ (v3_orders_2 @ X0)
% 10.63/10.81          | ~ (v4_orders_2 @ X0)
% 10.63/10.81          | ~ (v5_orders_2 @ X0)
% 10.63/10.81          | ~ (l1_orders_2 @ X0)
% 10.63/10.81          | ~ (l1_struct_0 @ X0))),
% 10.63/10.81      inference('sup-', [status(thm)], ['16', '24'])).
% 10.63/10.81  thf('26', plain,
% 10.63/10.81      (![X0 : $i]:
% 10.63/10.81         ((m1_subset_1 @ 
% 10.63/10.81           (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 10.63/10.81            (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 10.63/10.81           (k2_struct_0 @ X0))
% 10.63/10.81          | ~ (l1_struct_0 @ X0)
% 10.63/10.81          | ~ (l1_struct_0 @ X0)
% 10.63/10.81          | ~ (l1_orders_2 @ X0)
% 10.63/10.81          | ~ (v5_orders_2 @ X0)
% 10.63/10.81          | ~ (v4_orders_2 @ X0)
% 10.63/10.81          | ~ (v3_orders_2 @ X0)
% 10.63/10.81          | (v2_struct_0 @ X0)
% 10.63/10.81          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 10.63/10.81      inference('sup+', [status(thm)], ['15', '25'])).
% 10.63/10.81  thf('27', plain,
% 10.63/10.81      (![X0 : $i]:
% 10.63/10.81         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.63/10.81          | (v2_struct_0 @ X0)
% 10.63/10.81          | ~ (v3_orders_2 @ X0)
% 10.63/10.81          | ~ (v4_orders_2 @ X0)
% 10.63/10.81          | ~ (v5_orders_2 @ X0)
% 10.63/10.81          | ~ (l1_orders_2 @ X0)
% 10.63/10.81          | ~ (l1_struct_0 @ X0)
% 10.63/10.81          | (m1_subset_1 @ 
% 10.63/10.81             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 10.63/10.81              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 10.63/10.81             (k2_struct_0 @ X0)))),
% 10.63/10.81      inference('simplify', [status(thm)], ['26'])).
% 10.63/10.81  thf('28', plain,
% 10.63/10.81      (![X0 : $i]:
% 10.63/10.81         ((m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 10.63/10.81           (k2_struct_0 @ X0))
% 10.63/10.81          | ~ (l1_struct_0 @ X0)
% 10.63/10.81          | ~ (l1_orders_2 @ X0)
% 10.63/10.81          | ~ (v5_orders_2 @ X0)
% 10.63/10.81          | ~ (v4_orders_2 @ X0)
% 10.63/10.81          | ~ (v3_orders_2 @ X0)
% 10.63/10.81          | (v2_struct_0 @ X0)
% 10.63/10.81          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.63/10.81          | ~ (l1_struct_0 @ X0)
% 10.63/10.81          | ~ (l1_orders_2 @ X0)
% 10.63/10.81          | ~ (v5_orders_2 @ X0)
% 10.63/10.81          | ~ (v4_orders_2 @ X0)
% 10.63/10.81          | ~ (v3_orders_2 @ X0)
% 10.63/10.81          | (v2_struct_0 @ X0)
% 10.63/10.81          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 10.63/10.81      inference('sup+', [status(thm)], ['14', '27'])).
% 10.63/10.81  thf('29', plain,
% 10.63/10.81      (![X0 : $i]:
% 10.63/10.81         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.63/10.81          | (v2_struct_0 @ X0)
% 10.63/10.81          | ~ (v3_orders_2 @ X0)
% 10.63/10.81          | ~ (v4_orders_2 @ X0)
% 10.63/10.81          | ~ (v5_orders_2 @ X0)
% 10.63/10.81          | ~ (l1_orders_2 @ X0)
% 10.63/10.81          | ~ (l1_struct_0 @ X0)
% 10.63/10.81          | (m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 10.63/10.81             (k2_struct_0 @ X0)))),
% 10.63/10.81      inference('simplify', [status(thm)], ['28'])).
% 10.63/10.81  thf(t2_subset, axiom,
% 10.63/10.81    (![A:$i,B:$i]:
% 10.63/10.81     ( ( m1_subset_1 @ A @ B ) =>
% 10.63/10.81       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 10.63/10.81  thf('30', plain,
% 10.63/10.81      (![X2 : $i, X3 : $i]:
% 10.63/10.81         ((r2_hidden @ X2 @ X3)
% 10.63/10.81          | (v1_xboole_0 @ X3)
% 10.63/10.81          | ~ (m1_subset_1 @ X2 @ X3))),
% 10.63/10.81      inference('cnf', [status(esa)], [t2_subset])).
% 10.63/10.81  thf('31', plain,
% 10.63/10.81      (![X0 : $i]:
% 10.63/10.81         (~ (l1_struct_0 @ X0)
% 10.63/10.81          | ~ (l1_orders_2 @ X0)
% 10.63/10.81          | ~ (v5_orders_2 @ X0)
% 10.63/10.81          | ~ (v4_orders_2 @ X0)
% 10.63/10.81          | ~ (v3_orders_2 @ X0)
% 10.63/10.81          | (v2_struct_0 @ X0)
% 10.63/10.81          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.63/10.81          | (v1_xboole_0 @ (k2_struct_0 @ X0))
% 10.63/10.81          | (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 10.63/10.81             (k2_struct_0 @ X0)))),
% 10.63/10.81      inference('sup-', [status(thm)], ['29', '30'])).
% 10.63/10.81  thf('32', plain,
% 10.63/10.81      (![X0 : $i]:
% 10.63/10.81         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.63/10.81          | ((sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 10.63/10.81              = (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 10.63/10.81                 (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 10.63/10.81          | (v2_struct_0 @ X0)
% 10.63/10.81          | ~ (v3_orders_2 @ X0)
% 10.63/10.81          | ~ (v4_orders_2 @ X0)
% 10.63/10.81          | ~ (v5_orders_2 @ X0)
% 10.63/10.81          | ~ (l1_orders_2 @ X0)
% 10.63/10.81          | ~ (l1_struct_0 @ X0))),
% 10.63/10.81      inference('sup-', [status(thm)], ['1', '13'])).
% 10.63/10.81  thf('33', plain,
% 10.63/10.81      (![X0 : $i]:
% 10.63/10.81         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.63/10.81          | (m1_subset_1 @ 
% 10.63/10.81             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 10.63/10.81              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 10.63/10.82             (u1_struct_0 @ X0))
% 10.63/10.82          | (v2_struct_0 @ X0)
% 10.63/10.82          | ~ (v3_orders_2 @ X0)
% 10.63/10.82          | ~ (v4_orders_2 @ X0)
% 10.63/10.82          | ~ (v5_orders_2 @ X0)
% 10.63/10.82          | ~ (l1_orders_2 @ X0)
% 10.63/10.82          | ~ (l1_struct_0 @ X0))),
% 10.63/10.82      inference('sup-', [status(thm)], ['16', '24'])).
% 10.63/10.82  thf('34', plain,
% 10.63/10.82      (![X0 : $i]:
% 10.63/10.82         ((m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 10.63/10.82           (u1_struct_0 @ X0))
% 10.63/10.82          | ~ (l1_struct_0 @ X0)
% 10.63/10.82          | ~ (l1_orders_2 @ X0)
% 10.63/10.82          | ~ (v5_orders_2 @ X0)
% 10.63/10.82          | ~ (v4_orders_2 @ X0)
% 10.63/10.82          | ~ (v3_orders_2 @ X0)
% 10.63/10.82          | (v2_struct_0 @ X0)
% 10.63/10.82          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.63/10.82          | ~ (l1_struct_0 @ X0)
% 10.63/10.82          | ~ (l1_orders_2 @ X0)
% 10.63/10.82          | ~ (v5_orders_2 @ X0)
% 10.63/10.82          | ~ (v4_orders_2 @ X0)
% 10.63/10.82          | ~ (v3_orders_2 @ X0)
% 10.63/10.82          | (v2_struct_0 @ X0)
% 10.63/10.82          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 10.63/10.82      inference('sup+', [status(thm)], ['32', '33'])).
% 10.63/10.82  thf('35', plain,
% 10.63/10.82      (![X0 : $i]:
% 10.63/10.82         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.63/10.82          | (v2_struct_0 @ X0)
% 10.63/10.82          | ~ (v3_orders_2 @ X0)
% 10.63/10.82          | ~ (v4_orders_2 @ X0)
% 10.63/10.82          | ~ (v5_orders_2 @ X0)
% 10.63/10.82          | ~ (l1_orders_2 @ X0)
% 10.63/10.82          | ~ (l1_struct_0 @ X0)
% 10.63/10.82          | (m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 10.63/10.82             (u1_struct_0 @ X0)))),
% 10.63/10.82      inference('simplify', [status(thm)], ['34'])).
% 10.63/10.82  thf('36', plain,
% 10.63/10.82      (![X11 : $i]:
% 10.63/10.82         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 10.63/10.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 10.63/10.82  thf('37', plain,
% 10.63/10.82      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 10.63/10.82      inference('cnf', [status(esa)], [t4_mcart_1])).
% 10.63/10.82  thf('38', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 10.63/10.82      inference('demod', [status(thm)], ['3', '4'])).
% 10.63/10.82  thf('39', plain,
% 10.63/10.82      (![X11 : $i]:
% 10.63/10.82         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 10.63/10.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 10.63/10.82  thf('40', plain,
% 10.63/10.82      (![X16 : $i, X17 : $i]:
% 10.63/10.82         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 10.63/10.82          | ((k2_orders_2 @ X17 @ X16) = (a_2_1_orders_2 @ X17 @ X16))
% 10.63/10.82          | ~ (l1_orders_2 @ X17)
% 10.63/10.82          | ~ (v5_orders_2 @ X17)
% 10.63/10.82          | ~ (v4_orders_2 @ X17)
% 10.63/10.82          | ~ (v3_orders_2 @ X17)
% 10.63/10.82          | (v2_struct_0 @ X17))),
% 10.63/10.82      inference('cnf', [status(esa)], [d13_orders_2])).
% 10.63/10.82  thf('41', plain,
% 10.63/10.82      (![X0 : $i, X1 : $i]:
% 10.63/10.82         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 10.63/10.82          | ~ (l1_struct_0 @ X0)
% 10.63/10.82          | (v2_struct_0 @ X0)
% 10.63/10.82          | ~ (v3_orders_2 @ X0)
% 10.63/10.82          | ~ (v4_orders_2 @ X0)
% 10.63/10.82          | ~ (v5_orders_2 @ X0)
% 10.63/10.82          | ~ (l1_orders_2 @ X0)
% 10.63/10.82          | ((k2_orders_2 @ X0 @ X1) = (a_2_1_orders_2 @ X0 @ X1)))),
% 10.63/10.82      inference('sup-', [status(thm)], ['39', '40'])).
% 10.63/10.82  thf('42', plain,
% 10.63/10.82      (![X0 : $i]:
% 10.63/10.82         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 10.63/10.82            = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 10.63/10.82          | ~ (l1_orders_2 @ X0)
% 10.63/10.82          | ~ (v5_orders_2 @ X0)
% 10.63/10.82          | ~ (v4_orders_2 @ X0)
% 10.63/10.82          | ~ (v3_orders_2 @ X0)
% 10.63/10.82          | (v2_struct_0 @ X0)
% 10.63/10.82          | ~ (l1_struct_0 @ X0))),
% 10.63/10.82      inference('sup-', [status(thm)], ['38', '41'])).
% 10.63/10.82  thf('43', plain,
% 10.63/10.82      (![X11 : $i]:
% 10.63/10.82         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 10.63/10.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 10.63/10.82  thf('44', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 10.63/10.82      inference('demod', [status(thm)], ['3', '4'])).
% 10.63/10.82  thf('45', plain,
% 10.63/10.82      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 10.63/10.82         (~ (l1_orders_2 @ X19)
% 10.63/10.82          | ~ (v5_orders_2 @ X19)
% 10.63/10.82          | ~ (v4_orders_2 @ X19)
% 10.63/10.82          | ~ (v3_orders_2 @ X19)
% 10.63/10.82          | (v2_struct_0 @ X19)
% 10.63/10.82          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 10.63/10.82          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X19))
% 10.63/10.82          | (r2_orders_2 @ X19 @ (sk_D @ X20 @ X19 @ X22) @ X21)
% 10.63/10.82          | ~ (r2_hidden @ X21 @ X20)
% 10.63/10.82          | ~ (r2_hidden @ X22 @ (a_2_1_orders_2 @ X19 @ X20)))),
% 10.63/10.82      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 10.63/10.82  thf('46', plain,
% 10.63/10.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.63/10.82         (~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 10.63/10.82          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X0))
% 10.63/10.82          | (r2_orders_2 @ X0 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ X2)
% 10.63/10.82          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 10.63/10.82          | (v2_struct_0 @ X0)
% 10.63/10.82          | ~ (v3_orders_2 @ X0)
% 10.63/10.82          | ~ (v4_orders_2 @ X0)
% 10.63/10.82          | ~ (v5_orders_2 @ X0)
% 10.63/10.82          | ~ (l1_orders_2 @ X0))),
% 10.63/10.82      inference('sup-', [status(thm)], ['44', '45'])).
% 10.63/10.82  thf('47', plain,
% 10.63/10.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.63/10.82         (~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 10.63/10.82          | ~ (l1_struct_0 @ X0)
% 10.63/10.82          | ~ (l1_orders_2 @ X0)
% 10.63/10.82          | ~ (v5_orders_2 @ X0)
% 10.63/10.82          | ~ (v4_orders_2 @ X0)
% 10.63/10.82          | ~ (v3_orders_2 @ X0)
% 10.63/10.82          | (v2_struct_0 @ X0)
% 10.63/10.82          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 10.63/10.82          | (r2_orders_2 @ X0 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ X2)
% 10.63/10.82          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X0)))),
% 10.63/10.82      inference('sup-', [status(thm)], ['43', '46'])).
% 10.63/10.82  thf('48', plain,
% 10.63/10.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.63/10.82         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 10.63/10.82          | ~ (l1_struct_0 @ X0)
% 10.63/10.82          | (v2_struct_0 @ X0)
% 10.63/10.82          | ~ (v3_orders_2 @ X0)
% 10.63/10.82          | ~ (v4_orders_2 @ X0)
% 10.63/10.82          | ~ (v5_orders_2 @ X0)
% 10.63/10.82          | ~ (l1_orders_2 @ X0)
% 10.63/10.82          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X0))
% 10.63/10.82          | (r2_orders_2 @ X0 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ X2)
% 10.63/10.82          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 10.63/10.82          | (v2_struct_0 @ X0)
% 10.63/10.82          | ~ (v3_orders_2 @ X0)
% 10.63/10.82          | ~ (v4_orders_2 @ X0)
% 10.63/10.82          | ~ (v5_orders_2 @ X0)
% 10.63/10.82          | ~ (l1_orders_2 @ X0)
% 10.63/10.82          | ~ (l1_struct_0 @ X0))),
% 10.63/10.82      inference('sup-', [status(thm)], ['42', '47'])).
% 10.63/10.82  thf('49', plain,
% 10.63/10.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.63/10.82         (~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 10.63/10.82          | (r2_orders_2 @ X0 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ X2)
% 10.63/10.82          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X0))
% 10.63/10.82          | ~ (l1_orders_2 @ X0)
% 10.63/10.82          | ~ (v5_orders_2 @ X0)
% 10.63/10.82          | ~ (v4_orders_2 @ X0)
% 10.63/10.82          | ~ (v3_orders_2 @ X0)
% 10.63/10.82          | (v2_struct_0 @ X0)
% 10.63/10.82          | ~ (l1_struct_0 @ X0)
% 10.63/10.82          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 10.63/10.82      inference('simplify', [status(thm)], ['48'])).
% 10.63/10.82  thf('50', plain,
% 10.63/10.82      (![X0 : $i, X1 : $i]:
% 10.63/10.82         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.63/10.82          | ~ (l1_struct_0 @ X0)
% 10.63/10.82          | (v2_struct_0 @ X0)
% 10.63/10.82          | ~ (v3_orders_2 @ X0)
% 10.63/10.82          | ~ (v4_orders_2 @ X0)
% 10.63/10.82          | ~ (v5_orders_2 @ X0)
% 10.63/10.82          | ~ (l1_orders_2 @ X0)
% 10.63/10.82          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 10.63/10.82          | (r2_orders_2 @ X0 @ 
% 10.63/10.82             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 10.63/10.82              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 10.63/10.82             X1)
% 10.63/10.82          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0)))),
% 10.63/10.82      inference('sup-', [status(thm)], ['37', '49'])).
% 10.63/10.82  thf('51', plain,
% 10.63/10.82      (![X0 : $i, X1 : $i]:
% 10.63/10.82         (~ (r2_hidden @ X1 @ (k2_struct_0 @ X0))
% 10.63/10.82          | ~ (l1_struct_0 @ X0)
% 10.63/10.82          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 10.63/10.82          | (r2_orders_2 @ X0 @ 
% 10.63/10.82             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 10.63/10.82              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 10.63/10.82             X1)
% 10.63/10.82          | ~ (l1_orders_2 @ X0)
% 10.63/10.82          | ~ (v5_orders_2 @ X0)
% 10.63/10.82          | ~ (v4_orders_2 @ X0)
% 10.63/10.82          | ~ (v3_orders_2 @ X0)
% 10.63/10.82          | (v2_struct_0 @ X0)
% 10.63/10.82          | ~ (l1_struct_0 @ X0)
% 10.63/10.82          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 10.63/10.82      inference('sup-', [status(thm)], ['36', '50'])).
% 10.63/10.82  thf('52', plain,
% 10.63/10.82      (![X0 : $i, X1 : $i]:
% 10.63/10.82         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.63/10.82          | (v2_struct_0 @ X0)
% 10.63/10.82          | ~ (v3_orders_2 @ X0)
% 10.63/10.82          | ~ (v4_orders_2 @ X0)
% 10.63/10.82          | ~ (v5_orders_2 @ X0)
% 10.63/10.82          | ~ (l1_orders_2 @ X0)
% 10.63/10.82          | (r2_orders_2 @ X0 @ 
% 10.63/10.82             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 10.63/10.82              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 10.63/10.82             X1)
% 10.63/10.82          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 10.63/10.82          | ~ (l1_struct_0 @ X0)
% 10.63/10.82          | ~ (r2_hidden @ X1 @ (k2_struct_0 @ X0)))),
% 10.63/10.82      inference('simplify', [status(thm)], ['51'])).
% 10.63/10.82  thf('53', plain,
% 10.63/10.82      (![X0 : $i]:
% 10.63/10.82         (~ (l1_struct_0 @ X0)
% 10.63/10.82          | ~ (l1_orders_2 @ X0)
% 10.63/10.82          | ~ (v5_orders_2 @ X0)
% 10.63/10.82          | ~ (v4_orders_2 @ X0)
% 10.63/10.82          | ~ (v3_orders_2 @ X0)
% 10.63/10.82          | (v2_struct_0 @ X0)
% 10.63/10.82          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.63/10.82          | ~ (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 10.63/10.82               (k2_struct_0 @ X0))
% 10.63/10.82          | ~ (l1_struct_0 @ X0)
% 10.63/10.82          | (r2_orders_2 @ X0 @ 
% 10.63/10.82             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 10.63/10.82              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 10.63/10.82             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 10.63/10.82          | ~ (l1_orders_2 @ X0)
% 10.63/10.82          | ~ (v5_orders_2 @ X0)
% 10.63/10.82          | ~ (v4_orders_2 @ X0)
% 10.63/10.82          | ~ (v3_orders_2 @ X0)
% 10.63/10.82          | (v2_struct_0 @ X0)
% 10.63/10.82          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 10.63/10.82      inference('sup-', [status(thm)], ['35', '52'])).
% 10.63/10.82  thf('54', plain,
% 10.63/10.82      (![X0 : $i]:
% 10.63/10.82         ((r2_orders_2 @ X0 @ 
% 10.63/10.82           (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 10.63/10.82            (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 10.63/10.82           (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 10.63/10.82          | ~ (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 10.63/10.82               (k2_struct_0 @ X0))
% 10.63/10.82          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.63/10.82          | (v2_struct_0 @ X0)
% 10.63/10.82          | ~ (v3_orders_2 @ X0)
% 10.63/10.82          | ~ (v4_orders_2 @ X0)
% 10.63/10.82          | ~ (v5_orders_2 @ X0)
% 10.63/10.82          | ~ (l1_orders_2 @ X0)
% 10.63/10.82          | ~ (l1_struct_0 @ X0))),
% 10.63/10.82      inference('simplify', [status(thm)], ['53'])).
% 10.63/10.82  thf('55', plain,
% 10.63/10.82      (![X0 : $i]:
% 10.63/10.82         ((v1_xboole_0 @ (k2_struct_0 @ X0))
% 10.63/10.82          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.63/10.82          | (v2_struct_0 @ X0)
% 10.63/10.82          | ~ (v3_orders_2 @ X0)
% 10.63/10.82          | ~ (v4_orders_2 @ X0)
% 10.63/10.82          | ~ (v5_orders_2 @ X0)
% 10.63/10.82          | ~ (l1_orders_2 @ X0)
% 10.63/10.82          | ~ (l1_struct_0 @ X0)
% 10.63/10.82          | ~ (l1_struct_0 @ X0)
% 10.63/10.82          | ~ (l1_orders_2 @ X0)
% 10.63/10.82          | ~ (v5_orders_2 @ X0)
% 10.63/10.82          | ~ (v4_orders_2 @ X0)
% 10.63/10.82          | ~ (v3_orders_2 @ X0)
% 10.63/10.82          | (v2_struct_0 @ X0)
% 10.63/10.82          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.63/10.82          | (r2_orders_2 @ X0 @ 
% 10.63/10.82             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 10.63/10.82              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 10.63/10.82             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))),
% 10.63/10.82      inference('sup-', [status(thm)], ['31', '54'])).
% 10.63/10.82  thf('56', plain,
% 10.63/10.82      (![X0 : $i]:
% 10.63/10.82         ((r2_orders_2 @ X0 @ 
% 10.63/10.82           (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 10.63/10.82            (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 10.63/10.82           (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 10.63/10.82          | ~ (l1_struct_0 @ X0)
% 10.63/10.82          | ~ (l1_orders_2 @ X0)
% 10.63/10.82          | ~ (v5_orders_2 @ X0)
% 10.63/10.82          | ~ (v4_orders_2 @ X0)
% 10.63/10.82          | ~ (v3_orders_2 @ X0)
% 10.63/10.82          | (v2_struct_0 @ X0)
% 10.63/10.82          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.63/10.82          | (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 10.63/10.82      inference('simplify', [status(thm)], ['55'])).
% 10.63/10.82  thf('57', plain,
% 10.63/10.82      (![X0 : $i]:
% 10.63/10.82         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.63/10.82          | ((sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 10.63/10.82              = (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 10.63/10.82                 (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 10.63/10.82          | (v2_struct_0 @ X0)
% 10.63/10.82          | ~ (v3_orders_2 @ X0)
% 10.63/10.82          | ~ (v4_orders_2 @ X0)
% 10.63/10.82          | ~ (v5_orders_2 @ X0)
% 10.63/10.82          | ~ (l1_orders_2 @ X0)
% 10.63/10.82          | ~ (l1_struct_0 @ X0))),
% 10.63/10.82      inference('sup-', [status(thm)], ['1', '13'])).
% 10.63/10.82  thf('58', plain,
% 10.63/10.82      (![X0 : $i]:
% 10.63/10.82         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.63/10.82          | (m1_subset_1 @ 
% 10.63/10.82             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 10.63/10.82              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 10.63/10.82             (u1_struct_0 @ X0))
% 10.63/10.82          | (v2_struct_0 @ X0)
% 10.63/10.82          | ~ (v3_orders_2 @ X0)
% 10.63/10.82          | ~ (v4_orders_2 @ X0)
% 10.63/10.82          | ~ (v5_orders_2 @ X0)
% 10.63/10.82          | ~ (l1_orders_2 @ X0)
% 10.63/10.82          | ~ (l1_struct_0 @ X0))),
% 10.63/10.82      inference('sup-', [status(thm)], ['16', '24'])).
% 10.63/10.82  thf(d10_orders_2, axiom,
% 10.63/10.82    (![A:$i]:
% 10.63/10.82     ( ( l1_orders_2 @ A ) =>
% 10.63/10.82       ( ![B:$i]:
% 10.63/10.82         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 10.63/10.82           ( ![C:$i]:
% 10.63/10.82             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 10.63/10.82               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 10.63/10.82                 ( ( r1_orders_2 @ A @ B @ C ) & ( ( B ) != ( C ) ) ) ) ) ) ) ) ))).
% 10.63/10.82  thf('59', plain,
% 10.63/10.82      (![X13 : $i, X14 : $i, X15 : $i]:
% 10.63/10.82         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 10.63/10.82          | ~ (r2_orders_2 @ X14 @ X13 @ X15)
% 10.63/10.82          | ((X13) != (X15))
% 10.63/10.82          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 10.63/10.82          | ~ (l1_orders_2 @ X14))),
% 10.63/10.82      inference('cnf', [status(esa)], [d10_orders_2])).
% 10.63/10.82  thf('60', plain,
% 10.63/10.82      (![X14 : $i, X15 : $i]:
% 10.63/10.82         (~ (l1_orders_2 @ X14)
% 10.63/10.82          | ~ (r2_orders_2 @ X14 @ X15 @ X15)
% 10.63/10.82          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14)))),
% 10.63/10.82      inference('simplify', [status(thm)], ['59'])).
% 10.63/10.82  thf('61', plain,
% 10.63/10.82      (![X0 : $i]:
% 10.63/10.82         (~ (l1_struct_0 @ X0)
% 10.63/10.82          | ~ (l1_orders_2 @ X0)
% 10.63/10.82          | ~ (v5_orders_2 @ X0)
% 10.63/10.82          | ~ (v4_orders_2 @ X0)
% 10.63/10.82          | ~ (v3_orders_2 @ X0)
% 10.63/10.82          | (v2_struct_0 @ X0)
% 10.63/10.82          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.63/10.82          | ~ (r2_orders_2 @ X0 @ 
% 10.63/10.82               (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 10.63/10.82                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 10.63/10.82               (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 10.63/10.82                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 10.63/10.82          | ~ (l1_orders_2 @ X0))),
% 10.63/10.82      inference('sup-', [status(thm)], ['58', '60'])).
% 10.63/10.82  thf('62', plain,
% 10.63/10.82      (![X0 : $i]:
% 10.63/10.82         (~ (r2_orders_2 @ X0 @ 
% 10.63/10.82             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 10.63/10.82              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 10.63/10.82             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 10.63/10.82              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 10.63/10.82          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.63/10.82          | (v2_struct_0 @ X0)
% 10.63/10.82          | ~ (v3_orders_2 @ X0)
% 10.63/10.82          | ~ (v4_orders_2 @ X0)
% 10.63/10.82          | ~ (v5_orders_2 @ X0)
% 10.63/10.82          | ~ (l1_orders_2 @ X0)
% 10.63/10.82          | ~ (l1_struct_0 @ X0))),
% 10.63/10.82      inference('simplify', [status(thm)], ['61'])).
% 10.63/10.82  thf('63', plain,
% 10.63/10.82      (![X0 : $i]:
% 10.63/10.82         (~ (r2_orders_2 @ X0 @ 
% 10.63/10.82             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 10.63/10.82              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 10.63/10.82             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 10.63/10.82          | ~ (l1_struct_0 @ X0)
% 10.63/10.82          | ~ (l1_orders_2 @ X0)
% 10.63/10.82          | ~ (v5_orders_2 @ X0)
% 10.63/10.82          | ~ (v4_orders_2 @ X0)
% 10.63/10.82          | ~ (v3_orders_2 @ X0)
% 10.63/10.82          | (v2_struct_0 @ X0)
% 10.63/10.82          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.63/10.82          | ~ (l1_struct_0 @ X0)
% 10.63/10.82          | ~ (l1_orders_2 @ X0)
% 10.63/10.82          | ~ (v5_orders_2 @ X0)
% 10.63/10.82          | ~ (v4_orders_2 @ X0)
% 10.63/10.82          | ~ (v3_orders_2 @ X0)
% 10.63/10.82          | (v2_struct_0 @ X0)
% 10.63/10.82          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 10.63/10.82      inference('sup-', [status(thm)], ['57', '62'])).
% 10.63/10.82  thf('64', plain,
% 10.63/10.82      (![X0 : $i]:
% 10.63/10.82         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.63/10.82          | (v2_struct_0 @ X0)
% 10.63/10.82          | ~ (v3_orders_2 @ X0)
% 10.63/10.82          | ~ (v4_orders_2 @ X0)
% 10.63/10.82          | ~ (v5_orders_2 @ X0)
% 10.63/10.82          | ~ (l1_orders_2 @ X0)
% 10.63/10.82          | ~ (l1_struct_0 @ X0)
% 10.63/10.82          | ~ (r2_orders_2 @ X0 @ 
% 10.63/10.82               (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 10.63/10.82                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 10.63/10.82               (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))),
% 10.63/10.82      inference('simplify', [status(thm)], ['63'])).
% 10.63/10.82  thf('65', plain,
% 10.63/10.82      (![X0 : $i]:
% 10.63/10.82         ((v1_xboole_0 @ (k2_struct_0 @ X0))
% 10.63/10.82          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.63/10.82          | (v2_struct_0 @ X0)
% 10.63/10.82          | ~ (v3_orders_2 @ X0)
% 10.63/10.82          | ~ (v4_orders_2 @ X0)
% 10.63/10.82          | ~ (v5_orders_2 @ X0)
% 10.63/10.82          | ~ (l1_orders_2 @ X0)
% 10.63/10.82          | ~ (l1_struct_0 @ X0)
% 10.63/10.82          | ~ (l1_struct_0 @ X0)
% 10.63/10.82          | ~ (l1_orders_2 @ X0)
% 10.63/10.82          | ~ (v5_orders_2 @ X0)
% 10.63/10.82          | ~ (v4_orders_2 @ X0)
% 10.63/10.82          | ~ (v3_orders_2 @ X0)
% 10.63/10.82          | (v2_struct_0 @ X0)
% 10.63/10.82          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 10.63/10.82      inference('sup-', [status(thm)], ['56', '64'])).
% 10.63/10.82  thf('66', plain,
% 10.63/10.82      (![X0 : $i]:
% 10.63/10.82         (~ (l1_struct_0 @ X0)
% 10.63/10.82          | ~ (l1_orders_2 @ X0)
% 10.63/10.82          | ~ (v5_orders_2 @ X0)
% 10.63/10.82          | ~ (v4_orders_2 @ X0)
% 10.63/10.82          | ~ (v3_orders_2 @ X0)
% 10.63/10.82          | (v2_struct_0 @ X0)
% 10.63/10.82          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.63/10.82          | (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 10.63/10.82      inference('simplify', [status(thm)], ['65'])).
% 10.63/10.82  thf('67', plain,
% 10.63/10.82      (((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) != (k1_xboole_0))),
% 10.63/10.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.63/10.82  thf('68', plain,
% 10.63/10.82      ((((k1_xboole_0) != (k1_xboole_0))
% 10.63/10.82        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 10.63/10.82        | (v2_struct_0 @ sk_A)
% 10.63/10.82        | ~ (v3_orders_2 @ sk_A)
% 10.63/10.82        | ~ (v4_orders_2 @ sk_A)
% 10.63/10.82        | ~ (v5_orders_2 @ sk_A)
% 10.63/10.82        | ~ (l1_orders_2 @ sk_A)
% 10.63/10.82        | ~ (l1_struct_0 @ sk_A))),
% 10.63/10.82      inference('sup-', [status(thm)], ['66', '67'])).
% 10.63/10.82  thf('69', plain, ((v3_orders_2 @ sk_A)),
% 10.63/10.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.63/10.82  thf('70', plain, ((v4_orders_2 @ sk_A)),
% 10.63/10.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.63/10.82  thf('71', plain, ((v5_orders_2 @ sk_A)),
% 10.63/10.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.63/10.82  thf('72', plain, ((l1_orders_2 @ sk_A)),
% 10.63/10.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.63/10.82  thf('73', plain, ((l1_orders_2 @ sk_A)),
% 10.63/10.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.63/10.82  thf(dt_l1_orders_2, axiom,
% 10.63/10.82    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 10.63/10.82  thf('74', plain,
% 10.63/10.82      (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_orders_2 @ X18))),
% 10.63/10.82      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 10.63/10.82  thf('75', plain, ((l1_struct_0 @ sk_A)),
% 10.63/10.82      inference('sup-', [status(thm)], ['73', '74'])).
% 10.63/10.82  thf('76', plain,
% 10.63/10.82      ((((k1_xboole_0) != (k1_xboole_0))
% 10.63/10.82        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 10.63/10.82        | (v2_struct_0 @ sk_A))),
% 10.63/10.82      inference('demod', [status(thm)], ['68', '69', '70', '71', '72', '75'])).
% 10.63/10.82  thf('77', plain,
% 10.63/10.82      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 10.63/10.82      inference('simplify', [status(thm)], ['76'])).
% 10.63/10.82  thf('78', plain, (~ (v2_struct_0 @ sk_A)),
% 10.63/10.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.63/10.82  thf('79', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 10.63/10.82      inference('clc', [status(thm)], ['77', '78'])).
% 10.63/10.82  thf('80', plain,
% 10.63/10.82      (![X11 : $i]:
% 10.63/10.82         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 10.63/10.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 10.63/10.82  thf(fc2_struct_0, axiom,
% 10.63/10.82    (![A:$i]:
% 10.63/10.82     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 10.63/10.82       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 10.63/10.82  thf('81', plain,
% 10.63/10.82      (![X12 : $i]:
% 10.63/10.82         (~ (v1_xboole_0 @ (u1_struct_0 @ X12))
% 10.63/10.82          | ~ (l1_struct_0 @ X12)
% 10.63/10.82          | (v2_struct_0 @ X12))),
% 10.63/10.82      inference('cnf', [status(esa)], [fc2_struct_0])).
% 10.63/10.82  thf('82', plain,
% 10.63/10.82      (![X0 : $i]:
% 10.63/10.82         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 10.63/10.82          | ~ (l1_struct_0 @ X0)
% 10.63/10.82          | (v2_struct_0 @ X0)
% 10.63/10.82          | ~ (l1_struct_0 @ X0))),
% 10.63/10.82      inference('sup-', [status(thm)], ['80', '81'])).
% 10.63/10.82  thf('83', plain,
% 10.63/10.82      (![X0 : $i]:
% 10.63/10.82         ((v2_struct_0 @ X0)
% 10.63/10.82          | ~ (l1_struct_0 @ X0)
% 10.63/10.82          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 10.63/10.82      inference('simplify', [status(thm)], ['82'])).
% 10.63/10.82  thf('84', plain, ((~ (l1_struct_0 @ sk_A) | (v2_struct_0 @ sk_A))),
% 10.63/10.82      inference('sup-', [status(thm)], ['79', '83'])).
% 10.63/10.82  thf('85', plain, ((l1_struct_0 @ sk_A)),
% 10.63/10.82      inference('sup-', [status(thm)], ['73', '74'])).
% 10.63/10.82  thf('86', plain, ((v2_struct_0 @ sk_A)),
% 10.63/10.82      inference('demod', [status(thm)], ['84', '85'])).
% 10.63/10.82  thf('87', plain, ($false), inference('demod', [status(thm)], ['0', '86'])).
% 10.63/10.82  
% 10.63/10.82  % SZS output end Refutation
% 10.63/10.82  
% 10.63/10.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
