%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QVfkO0cdLc

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:14 EST 2020

% Result     : Theorem 1.93s
% Output     : Refutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 350 expanded)
%              Number of leaves         :   42 ( 113 expanded)
%              Depth                    :   36
%              Number of atoms          : 1952 (7635 expanded)
%              Number of equality atoms :   63 ( 312 expanded)
%              Maximal formula depth    :   21 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_tsep_1_type,type,(
    k2_tsep_1: $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t17_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ~ ( r1_tsep_1 @ B @ C )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) )
                   => ( ? [E: $i] :
                          ( ( E = D )
                          & ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) )
                      & ? [E: $i] :
                          ( ( E = D )
                          & ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( m1_pre_topc @ C @ A ) )
               => ( ~ ( r1_tsep_1 @ B @ C )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) )
                     => ( ? [E: $i] :
                            ( ( E = D )
                            & ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) )
                        & ? [E: $i] :
                            ( ( E = D )
                            & ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tsep_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( m1_pre_topc @ B @ A )
        & ~ ( v2_struct_0 @ C )
        & ( m1_pre_topc @ C @ A ) )
     => ( ~ ( v2_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) )
        & ( v1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) )
        & ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ A ) ) ) )).

thf('3',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ~ ( m1_pre_topc @ X55 @ X56 )
      | ( v2_struct_0 @ X55 )
      | ~ ( l1_pre_topc @ X56 )
      | ( v2_struct_0 @ X56 )
      | ( v2_struct_0 @ X57 )
      | ~ ( m1_pre_topc @ X57 @ X56 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X56 @ X55 @ X57 ) @ X56 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k1_enumset1 @ X2 @ X2 @ X3 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_enumset1 @ X4 @ X4 @ X5 @ X6 )
      = ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k3_enumset1 @ X7 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_enumset1 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k4_enumset1 @ X11 @ X11 @ X12 @ X13 @ X14 @ X15 )
      = ( k3_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('12',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k5_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 )
      = ( k4_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(d5_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( H
        = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) )
    <=> ! [I: $i] :
          ( ( r2_hidden @ I @ H )
        <=> ~ ( ( I != G )
              & ( I != F )
              & ( I != E )
              & ( I != D )
              & ( I != C )
              & ( I != B )
              & ( I != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [I: $i,G: $i,F: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ I @ G @ F @ E @ D @ C @ B @ A )
    <=> ( ( I != A )
        & ( I != B )
        & ( I != C )
        & ( I != D )
        & ( I != E )
        & ( I != F )
        & ( I != G ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( H
        = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) )
    <=> ! [I: $i] :
          ( ( r2_hidden @ I @ H )
        <=> ~ ( zip_tseitin_0 @ I @ G @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 )
      | ( r2_hidden @ X31 @ X39 )
      | ( X39
       != ( k5_enumset1 @ X38 @ X37 @ X36 @ X35 @ X34 @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('14',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( r2_hidden @ X31 @ ( k5_enumset1 @ X38 @ X37 @ X36 @ X35 @ X34 @ X33 @ X32 ) )
      | ( zip_tseitin_0 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X6 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X5 ) ) ),
    inference('sup+',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X23 != X24 )
      | ~ ( zip_tseitin_0 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('17',plain,(
    ! [X22: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ~ ( zip_tseitin_0 @ X24 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X22 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( r2_hidden @ X5 @ ( k4_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','21'])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('23',plain,(
    ! [X44: $i,X45: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X44 ) @ X45 )
      | ~ ( r2_hidden @ X45 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X42 @ X43 ) )
      = ( k3_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ~ ( m1_pre_topc @ X55 @ X56 )
      | ( v2_struct_0 @ X55 )
      | ~ ( l1_pre_topc @ X56 )
      | ( v2_struct_0 @ X56 )
      | ( v2_struct_0 @ X57 )
      | ~ ( m1_pre_topc @ X57 @ X56 )
      | ( v1_pre_topc @ ( k2_tsep_1 @ X56 @ X55 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(d5_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ~ ( r1_tsep_1 @ B @ C )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( v1_pre_topc @ D )
                      & ( m1_pre_topc @ D @ A ) )
                   => ( ( D
                        = ( k2_tsep_1 @ A @ B @ C ) )
                    <=> ( ( u1_struct_0 @ D )
                        = ( k3_xboole_0 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) )).

thf('35',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( v2_struct_0 @ X51 )
      | ~ ( m1_pre_topc @ X51 @ X52 )
      | ( r1_tsep_1 @ X51 @ X53 )
      | ( v2_struct_0 @ X54 )
      | ~ ( v1_pre_topc @ X54 )
      | ~ ( m1_pre_topc @ X54 @ X52 )
      | ( X54
       != ( k2_tsep_1 @ X52 @ X51 @ X53 ) )
      | ( ( u1_struct_0 @ X54 )
        = ( k3_xboole_0 @ ( u1_struct_0 @ X51 ) @ ( u1_struct_0 @ X53 ) ) )
      | ~ ( m1_pre_topc @ X53 @ X52 )
      | ( v2_struct_0 @ X53 )
      | ~ ( l1_pre_topc @ X52 )
      | ( v2_struct_0 @ X52 ) ) ),
    inference(cnf,[status(esa)],[d5_tsep_1])).

thf('36',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( v2_struct_0 @ X52 )
      | ~ ( l1_pre_topc @ X52 )
      | ( v2_struct_0 @ X53 )
      | ~ ( m1_pre_topc @ X53 @ X52 )
      | ( ( u1_struct_0 @ ( k2_tsep_1 @ X52 @ X51 @ X53 ) )
        = ( k3_xboole_0 @ ( u1_struct_0 @ X51 ) @ ( u1_struct_0 @ X53 ) ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ X52 @ X51 @ X53 ) @ X52 )
      | ~ ( v1_pre_topc @ ( k2_tsep_1 @ X52 @ X51 @ X53 ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ X52 @ X51 @ X53 ) )
      | ( r1_tsep_1 @ X51 @ X53 )
      | ~ ( m1_pre_topc @ X51 @ X52 )
      | ( v2_struct_0 @ X51 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('42',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['33','42'])).

thf('44',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ~ ( m1_pre_topc @ X55 @ X56 )
      | ( v2_struct_0 @ X55 )
      | ~ ( l1_pre_topc @ X56 )
      | ( v2_struct_0 @ X56 )
      | ( v2_struct_0 @ X57 )
      | ~ ( m1_pre_topc @ X57 @ X56 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X56 @ X55 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('51',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['50'])).

thf(t4_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) )
              <=> ( m1_pre_topc @ B @ C ) ) ) ) ) )).

thf('52',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ~ ( m1_pre_topc @ X58 @ X59 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X58 ) @ ( u1_struct_0 @ X60 ) )
      | ( m1_pre_topc @ X58 @ X60 )
      | ~ ( m1_pre_topc @ X60 @ X59 )
      | ~ ( l1_pre_topc @ X59 )
      | ~ ( v2_pre_topc @ X59 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','53'])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['7','54'])).

thf('56',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['55','56','57','58'])).

thf('60',plain,
    ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('62',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( v2_struct_0 @ X48 )
      | ~ ( m1_pre_topc @ X48 @ X49 )
      | ( m1_subset_1 @ X50 @ ( u1_struct_0 @ X49 ) )
      | ~ ( m1_subset_1 @ X50 @ ( u1_struct_0 @ X48 ) )
      | ~ ( l1_pre_topc @ X49 )
      | ( v2_struct_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t55_pre_topc])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
    | ~ ( l1_pre_topc @ sk_C )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('66',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( m1_pre_topc @ X46 @ X47 )
      | ( l1_pre_topc @ X46 )
      | ~ ( l1_pre_topc @ X47 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('67',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['64','69'])).

thf('71',plain,
    ( ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ~ ( m1_pre_topc @ X55 @ X56 )
      | ( v2_struct_0 @ X55 )
      | ~ ( l1_pre_topc @ X56 )
      | ( v2_struct_0 @ X56 )
      | ( v2_struct_0 @ X57 )
      | ~ ( m1_pre_topc @ X57 @ X56 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X56 @ X55 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['73','74','75','76'])).

thf('78',plain,
    ( ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( m1_subset_1 @ X61 @ ( u1_struct_0 @ sk_B ) )
      | ( X61 != sk_D )
      | ~ ( m1_subset_1 @ X62 @ ( u1_struct_0 @ sk_C ) )
      | ( X62 != sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ! [X62: $i] :
        ( ( X62 != sk_D )
        | ~ ( m1_subset_1 @ X62 @ ( u1_struct_0 @ sk_C ) ) )
   <= ! [X62: $i] :
        ( ( X62 != sk_D )
        | ~ ( m1_subset_1 @ X62 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(split,[status(esa)],['79'])).

thf('81',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
   <= ! [X62: $i] :
        ( ( X62 != sk_D )
        | ~ ( m1_subset_1 @ X62 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['86','87','88','89'])).

thf('91',plain,
    ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( m1_pre_topc @ X46 @ X47 )
      | ( l1_pre_topc @ X46 )
      | ~ ( l1_pre_topc @ X47 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('96',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['93','98'])).

thf('100',plain,
    ( ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ~ ( m1_pre_topc @ X55 @ X56 )
      | ( v2_struct_0 @ X55 )
      | ~ ( l1_pre_topc @ X56 )
      | ( v2_struct_0 @ X56 )
      | ( v2_struct_0 @ X57 )
      | ~ ( m1_pre_topc @ X57 @ X56 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X56 @ X55 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['102','103','104','105'])).

thf('107',plain,
    ( ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,
    ( ! [X61: $i] :
        ( ( X61 != sk_D )
        | ~ ( m1_subset_1 @ X61 @ ( u1_struct_0 @ sk_B ) ) )
   <= ! [X61: $i] :
        ( ( X61 != sk_D )
        | ~ ( m1_subset_1 @ X61 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(split,[status(esa)],['79'])).

thf('109',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
   <= ! [X61: $i] :
        ( ( X61 != sk_D )
        | ~ ( m1_subset_1 @ X61 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C ) )
   <= ! [X61: $i] :
        ( ( X61 != sk_D )
        | ~ ( m1_subset_1 @ X61 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['107','109'])).

thf('111',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ! [X61: $i] :
        ( ( X61 != sk_D )
        | ~ ( m1_subset_1 @ X61 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X61: $i] :
        ( ( X61 != sk_D )
        | ~ ( m1_subset_1 @ X61 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ! [X61: $i] :
        ( ( X61 != sk_D )
        | ~ ( m1_subset_1 @ X61 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['114','115'])).

thf('117',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ~ ! [X61: $i] :
        ( ( X61 != sk_D )
        | ~ ( m1_subset_1 @ X61 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ! [X62: $i] :
        ( ( X62 != sk_D )
        | ~ ( m1_subset_1 @ X62 @ ( u1_struct_0 @ sk_C ) ) )
    | ! [X61: $i] :
        ( ( X61 != sk_D )
        | ~ ( m1_subset_1 @ X61 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(split,[status(esa)],['79'])).

thf('120',plain,(
    ! [X62: $i] :
      ( ( X62 != sk_D )
      | ~ ( m1_subset_1 @ X62 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sat_resolution*',[status(thm)],['118','119'])).

thf('121',plain,(
    ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['81','120'])).

thf('122',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['78','121'])).

thf('123',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['126','127'])).

thf('129',plain,(
    $false ),
    inference(demod,[status(thm)],['0','128'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QVfkO0cdLc
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:32:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.93/2.11  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.93/2.11  % Solved by: fo/fo7.sh
% 1.93/2.11  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.93/2.11  % done 1055 iterations in 1.651s
% 1.93/2.11  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.93/2.11  % SZS output start Refutation
% 1.93/2.11  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 1.93/2.11  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.93/2.11  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.93/2.11  thf(sk_C_type, type, sk_C: $i).
% 1.93/2.11  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 1.93/2.11                                               $i > $i > $o).
% 1.93/2.11  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.93/2.11  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 1.93/2.11  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.93/2.11  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.93/2.11  thf(sk_A_type, type, sk_A: $i).
% 1.93/2.11  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.93/2.11  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.93/2.11  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.93/2.11  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.93/2.11  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 1.93/2.11  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 1.93/2.11  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.93/2.11  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.93/2.11  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 1.93/2.11  thf(k2_tsep_1_type, type, k2_tsep_1: $i > $i > $i > $i).
% 1.93/2.11  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.93/2.11  thf(sk_D_type, type, sk_D: $i).
% 1.93/2.11  thf(sk_B_type, type, sk_B: $i).
% 1.93/2.11  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.93/2.11  thf(t17_tmap_1, conjecture,
% 1.93/2.11    (![A:$i]:
% 1.93/2.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.93/2.11       ( ![B:$i]:
% 1.93/2.11         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.93/2.11           ( ![C:$i]:
% 1.93/2.11             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.93/2.11               ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 1.93/2.11                 ( ![D:$i]:
% 1.93/2.11                   ( ( m1_subset_1 @
% 1.93/2.11                       D @ ( u1_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) =>
% 1.93/2.11                     ( ( ?[E:$i]:
% 1.93/2.11                         ( ( ( E ) = ( D ) ) & 
% 1.93/2.11                           ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) & 
% 1.93/2.11                       ( ?[E:$i]:
% 1.93/2.11                         ( ( ( E ) = ( D ) ) & 
% 1.93/2.11                           ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.93/2.11  thf(zf_stmt_0, negated_conjecture,
% 1.93/2.11    (~( ![A:$i]:
% 1.93/2.11        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.93/2.11            ( l1_pre_topc @ A ) ) =>
% 1.93/2.11          ( ![B:$i]:
% 1.93/2.11            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.93/2.11              ( ![C:$i]:
% 1.93/2.11                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.93/2.11                  ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 1.93/2.11                    ( ![D:$i]:
% 1.93/2.11                      ( ( m1_subset_1 @
% 1.93/2.11                          D @ ( u1_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) =>
% 1.93/2.11                        ( ( ?[E:$i]:
% 1.93/2.11                            ( ( ( E ) = ( D ) ) & 
% 1.93/2.11                              ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) & 
% 1.93/2.11                          ( ?[E:$i]:
% 1.93/2.11                            ( ( ( E ) = ( D ) ) & 
% 1.93/2.11                              ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.93/2.11    inference('cnf.neg', [status(esa)], [t17_tmap_1])).
% 1.93/2.11  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf(dt_k2_tsep_1, axiom,
% 1.93/2.11    (![A:$i,B:$i,C:$i]:
% 1.93/2.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 1.93/2.11         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 1.93/2.11         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.93/2.11       ( ( ~( v2_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) & 
% 1.93/2.11         ( v1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) ) & 
% 1.93/2.11         ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 1.93/2.11  thf('3', plain,
% 1.93/2.11      (![X55 : $i, X56 : $i, X57 : $i]:
% 1.93/2.11         (~ (m1_pre_topc @ X55 @ X56)
% 1.93/2.11          | (v2_struct_0 @ X55)
% 1.93/2.11          | ~ (l1_pre_topc @ X56)
% 1.93/2.11          | (v2_struct_0 @ X56)
% 1.93/2.11          | (v2_struct_0 @ X57)
% 1.93/2.11          | ~ (m1_pre_topc @ X57 @ X56)
% 1.93/2.11          | (m1_pre_topc @ (k2_tsep_1 @ X56 @ X55 @ X57) @ X56))),
% 1.93/2.11      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 1.93/2.11  thf('4', plain,
% 1.93/2.11      (![X0 : $i]:
% 1.93/2.11         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 1.93/2.11          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.93/2.11          | (v2_struct_0 @ X0)
% 1.93/2.11          | (v2_struct_0 @ sk_A)
% 1.93/2.11          | ~ (l1_pre_topc @ sk_A)
% 1.93/2.11          | (v2_struct_0 @ sk_B))),
% 1.93/2.11      inference('sup-', [status(thm)], ['2', '3'])).
% 1.93/2.11  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('6', plain,
% 1.93/2.11      (![X0 : $i]:
% 1.93/2.11         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 1.93/2.11          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.93/2.11          | (v2_struct_0 @ X0)
% 1.93/2.11          | (v2_struct_0 @ sk_A)
% 1.93/2.11          | (v2_struct_0 @ sk_B))),
% 1.93/2.11      inference('demod', [status(thm)], ['4', '5'])).
% 1.93/2.11  thf('7', plain,
% 1.93/2.11      (((v2_struct_0 @ sk_B)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_C)
% 1.93/2.11        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 1.93/2.11      inference('sup-', [status(thm)], ['1', '6'])).
% 1.93/2.11  thf(t70_enumset1, axiom,
% 1.93/2.11    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.93/2.11  thf('8', plain,
% 1.93/2.11      (![X2 : $i, X3 : $i]:
% 1.93/2.11         ((k1_enumset1 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 1.93/2.11      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.93/2.11  thf(t71_enumset1, axiom,
% 1.93/2.11    (![A:$i,B:$i,C:$i]:
% 1.93/2.11     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 1.93/2.11  thf('9', plain,
% 1.93/2.11      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.93/2.11         ((k2_enumset1 @ X4 @ X4 @ X5 @ X6) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 1.93/2.11      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.93/2.11  thf(t72_enumset1, axiom,
% 1.93/2.11    (![A:$i,B:$i,C:$i,D:$i]:
% 1.93/2.11     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 1.93/2.11  thf('10', plain,
% 1.93/2.11      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.93/2.11         ((k3_enumset1 @ X7 @ X7 @ X8 @ X9 @ X10)
% 1.93/2.11           = (k2_enumset1 @ X7 @ X8 @ X9 @ X10))),
% 1.93/2.11      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.93/2.11  thf(t73_enumset1, axiom,
% 1.93/2.11    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.93/2.11     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 1.93/2.11       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 1.93/2.11  thf('11', plain,
% 1.93/2.11      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 1.93/2.11         ((k4_enumset1 @ X11 @ X11 @ X12 @ X13 @ X14 @ X15)
% 1.93/2.11           = (k3_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15))),
% 1.93/2.11      inference('cnf', [status(esa)], [t73_enumset1])).
% 1.93/2.11  thf(t74_enumset1, axiom,
% 1.93/2.11    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.93/2.11     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 1.93/2.11       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 1.93/2.11  thf('12', plain,
% 1.93/2.11      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.93/2.11         ((k5_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21)
% 1.93/2.11           = (k4_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21))),
% 1.93/2.11      inference('cnf', [status(esa)], [t74_enumset1])).
% 1.93/2.11  thf(d5_enumset1, axiom,
% 1.93/2.11    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 1.93/2.11     ( ( ( H ) = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) <=>
% 1.93/2.11       ( ![I:$i]:
% 1.93/2.11         ( ( r2_hidden @ I @ H ) <=>
% 1.93/2.11           ( ~( ( ( I ) != ( G ) ) & ( ( I ) != ( F ) ) & ( ( I ) != ( E ) ) & 
% 1.93/2.11                ( ( I ) != ( D ) ) & ( ( I ) != ( C ) ) & ( ( I ) != ( B ) ) & 
% 1.93/2.11                ( ( I ) != ( A ) ) ) ) ) ) ))).
% 1.93/2.11  thf(zf_stmt_1, type, zip_tseitin_0 :
% 1.93/2.11      $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 1.93/2.11  thf(zf_stmt_2, axiom,
% 1.93/2.11    (![I:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 1.93/2.11     ( ( zip_tseitin_0 @ I @ G @ F @ E @ D @ C @ B @ A ) <=>
% 1.93/2.11       ( ( ( I ) != ( A ) ) & ( ( I ) != ( B ) ) & ( ( I ) != ( C ) ) & 
% 1.93/2.11         ( ( I ) != ( D ) ) & ( ( I ) != ( E ) ) & ( ( I ) != ( F ) ) & 
% 1.93/2.11         ( ( I ) != ( G ) ) ) ))).
% 1.93/2.11  thf(zf_stmt_3, axiom,
% 1.93/2.11    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 1.93/2.11     ( ( ( H ) = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) <=>
% 1.93/2.11       ( ![I:$i]:
% 1.93/2.11         ( ( r2_hidden @ I @ H ) <=>
% 1.93/2.11           ( ~( zip_tseitin_0 @ I @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 1.93/2.11  thf('13', plain,
% 1.93/2.11      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, 
% 1.93/2.11         X38 : $i, X39 : $i]:
% 1.93/2.11         ((zip_tseitin_0 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38)
% 1.93/2.11          | (r2_hidden @ X31 @ X39)
% 1.93/2.11          | ((X39) != (k5_enumset1 @ X38 @ X37 @ X36 @ X35 @ X34 @ X33 @ X32)))),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.93/2.11  thf('14', plain,
% 1.93/2.11      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, 
% 1.93/2.11         X38 : $i]:
% 1.93/2.11         ((r2_hidden @ X31 @ 
% 1.93/2.11           (k5_enumset1 @ X38 @ X37 @ X36 @ X35 @ X34 @ X33 @ X32))
% 1.93/2.11          | (zip_tseitin_0 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38))),
% 1.93/2.11      inference('simplify', [status(thm)], ['13'])).
% 1.93/2.11  thf('15', plain,
% 1.93/2.11      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.93/2.11         ((r2_hidden @ X6 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 1.93/2.11          | (zip_tseitin_0 @ X6 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X5))),
% 1.93/2.11      inference('sup+', [status(thm)], ['12', '14'])).
% 1.93/2.11  thf('16', plain,
% 1.93/2.11      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, 
% 1.93/2.11         X29 : $i]:
% 1.93/2.11         (((X23) != (X24))
% 1.93/2.11          | ~ (zip_tseitin_0 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X22))),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.93/2.11  thf('17', plain,
% 1.93/2.11      (![X22 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.93/2.11         ~ (zip_tseitin_0 @ X24 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X22)),
% 1.93/2.11      inference('simplify', [status(thm)], ['16'])).
% 1.93/2.11  thf('18', plain,
% 1.93/2.11      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.93/2.11         (r2_hidden @ X5 @ (k4_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5))),
% 1.93/2.11      inference('sup-', [status(thm)], ['15', '17'])).
% 1.93/2.11  thf('19', plain,
% 1.93/2.11      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.93/2.11         (r2_hidden @ X0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 1.93/2.11      inference('sup+', [status(thm)], ['11', '18'])).
% 1.93/2.11  thf('20', plain,
% 1.93/2.11      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.93/2.11         (r2_hidden @ X0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 1.93/2.11      inference('sup+', [status(thm)], ['10', '19'])).
% 1.93/2.11  thf('21', plain,
% 1.93/2.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.93/2.11         (r2_hidden @ X0 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.93/2.11      inference('sup+', [status(thm)], ['9', '20'])).
% 1.93/2.11  thf('22', plain,
% 1.93/2.11      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 1.93/2.11      inference('sup+', [status(thm)], ['8', '21'])).
% 1.93/2.11  thf(t4_setfam_1, axiom,
% 1.93/2.11    (![A:$i,B:$i]:
% 1.93/2.11     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 1.93/2.11  thf('23', plain,
% 1.93/2.11      (![X44 : $i, X45 : $i]:
% 1.93/2.11         ((r1_tarski @ (k1_setfam_1 @ X44) @ X45) | ~ (r2_hidden @ X45 @ X44))),
% 1.93/2.11      inference('cnf', [status(esa)], [t4_setfam_1])).
% 1.93/2.11  thf('24', plain,
% 1.93/2.11      (![X0 : $i, X1 : $i]:
% 1.93/2.11         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 1.93/2.11      inference('sup-', [status(thm)], ['22', '23'])).
% 1.93/2.11  thf(t12_setfam_1, axiom,
% 1.93/2.11    (![A:$i,B:$i]:
% 1.93/2.11     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.93/2.11  thf('25', plain,
% 1.93/2.11      (![X42 : $i, X43 : $i]:
% 1.93/2.11         ((k1_setfam_1 @ (k2_tarski @ X42 @ X43)) = (k3_xboole_0 @ X42 @ X43))),
% 1.93/2.11      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.93/2.11  thf('26', plain,
% 1.93/2.11      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.93/2.11      inference('demod', [status(thm)], ['24', '25'])).
% 1.93/2.11  thf('27', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('28', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('29', plain,
% 1.93/2.11      (![X55 : $i, X56 : $i, X57 : $i]:
% 1.93/2.11         (~ (m1_pre_topc @ X55 @ X56)
% 1.93/2.11          | (v2_struct_0 @ X55)
% 1.93/2.11          | ~ (l1_pre_topc @ X56)
% 1.93/2.11          | (v2_struct_0 @ X56)
% 1.93/2.11          | (v2_struct_0 @ X57)
% 1.93/2.11          | ~ (m1_pre_topc @ X57 @ X56)
% 1.93/2.11          | (v1_pre_topc @ (k2_tsep_1 @ X56 @ X55 @ X57)))),
% 1.93/2.11      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 1.93/2.11  thf('30', plain,
% 1.93/2.11      (![X0 : $i]:
% 1.93/2.11         ((v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 1.93/2.11          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.93/2.11          | (v2_struct_0 @ X0)
% 1.93/2.11          | (v2_struct_0 @ sk_A)
% 1.93/2.11          | ~ (l1_pre_topc @ sk_A)
% 1.93/2.11          | (v2_struct_0 @ sk_B))),
% 1.93/2.11      inference('sup-', [status(thm)], ['28', '29'])).
% 1.93/2.11  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('32', plain,
% 1.93/2.11      (![X0 : $i]:
% 1.93/2.11         ((v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 1.93/2.11          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.93/2.11          | (v2_struct_0 @ X0)
% 1.93/2.11          | (v2_struct_0 @ sk_A)
% 1.93/2.11          | (v2_struct_0 @ sk_B))),
% 1.93/2.11      inference('demod', [status(thm)], ['30', '31'])).
% 1.93/2.11  thf('33', plain,
% 1.93/2.11      (((v2_struct_0 @ sk_B)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_C)
% 1.93/2.11        | (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.93/2.11      inference('sup-', [status(thm)], ['27', '32'])).
% 1.93/2.11  thf('34', plain,
% 1.93/2.11      (((v2_struct_0 @ sk_B)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_C)
% 1.93/2.11        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 1.93/2.11      inference('sup-', [status(thm)], ['1', '6'])).
% 1.93/2.11  thf(d5_tsep_1, axiom,
% 1.93/2.11    (![A:$i]:
% 1.93/2.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 1.93/2.11       ( ![B:$i]:
% 1.93/2.11         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.93/2.11           ( ![C:$i]:
% 1.93/2.11             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.93/2.11               ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 1.93/2.11                 ( ![D:$i]:
% 1.93/2.11                   ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 1.93/2.11                       ( m1_pre_topc @ D @ A ) ) =>
% 1.93/2.11                     ( ( ( D ) = ( k2_tsep_1 @ A @ B @ C ) ) <=>
% 1.93/2.11                       ( ( u1_struct_0 @ D ) =
% 1.93/2.11                         ( k3_xboole_0 @
% 1.93/2.11                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.93/2.11  thf('35', plain,
% 1.93/2.11      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 1.93/2.11         ((v2_struct_0 @ X51)
% 1.93/2.11          | ~ (m1_pre_topc @ X51 @ X52)
% 1.93/2.11          | (r1_tsep_1 @ X51 @ X53)
% 1.93/2.11          | (v2_struct_0 @ X54)
% 1.93/2.11          | ~ (v1_pre_topc @ X54)
% 1.93/2.11          | ~ (m1_pre_topc @ X54 @ X52)
% 1.93/2.11          | ((X54) != (k2_tsep_1 @ X52 @ X51 @ X53))
% 1.93/2.11          | ((u1_struct_0 @ X54)
% 1.93/2.11              = (k3_xboole_0 @ (u1_struct_0 @ X51) @ (u1_struct_0 @ X53)))
% 1.93/2.11          | ~ (m1_pre_topc @ X53 @ X52)
% 1.93/2.11          | (v2_struct_0 @ X53)
% 1.93/2.11          | ~ (l1_pre_topc @ X52)
% 1.93/2.11          | (v2_struct_0 @ X52))),
% 1.93/2.11      inference('cnf', [status(esa)], [d5_tsep_1])).
% 1.93/2.11  thf('36', plain,
% 1.93/2.11      (![X51 : $i, X52 : $i, X53 : $i]:
% 1.93/2.11         ((v2_struct_0 @ X52)
% 1.93/2.11          | ~ (l1_pre_topc @ X52)
% 1.93/2.11          | (v2_struct_0 @ X53)
% 1.93/2.11          | ~ (m1_pre_topc @ X53 @ X52)
% 1.93/2.11          | ((u1_struct_0 @ (k2_tsep_1 @ X52 @ X51 @ X53))
% 1.93/2.11              = (k3_xboole_0 @ (u1_struct_0 @ X51) @ (u1_struct_0 @ X53)))
% 1.93/2.11          | ~ (m1_pre_topc @ (k2_tsep_1 @ X52 @ X51 @ X53) @ X52)
% 1.93/2.11          | ~ (v1_pre_topc @ (k2_tsep_1 @ X52 @ X51 @ X53))
% 1.93/2.11          | (v2_struct_0 @ (k2_tsep_1 @ X52 @ X51 @ X53))
% 1.93/2.11          | (r1_tsep_1 @ X51 @ X53)
% 1.93/2.11          | ~ (m1_pre_topc @ X51 @ X52)
% 1.93/2.11          | (v2_struct_0 @ X51))),
% 1.93/2.11      inference('simplify', [status(thm)], ['35'])).
% 1.93/2.11  thf('37', plain,
% 1.93/2.11      (((v2_struct_0 @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 1.93/2.11        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.11        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.11        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.11            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.93/2.11        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_C)
% 1.93/2.11        | ~ (l1_pre_topc @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_A))),
% 1.93/2.11      inference('sup-', [status(thm)], ['34', '36'])).
% 1.93/2.11  thf('38', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('39', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('41', plain,
% 1.93/2.11      (((v2_struct_0 @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.11        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.11        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.11            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.93/2.11        | (v2_struct_0 @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ sk_A))),
% 1.93/2.11      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 1.93/2.11  thf('42', plain,
% 1.93/2.11      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.11          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.93/2.11        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.11        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.11        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_C))),
% 1.93/2.11      inference('simplify', [status(thm)], ['41'])).
% 1.93/2.11  thf('43', plain,
% 1.93/2.11      (((v2_struct_0 @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | (v2_struct_0 @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.11        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.11            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))),
% 1.93/2.11      inference('sup-', [status(thm)], ['33', '42'])).
% 1.93/2.11  thf('44', plain,
% 1.93/2.11      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.11          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.93/2.11        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.11        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_C))),
% 1.93/2.11      inference('simplify', [status(thm)], ['43'])).
% 1.93/2.11  thf('45', plain,
% 1.93/2.11      (![X55 : $i, X56 : $i, X57 : $i]:
% 1.93/2.11         (~ (m1_pre_topc @ X55 @ X56)
% 1.93/2.11          | (v2_struct_0 @ X55)
% 1.93/2.11          | ~ (l1_pre_topc @ X56)
% 1.93/2.11          | (v2_struct_0 @ X56)
% 1.93/2.11          | (v2_struct_0 @ X57)
% 1.93/2.11          | ~ (m1_pre_topc @ X57 @ X56)
% 1.93/2.11          | ~ (v2_struct_0 @ (k2_tsep_1 @ X56 @ X55 @ X57)))),
% 1.93/2.11      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 1.93/2.11  thf('46', plain,
% 1.93/2.11      (((v2_struct_0 @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.11        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.11            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.93/2.11        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | ~ (l1_pre_topc @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 1.93/2.11      inference('sup-', [status(thm)], ['44', '45'])).
% 1.93/2.11  thf('47', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('49', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('50', plain,
% 1.93/2.11      (((v2_struct_0 @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.11        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.11            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.93/2.11        | (v2_struct_0 @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_B))),
% 1.93/2.11      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 1.93/2.11  thf('51', plain,
% 1.93/2.11      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.11          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.93/2.11        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_C))),
% 1.93/2.11      inference('simplify', [status(thm)], ['50'])).
% 1.93/2.11  thf(t4_tsep_1, axiom,
% 1.93/2.11    (![A:$i]:
% 1.93/2.11     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.93/2.11       ( ![B:$i]:
% 1.93/2.11         ( ( m1_pre_topc @ B @ A ) =>
% 1.93/2.11           ( ![C:$i]:
% 1.93/2.11             ( ( m1_pre_topc @ C @ A ) =>
% 1.93/2.11               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 1.93/2.11                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 1.93/2.11  thf('52', plain,
% 1.93/2.11      (![X58 : $i, X59 : $i, X60 : $i]:
% 1.93/2.11         (~ (m1_pre_topc @ X58 @ X59)
% 1.93/2.11          | ~ (r1_tarski @ (u1_struct_0 @ X58) @ (u1_struct_0 @ X60))
% 1.93/2.11          | (m1_pre_topc @ X58 @ X60)
% 1.93/2.11          | ~ (m1_pre_topc @ X60 @ X59)
% 1.93/2.11          | ~ (l1_pre_topc @ X59)
% 1.93/2.11          | ~ (v2_pre_topc @ X59))),
% 1.93/2.11      inference('cnf', [status(esa)], [t4_tsep_1])).
% 1.93/2.11  thf('53', plain,
% 1.93/2.11      (![X0 : $i, X1 : $i]:
% 1.93/2.11         (~ (r1_tarski @ 
% 1.93/2.11             (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)) @ 
% 1.93/2.11             (u1_struct_0 @ X0))
% 1.93/2.11          | (v2_struct_0 @ sk_C)
% 1.93/2.11          | (v2_struct_0 @ sk_A)
% 1.93/2.11          | (v2_struct_0 @ sk_B)
% 1.93/2.11          | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.11          | ~ (v2_pre_topc @ X1)
% 1.93/2.11          | ~ (l1_pre_topc @ X1)
% 1.93/2.11          | ~ (m1_pre_topc @ X0 @ X1)
% 1.93/2.11          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 1.93/2.11          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X1))),
% 1.93/2.11      inference('sup-', [status(thm)], ['51', '52'])).
% 1.93/2.11  thf('54', plain,
% 1.93/2.11      (![X0 : $i]:
% 1.93/2.11         (~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 1.93/2.11          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C)
% 1.93/2.11          | ~ (m1_pre_topc @ sk_C @ X0)
% 1.93/2.11          | ~ (l1_pre_topc @ X0)
% 1.93/2.11          | ~ (v2_pre_topc @ X0)
% 1.93/2.11          | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.11          | (v2_struct_0 @ sk_B)
% 1.93/2.11          | (v2_struct_0 @ sk_A)
% 1.93/2.11          | (v2_struct_0 @ sk_C))),
% 1.93/2.11      inference('sup-', [status(thm)], ['26', '53'])).
% 1.93/2.11  thf('55', plain,
% 1.93/2.11      (((v2_struct_0 @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | (v2_struct_0 @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.11        | ~ (v2_pre_topc @ sk_A)
% 1.93/2.11        | ~ (l1_pre_topc @ sk_A)
% 1.93/2.11        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.93/2.11        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C))),
% 1.93/2.11      inference('sup-', [status(thm)], ['7', '54'])).
% 1.93/2.11  thf('56', plain, ((v2_pre_topc @ sk_A)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('58', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('59', plain,
% 1.93/2.11      (((v2_struct_0 @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | (v2_struct_0 @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.11        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C))),
% 1.93/2.11      inference('demod', [status(thm)], ['55', '56', '57', '58'])).
% 1.93/2.11  thf('60', plain,
% 1.93/2.11      (((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C)
% 1.93/2.11        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_C))),
% 1.93/2.11      inference('simplify', [status(thm)], ['59'])).
% 1.93/2.11  thf('61', plain,
% 1.93/2.11      ((m1_subset_1 @ sk_D @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf(t55_pre_topc, axiom,
% 1.93/2.11    (![A:$i]:
% 1.93/2.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 1.93/2.11       ( ![B:$i]:
% 1.93/2.11         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.93/2.11           ( ![C:$i]:
% 1.93/2.11             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 1.93/2.11               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 1.93/2.11  thf('62', plain,
% 1.93/2.11      (![X48 : $i, X49 : $i, X50 : $i]:
% 1.93/2.11         ((v2_struct_0 @ X48)
% 1.93/2.11          | ~ (m1_pre_topc @ X48 @ X49)
% 1.93/2.11          | (m1_subset_1 @ X50 @ (u1_struct_0 @ X49))
% 1.93/2.11          | ~ (m1_subset_1 @ X50 @ (u1_struct_0 @ X48))
% 1.93/2.11          | ~ (l1_pre_topc @ X49)
% 1.93/2.11          | (v2_struct_0 @ X49))),
% 1.93/2.11      inference('cnf', [status(esa)], [t55_pre_topc])).
% 1.93/2.11  thf('63', plain,
% 1.93/2.11      (![X0 : $i]:
% 1.93/2.11         ((v2_struct_0 @ X0)
% 1.93/2.11          | ~ (l1_pre_topc @ X0)
% 1.93/2.11          | (m1_subset_1 @ sk_D @ (u1_struct_0 @ X0))
% 1.93/2.11          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 1.93/2.11          | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.93/2.11      inference('sup-', [status(thm)], ['61', '62'])).
% 1.93/2.11  thf('64', plain,
% 1.93/2.11      (((v2_struct_0 @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.11        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))
% 1.93/2.11        | ~ (l1_pre_topc @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ sk_C))),
% 1.93/2.11      inference('sup-', [status(thm)], ['60', '63'])).
% 1.93/2.11  thf('65', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf(dt_m1_pre_topc, axiom,
% 1.93/2.11    (![A:$i]:
% 1.93/2.11     ( ( l1_pre_topc @ A ) =>
% 1.93/2.11       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.93/2.11  thf('66', plain,
% 1.93/2.11      (![X46 : $i, X47 : $i]:
% 1.93/2.11         (~ (m1_pre_topc @ X46 @ X47)
% 1.93/2.11          | (l1_pre_topc @ X46)
% 1.93/2.11          | ~ (l1_pre_topc @ X47))),
% 1.93/2.11      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.93/2.11  thf('67', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 1.93/2.11      inference('sup-', [status(thm)], ['65', '66'])).
% 1.93/2.11  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('69', plain, ((l1_pre_topc @ sk_C)),
% 1.93/2.11      inference('demod', [status(thm)], ['67', '68'])).
% 1.93/2.11  thf('70', plain,
% 1.93/2.11      (((v2_struct_0 @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.11        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))
% 1.93/2.11        | (v2_struct_0 @ sk_C))),
% 1.93/2.11      inference('demod', [status(thm)], ['64', '69'])).
% 1.93/2.11  thf('71', plain,
% 1.93/2.11      (((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))
% 1.93/2.11        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.11        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_C))),
% 1.93/2.11      inference('simplify', [status(thm)], ['70'])).
% 1.93/2.11  thf('72', plain,
% 1.93/2.11      (![X55 : $i, X56 : $i, X57 : $i]:
% 1.93/2.11         (~ (m1_pre_topc @ X55 @ X56)
% 1.93/2.11          | (v2_struct_0 @ X55)
% 1.93/2.11          | ~ (l1_pre_topc @ X56)
% 1.93/2.11          | (v2_struct_0 @ X56)
% 1.93/2.11          | (v2_struct_0 @ X57)
% 1.93/2.11          | ~ (m1_pre_topc @ X57 @ X56)
% 1.93/2.11          | ~ (v2_struct_0 @ (k2_tsep_1 @ X56 @ X55 @ X57)))),
% 1.93/2.11      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 1.93/2.11  thf('73', plain,
% 1.93/2.11      (((v2_struct_0 @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.11        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))
% 1.93/2.11        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | ~ (l1_pre_topc @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 1.93/2.11      inference('sup-', [status(thm)], ['71', '72'])).
% 1.93/2.11  thf('74', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('76', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('77', plain,
% 1.93/2.11      (((v2_struct_0 @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.11        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))
% 1.93/2.11        | (v2_struct_0 @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_B))),
% 1.93/2.11      inference('demod', [status(thm)], ['73', '74', '75', '76'])).
% 1.93/2.11  thf('78', plain,
% 1.93/2.11      (((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))
% 1.93/2.11        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_C))),
% 1.93/2.11      inference('simplify', [status(thm)], ['77'])).
% 1.93/2.11  thf('79', plain,
% 1.93/2.11      (![X61 : $i, X62 : $i]:
% 1.93/2.11         (~ (m1_subset_1 @ X61 @ (u1_struct_0 @ sk_B))
% 1.93/2.11          | ((X61) != (sk_D))
% 1.93/2.11          | ~ (m1_subset_1 @ X62 @ (u1_struct_0 @ sk_C))
% 1.93/2.11          | ((X62) != (sk_D)))),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('80', plain,
% 1.93/2.11      ((![X62 : $i]:
% 1.93/2.11          (((X62) != (sk_D)) | ~ (m1_subset_1 @ X62 @ (u1_struct_0 @ sk_C))))
% 1.93/2.11         <= ((![X62 : $i]:
% 1.93/2.11                (((X62) != (sk_D))
% 1.93/2.11                 | ~ (m1_subset_1 @ X62 @ (u1_struct_0 @ sk_C)))))),
% 1.93/2.11      inference('split', [status(esa)], ['79'])).
% 1.93/2.11  thf('81', plain,
% 1.93/2.11      ((~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 1.93/2.11         <= ((![X62 : $i]:
% 1.93/2.11                (((X62) != (sk_D))
% 1.93/2.11                 | ~ (m1_subset_1 @ X62 @ (u1_struct_0 @ sk_C)))))),
% 1.93/2.11      inference('simplify', [status(thm)], ['80'])).
% 1.93/2.11  thf('82', plain,
% 1.93/2.11      (((v2_struct_0 @ sk_B)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_C)
% 1.93/2.11        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 1.93/2.11      inference('sup-', [status(thm)], ['1', '6'])).
% 1.93/2.11  thf(t17_xboole_1, axiom,
% 1.93/2.11    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.93/2.11  thf('83', plain,
% 1.93/2.11      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 1.93/2.11      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.93/2.11  thf('84', plain,
% 1.93/2.11      (![X0 : $i, X1 : $i]:
% 1.93/2.11         (~ (r1_tarski @ 
% 1.93/2.11             (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)) @ 
% 1.93/2.11             (u1_struct_0 @ X0))
% 1.93/2.11          | (v2_struct_0 @ sk_C)
% 1.93/2.11          | (v2_struct_0 @ sk_A)
% 1.93/2.11          | (v2_struct_0 @ sk_B)
% 1.93/2.11          | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.11          | ~ (v2_pre_topc @ X1)
% 1.93/2.11          | ~ (l1_pre_topc @ X1)
% 1.93/2.11          | ~ (m1_pre_topc @ X0 @ X1)
% 1.93/2.11          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 1.93/2.11          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X1))),
% 1.93/2.11      inference('sup-', [status(thm)], ['51', '52'])).
% 1.93/2.11  thf('85', plain,
% 1.93/2.11      (![X0 : $i]:
% 1.93/2.11         (~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 1.93/2.11          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B)
% 1.93/2.11          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.93/2.11          | ~ (l1_pre_topc @ X0)
% 1.93/2.11          | ~ (v2_pre_topc @ X0)
% 1.93/2.11          | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.11          | (v2_struct_0 @ sk_B)
% 1.93/2.11          | (v2_struct_0 @ sk_A)
% 1.93/2.11          | (v2_struct_0 @ sk_C))),
% 1.93/2.11      inference('sup-', [status(thm)], ['83', '84'])).
% 1.93/2.11  thf('86', plain,
% 1.93/2.11      (((v2_struct_0 @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | (v2_struct_0 @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.11        | ~ (v2_pre_topc @ sk_A)
% 1.93/2.11        | ~ (l1_pre_topc @ sk_A)
% 1.93/2.11        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 1.93/2.11        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B))),
% 1.93/2.11      inference('sup-', [status(thm)], ['82', '85'])).
% 1.93/2.11  thf('87', plain, ((v2_pre_topc @ sk_A)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('88', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('89', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('90', plain,
% 1.93/2.11      (((v2_struct_0 @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | (v2_struct_0 @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.11        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B))),
% 1.93/2.11      inference('demod', [status(thm)], ['86', '87', '88', '89'])).
% 1.93/2.11  thf('91', plain,
% 1.93/2.11      (((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B)
% 1.93/2.11        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_C))),
% 1.93/2.11      inference('simplify', [status(thm)], ['90'])).
% 1.93/2.11  thf('92', plain,
% 1.93/2.11      (![X0 : $i]:
% 1.93/2.11         ((v2_struct_0 @ X0)
% 1.93/2.11          | ~ (l1_pre_topc @ X0)
% 1.93/2.11          | (m1_subset_1 @ sk_D @ (u1_struct_0 @ X0))
% 1.93/2.11          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 1.93/2.11          | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.93/2.11      inference('sup-', [status(thm)], ['61', '62'])).
% 1.93/2.11  thf('93', plain,
% 1.93/2.11      (((v2_struct_0 @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.11        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))
% 1.93/2.11        | ~ (l1_pre_topc @ sk_B)
% 1.93/2.11        | (v2_struct_0 @ sk_B))),
% 1.93/2.11      inference('sup-', [status(thm)], ['91', '92'])).
% 1.93/2.11  thf('94', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('95', plain,
% 1.93/2.11      (![X46 : $i, X47 : $i]:
% 1.93/2.11         (~ (m1_pre_topc @ X46 @ X47)
% 1.93/2.11          | (l1_pre_topc @ X46)
% 1.93/2.11          | ~ (l1_pre_topc @ X47))),
% 1.93/2.11      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.93/2.11  thf('96', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 1.93/2.11      inference('sup-', [status(thm)], ['94', '95'])).
% 1.93/2.11  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('98', plain, ((l1_pre_topc @ sk_B)),
% 1.93/2.11      inference('demod', [status(thm)], ['96', '97'])).
% 1.93/2.11  thf('99', plain,
% 1.93/2.11      (((v2_struct_0 @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.11        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))
% 1.93/2.11        | (v2_struct_0 @ sk_B))),
% 1.93/2.11      inference('demod', [status(thm)], ['93', '98'])).
% 1.93/2.11  thf('100', plain,
% 1.93/2.11      (((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))
% 1.93/2.11        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.93/2.11        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_C))),
% 1.93/2.11      inference('simplify', [status(thm)], ['99'])).
% 1.93/2.11  thf('101', plain,
% 1.93/2.11      (![X55 : $i, X56 : $i, X57 : $i]:
% 1.93/2.11         (~ (m1_pre_topc @ X55 @ X56)
% 1.93/2.11          | (v2_struct_0 @ X55)
% 1.93/2.11          | ~ (l1_pre_topc @ X56)
% 1.93/2.11          | (v2_struct_0 @ X56)
% 1.93/2.11          | (v2_struct_0 @ X57)
% 1.93/2.11          | ~ (m1_pre_topc @ X57 @ X56)
% 1.93/2.11          | ~ (v2_struct_0 @ (k2_tsep_1 @ X56 @ X55 @ X57)))),
% 1.93/2.11      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 1.93/2.11  thf('102', plain,
% 1.93/2.11      (((v2_struct_0 @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.11        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))
% 1.93/2.11        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | ~ (l1_pre_topc @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 1.93/2.11      inference('sup-', [status(thm)], ['100', '101'])).
% 1.93/2.11  thf('103', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('104', plain, ((l1_pre_topc @ sk_A)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('105', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('106', plain,
% 1.93/2.11      (((v2_struct_0 @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.11        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))
% 1.93/2.11        | (v2_struct_0 @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_B))),
% 1.93/2.11      inference('demod', [status(thm)], ['102', '103', '104', '105'])).
% 1.93/2.11  thf('107', plain,
% 1.93/2.11      (((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))
% 1.93/2.11        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_C))),
% 1.93/2.11      inference('simplify', [status(thm)], ['106'])).
% 1.93/2.11  thf('108', plain,
% 1.93/2.11      ((![X61 : $i]:
% 1.93/2.11          (((X61) != (sk_D)) | ~ (m1_subset_1 @ X61 @ (u1_struct_0 @ sk_B))))
% 1.93/2.11         <= ((![X61 : $i]:
% 1.93/2.11                (((X61) != (sk_D))
% 1.93/2.11                 | ~ (m1_subset_1 @ X61 @ (u1_struct_0 @ sk_B)))))),
% 1.93/2.11      inference('split', [status(esa)], ['79'])).
% 1.93/2.11  thf('109', plain,
% 1.93/2.11      ((~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B)))
% 1.93/2.11         <= ((![X61 : $i]:
% 1.93/2.11                (((X61) != (sk_D))
% 1.93/2.11                 | ~ (m1_subset_1 @ X61 @ (u1_struct_0 @ sk_B)))))),
% 1.93/2.11      inference('simplify', [status(thm)], ['108'])).
% 1.93/2.11  thf('110', plain,
% 1.93/2.11      ((((v2_struct_0 @ sk_C)
% 1.93/2.11         | (v2_struct_0 @ sk_A)
% 1.93/2.11         | (v2_struct_0 @ sk_B)
% 1.93/2.11         | (r1_tsep_1 @ sk_B @ sk_C)))
% 1.93/2.11         <= ((![X61 : $i]:
% 1.93/2.11                (((X61) != (sk_D))
% 1.93/2.11                 | ~ (m1_subset_1 @ X61 @ (u1_struct_0 @ sk_B)))))),
% 1.93/2.11      inference('sup-', [status(thm)], ['107', '109'])).
% 1.93/2.11  thf('111', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('112', plain,
% 1.93/2.11      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C)))
% 1.93/2.11         <= ((![X61 : $i]:
% 1.93/2.11                (((X61) != (sk_D))
% 1.93/2.11                 | ~ (m1_subset_1 @ X61 @ (u1_struct_0 @ sk_B)))))),
% 1.93/2.11      inference('sup-', [status(thm)], ['110', '111'])).
% 1.93/2.11  thf('113', plain, (~ (v2_struct_0 @ sk_B)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('114', plain,
% 1.93/2.11      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A)))
% 1.93/2.11         <= ((![X61 : $i]:
% 1.93/2.11                (((X61) != (sk_D))
% 1.93/2.11                 | ~ (m1_subset_1 @ X61 @ (u1_struct_0 @ sk_B)))))),
% 1.93/2.11      inference('clc', [status(thm)], ['112', '113'])).
% 1.93/2.11  thf('115', plain, (~ (v2_struct_0 @ sk_C)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('116', plain,
% 1.93/2.11      (((v2_struct_0 @ sk_A))
% 1.93/2.11         <= ((![X61 : $i]:
% 1.93/2.11                (((X61) != (sk_D))
% 1.93/2.11                 | ~ (m1_subset_1 @ X61 @ (u1_struct_0 @ sk_B)))))),
% 1.93/2.11      inference('clc', [status(thm)], ['114', '115'])).
% 1.93/2.11  thf('117', plain, (~ (v2_struct_0 @ sk_A)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('118', plain,
% 1.93/2.11      (~
% 1.93/2.11       (![X61 : $i]:
% 1.93/2.11          (((X61) != (sk_D)) | ~ (m1_subset_1 @ X61 @ (u1_struct_0 @ sk_B))))),
% 1.93/2.11      inference('sup-', [status(thm)], ['116', '117'])).
% 1.93/2.11  thf('119', plain,
% 1.93/2.11      ((![X62 : $i]:
% 1.93/2.11          (((X62) != (sk_D)) | ~ (m1_subset_1 @ X62 @ (u1_struct_0 @ sk_C)))) | 
% 1.93/2.11       (![X61 : $i]:
% 1.93/2.11          (((X61) != (sk_D)) | ~ (m1_subset_1 @ X61 @ (u1_struct_0 @ sk_B))))),
% 1.93/2.11      inference('split', [status(esa)], ['79'])).
% 1.93/2.11  thf('120', plain,
% 1.93/2.11      ((![X62 : $i]:
% 1.93/2.11          (((X62) != (sk_D)) | ~ (m1_subset_1 @ X62 @ (u1_struct_0 @ sk_C))))),
% 1.93/2.11      inference('sat_resolution*', [status(thm)], ['118', '119'])).
% 1.93/2.11  thf('121', plain, (~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))),
% 1.93/2.11      inference('simpl_trail', [status(thm)], ['81', '120'])).
% 1.93/2.11  thf('122', plain,
% 1.93/2.11      (((v2_struct_0 @ sk_C)
% 1.93/2.11        | (v2_struct_0 @ sk_A)
% 1.93/2.11        | (v2_struct_0 @ sk_B)
% 1.93/2.11        | (r1_tsep_1 @ sk_B @ sk_C))),
% 1.93/2.11      inference('sup-', [status(thm)], ['78', '121'])).
% 1.93/2.11  thf('123', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('124', plain,
% 1.93/2.11      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 1.93/2.11      inference('sup-', [status(thm)], ['122', '123'])).
% 1.93/2.11  thf('125', plain, (~ (v2_struct_0 @ sk_B)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('126', plain, (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 1.93/2.11      inference('clc', [status(thm)], ['124', '125'])).
% 1.93/2.11  thf('127', plain, (~ (v2_struct_0 @ sk_C)),
% 1.93/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.11  thf('128', plain, ((v2_struct_0 @ sk_A)),
% 1.93/2.11      inference('clc', [status(thm)], ['126', '127'])).
% 1.93/2.11  thf('129', plain, ($false), inference('demod', [status(thm)], ['0', '128'])).
% 1.93/2.11  
% 1.93/2.11  % SZS output end Refutation
% 1.93/2.11  
% 1.97/2.12  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
