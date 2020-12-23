%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.brHKL1Fe4d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:14 EST 2020

% Result     : Theorem 1.95s
% Output     : Refutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 354 expanded)
%              Number of leaves         :   44 ( 115 expanded)
%              Depth                    :   36
%              Number of atoms          : 2016 (7699 expanded)
%              Number of equality atoms :   67 ( 316 expanded)
%              Maximal formula depth    :   23 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tsep_1_type,type,(
    k2_tsep_1: $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

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
    ! [X64: $i,X65: $i,X66: $i] :
      ( ~ ( m1_pre_topc @ X64 @ X65 )
      | ( v2_struct_0 @ X64 )
      | ~ ( l1_pre_topc @ X65 )
      | ( v2_struct_0 @ X65 )
      | ( v2_struct_0 @ X66 )
      | ~ ( m1_pre_topc @ X66 @ X65 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X65 @ X64 @ X66 ) @ X65 ) ) ),
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

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('13',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k6_enumset1 @ X22 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 )
      = ( k5_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(d6_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( I
        = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) )
    <=> ! [J: $i] :
          ( ( r2_hidden @ J @ I )
        <=> ~ ( ( J != H )
              & ( J != G )
              & ( J != F )
              & ( J != E )
              & ( J != D )
              & ( J != C )
              & ( J != B )
              & ( J != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [J: $i,H: $i,G: $i,F: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A )
    <=> ( ( J != A )
        & ( J != B )
        & ( J != C )
        & ( J != D )
        & ( J != E )
        & ( J != F )
        & ( J != G )
        & ( J != H ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( I
        = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) )
    <=> ! [J: $i] :
          ( ( r2_hidden @ J @ I )
        <=> ~ ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 )
      | ( r2_hidden @ X39 @ X48 )
      | ( X48
       != ( k6_enumset1 @ X47 @ X46 @ X45 @ X44 @ X43 @ X42 @ X41 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('15',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( r2_hidden @ X39 @ ( k6_enumset1 @ X47 @ X46 @ X45 @ X44 @ X43 @ X42 @ X41 @ X40 ) )
      | ( zip_tseitin_0 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6 ) ) ),
    inference('sup+',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( X30 != X31 )
      | ~ ( zip_tseitin_0 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('18',plain,(
    ! [X29: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ~ ( zip_tseitin_0 @ X31 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X29 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( r2_hidden @ X6 @ ( k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( r2_hidden @ X0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','23'])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('25',plain,(
    ! [X53: $i,X54: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X53 ) @ X54 )
      | ~ ( r2_hidden @ X54 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('27',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X51 @ X52 ) )
      = ( k3_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X64: $i,X65: $i,X66: $i] :
      ( ~ ( m1_pre_topc @ X64 @ X65 )
      | ( v2_struct_0 @ X64 )
      | ~ ( l1_pre_topc @ X65 )
      | ( v2_struct_0 @ X65 )
      | ( v2_struct_0 @ X66 )
      | ~ ( m1_pre_topc @ X66 @ X65 )
      | ( v1_pre_topc @ ( k2_tsep_1 @ X65 @ X64 @ X66 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,
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

thf('37',plain,(
    ! [X60: $i,X61: $i,X62: $i,X63: $i] :
      ( ( v2_struct_0 @ X60 )
      | ~ ( m1_pre_topc @ X60 @ X61 )
      | ( r1_tsep_1 @ X60 @ X62 )
      | ( v2_struct_0 @ X63 )
      | ~ ( v1_pre_topc @ X63 )
      | ~ ( m1_pre_topc @ X63 @ X61 )
      | ( X63
       != ( k2_tsep_1 @ X61 @ X60 @ X62 ) )
      | ( ( u1_struct_0 @ X63 )
        = ( k3_xboole_0 @ ( u1_struct_0 @ X60 ) @ ( u1_struct_0 @ X62 ) ) )
      | ~ ( m1_pre_topc @ X62 @ X61 )
      | ( v2_struct_0 @ X62 )
      | ~ ( l1_pre_topc @ X61 )
      | ( v2_struct_0 @ X61 ) ) ),
    inference(cnf,[status(esa)],[d5_tsep_1])).

thf('38',plain,(
    ! [X60: $i,X61: $i,X62: $i] :
      ( ( v2_struct_0 @ X61 )
      | ~ ( l1_pre_topc @ X61 )
      | ( v2_struct_0 @ X62 )
      | ~ ( m1_pre_topc @ X62 @ X61 )
      | ( ( u1_struct_0 @ ( k2_tsep_1 @ X61 @ X60 @ X62 ) )
        = ( k3_xboole_0 @ ( u1_struct_0 @ X60 ) @ ( u1_struct_0 @ X62 ) ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ X61 @ X60 @ X62 ) @ X61 )
      | ~ ( v1_pre_topc @ ( k2_tsep_1 @ X61 @ X60 @ X62 ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ X61 @ X60 @ X62 ) )
      | ( r1_tsep_1 @ X60 @ X62 )
      | ~ ( m1_pre_topc @ X60 @ X61 )
      | ( v2_struct_0 @ X60 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
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
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
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
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('44',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
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
    inference('sup-',[status(thm)],['35','44'])).

thf('46',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X64: $i,X65: $i,X66: $i] :
      ( ~ ( m1_pre_topc @ X64 @ X65 )
      | ( v2_struct_0 @ X64 )
      | ~ ( l1_pre_topc @ X65 )
      | ( v2_struct_0 @ X65 )
      | ( v2_struct_0 @ X66 )
      | ~ ( m1_pre_topc @ X66 @ X65 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X65 @ X64 @ X66 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('48',plain,
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
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['48','49','50','51'])).

thf('53',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['52'])).

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

thf('54',plain,(
    ! [X67: $i,X68: $i,X69: $i] :
      ( ~ ( m1_pre_topc @ X67 @ X68 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X67 ) @ ( u1_struct_0 @ X69 ) )
      | ( m1_pre_topc @ X67 @ X69 )
      | ~ ( m1_pre_topc @ X69 @ X68 )
      | ~ ( l1_pre_topc @ X68 )
      | ~ ( v2_pre_topc @ X68 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('55',plain,(
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
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
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
    inference('sup-',[status(thm)],['28','55'])).

thf('57',plain,
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
    inference('sup-',[status(thm)],['7','56'])).

thf('58',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('62',plain,
    ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
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

thf('64',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( v2_struct_0 @ X57 )
      | ~ ( m1_pre_topc @ X57 @ X58 )
      | ( m1_subset_1 @ X59 @ ( u1_struct_0 @ X58 ) )
      | ~ ( m1_subset_1 @ X59 @ ( u1_struct_0 @ X57 ) )
      | ~ ( l1_pre_topc @ X58 )
      | ( v2_struct_0 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t55_pre_topc])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
    | ~ ( l1_pre_topc @ sk_C )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('68',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( m1_pre_topc @ X55 @ X56 )
      | ( l1_pre_topc @ X55 )
      | ~ ( l1_pre_topc @ X56 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('69',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['66','71'])).

thf('73',plain,
    ( ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X64: $i,X65: $i,X66: $i] :
      ( ~ ( m1_pre_topc @ X64 @ X65 )
      | ( v2_struct_0 @ X64 )
      | ~ ( l1_pre_topc @ X65 )
      | ( v2_struct_0 @ X65 )
      | ( v2_struct_0 @ X66 )
      | ~ ( m1_pre_topc @ X66 @ X65 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X65 @ X64 @ X66 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('75',plain,
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
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['75','76','77','78'])).

thf('80',plain,
    ( ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X70: $i,X71: $i] :
      ( ~ ( m1_subset_1 @ X70 @ ( u1_struct_0 @ sk_B ) )
      | ( X70 != sk_D )
      | ~ ( m1_subset_1 @ X71 @ ( u1_struct_0 @ sk_C ) )
      | ( X71 != sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ! [X71: $i] :
        ( ( X71 != sk_D )
        | ~ ( m1_subset_1 @ X71 @ ( u1_struct_0 @ sk_C ) ) )
   <= ! [X71: $i] :
        ( ( X71 != sk_D )
        | ~ ( m1_subset_1 @ X71 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(split,[status(esa)],['81'])).

thf('83',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
   <= ! [X71: $i] :
        ( ( X71 != sk_D )
        | ~ ( m1_subset_1 @ X71 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('86',plain,(
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
    inference('sup-',[status(thm)],['53','54'])).

thf('87',plain,(
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
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
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
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['88','89','90','91'])).

thf('93',plain,
    ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( m1_pre_topc @ X55 @ X56 )
      | ( l1_pre_topc @ X55 )
      | ~ ( l1_pre_topc @ X56 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('98',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['95','100'])).

thf('102',plain,
    ( ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X64: $i,X65: $i,X66: $i] :
      ( ~ ( m1_pre_topc @ X64 @ X65 )
      | ( v2_struct_0 @ X64 )
      | ~ ( l1_pre_topc @ X65 )
      | ( v2_struct_0 @ X65 )
      | ( v2_struct_0 @ X66 )
      | ~ ( m1_pre_topc @ X66 @ X65 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X65 @ X64 @ X66 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('104',plain,
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
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['104','105','106','107'])).

thf('109',plain,
    ( ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,
    ( ! [X70: $i] :
        ( ( X70 != sk_D )
        | ~ ( m1_subset_1 @ X70 @ ( u1_struct_0 @ sk_B ) ) )
   <= ! [X70: $i] :
        ( ( X70 != sk_D )
        | ~ ( m1_subset_1 @ X70 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(split,[status(esa)],['81'])).

thf('111',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
   <= ! [X70: $i] :
        ( ( X70 != sk_D )
        | ~ ( m1_subset_1 @ X70 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C ) )
   <= ! [X70: $i] :
        ( ( X70 != sk_D )
        | ~ ( m1_subset_1 @ X70 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['109','111'])).

thf('113',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ! [X70: $i] :
        ( ( X70 != sk_D )
        | ~ ( m1_subset_1 @ X70 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X70: $i] :
        ( ( X70 != sk_D )
        | ~ ( m1_subset_1 @ X70 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['114','115'])).

thf('117',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ! [X70: $i] :
        ( ( X70 != sk_D )
        | ~ ( m1_subset_1 @ X70 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('119',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ~ ! [X70: $i] :
        ( ( X70 != sk_D )
        | ~ ( m1_subset_1 @ X70 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ! [X71: $i] :
        ( ( X71 != sk_D )
        | ~ ( m1_subset_1 @ X71 @ ( u1_struct_0 @ sk_C ) ) )
    | ! [X70: $i] :
        ( ( X70 != sk_D )
        | ~ ( m1_subset_1 @ X70 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(split,[status(esa)],['81'])).

thf('122',plain,(
    ! [X71: $i] :
      ( ( X71 != sk_D )
      | ~ ( m1_subset_1 @ X71 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sat_resolution*',[status(thm)],['120','121'])).

thf('123',plain,(
    ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['83','122'])).

thf('124',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['80','123'])).

thf('125',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['126','127'])).

thf('129',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['128','129'])).

thf('131',plain,(
    $false ),
    inference(demod,[status(thm)],['0','130'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.brHKL1Fe4d
% 0.13/0.37  % Computer   : n014.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 15:45:22 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 1.95/2.12  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.95/2.12  % Solved by: fo/fo7.sh
% 1.95/2.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.95/2.12  % done 1093 iterations in 1.637s
% 1.95/2.12  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.95/2.12  % SZS output start Refutation
% 1.95/2.12  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 1.95/2.12                                               $i > $i > $i > $o).
% 1.95/2.12  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.95/2.12  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 1.95/2.12  thf(sk_C_type, type, sk_C: $i).
% 1.95/2.12  thf(sk_A_type, type, sk_A: $i).
% 1.95/2.12  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.95/2.12  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 1.95/2.12  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.95/2.12  thf(sk_D_type, type, sk_D: $i).
% 1.95/2.12  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.95/2.12  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.95/2.12  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.95/2.12  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.95/2.12  thf(k2_tsep_1_type, type, k2_tsep_1: $i > $i > $i > $i).
% 1.95/2.12  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 1.95/2.12  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.95/2.12  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.95/2.12  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 1.95/2.12  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 1.95/2.12                                           $i > $i).
% 1.95/2.12  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.95/2.12  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.95/2.12  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 1.95/2.12  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.95/2.12  thf(sk_B_type, type, sk_B: $i).
% 1.95/2.12  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.95/2.12  thf(t17_tmap_1, conjecture,
% 1.95/2.12    (![A:$i]:
% 1.95/2.12     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.95/2.12       ( ![B:$i]:
% 1.95/2.12         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.95/2.12           ( ![C:$i]:
% 1.95/2.12             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.95/2.12               ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 1.95/2.12                 ( ![D:$i]:
% 1.95/2.12                   ( ( m1_subset_1 @
% 1.95/2.12                       D @ ( u1_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) =>
% 1.95/2.12                     ( ( ?[E:$i]:
% 1.95/2.12                         ( ( ( E ) = ( D ) ) & 
% 1.95/2.12                           ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) & 
% 1.95/2.12                       ( ?[E:$i]:
% 1.95/2.12                         ( ( ( E ) = ( D ) ) & 
% 1.95/2.12                           ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.95/2.12  thf(zf_stmt_0, negated_conjecture,
% 1.95/2.12    (~( ![A:$i]:
% 1.95/2.12        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.95/2.12            ( l1_pre_topc @ A ) ) =>
% 1.95/2.12          ( ![B:$i]:
% 1.95/2.12            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.95/2.12              ( ![C:$i]:
% 1.95/2.12                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.95/2.12                  ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 1.95/2.12                    ( ![D:$i]:
% 1.95/2.12                      ( ( m1_subset_1 @
% 1.95/2.12                          D @ ( u1_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) =>
% 1.95/2.12                        ( ( ?[E:$i]:
% 1.95/2.12                            ( ( ( E ) = ( D ) ) & 
% 1.95/2.12                              ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) & 
% 1.95/2.12                          ( ?[E:$i]:
% 1.95/2.12                            ( ( ( E ) = ( D ) ) & 
% 1.95/2.12                              ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.95/2.12    inference('cnf.neg', [status(esa)], [t17_tmap_1])).
% 1.95/2.12  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf(dt_k2_tsep_1, axiom,
% 1.95/2.12    (![A:$i,B:$i,C:$i]:
% 1.95/2.12     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 1.95/2.12         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 1.95/2.12         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.95/2.12       ( ( ~( v2_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) & 
% 1.95/2.12         ( v1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) ) & 
% 1.95/2.12         ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 1.95/2.12  thf('3', plain,
% 1.95/2.12      (![X64 : $i, X65 : $i, X66 : $i]:
% 1.95/2.12         (~ (m1_pre_topc @ X64 @ X65)
% 1.95/2.12          | (v2_struct_0 @ X64)
% 1.95/2.12          | ~ (l1_pre_topc @ X65)
% 1.95/2.12          | (v2_struct_0 @ X65)
% 1.95/2.12          | (v2_struct_0 @ X66)
% 1.95/2.12          | ~ (m1_pre_topc @ X66 @ X65)
% 1.95/2.12          | (m1_pre_topc @ (k2_tsep_1 @ X65 @ X64 @ X66) @ X65))),
% 1.95/2.12      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 1.95/2.12  thf('4', plain,
% 1.95/2.12      (![X0 : $i]:
% 1.95/2.12         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 1.95/2.12          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.12          | (v2_struct_0 @ X0)
% 1.95/2.12          | (v2_struct_0 @ sk_A)
% 1.95/2.12          | ~ (l1_pre_topc @ sk_A)
% 1.95/2.12          | (v2_struct_0 @ sk_B))),
% 1.95/2.12      inference('sup-', [status(thm)], ['2', '3'])).
% 1.95/2.12  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('6', plain,
% 1.95/2.12      (![X0 : $i]:
% 1.95/2.12         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 1.95/2.12          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.12          | (v2_struct_0 @ X0)
% 1.95/2.12          | (v2_struct_0 @ sk_A)
% 1.95/2.12          | (v2_struct_0 @ sk_B))),
% 1.95/2.12      inference('demod', [status(thm)], ['4', '5'])).
% 1.95/2.12  thf('7', plain,
% 1.95/2.12      (((v2_struct_0 @ sk_B)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_C)
% 1.95/2.12        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 1.95/2.12      inference('sup-', [status(thm)], ['1', '6'])).
% 1.95/2.12  thf(t70_enumset1, axiom,
% 1.95/2.12    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.95/2.12  thf('8', plain,
% 1.95/2.12      (![X2 : $i, X3 : $i]:
% 1.95/2.12         ((k1_enumset1 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 1.95/2.12      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.95/2.12  thf(t71_enumset1, axiom,
% 1.95/2.12    (![A:$i,B:$i,C:$i]:
% 1.95/2.12     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 1.95/2.12  thf('9', plain,
% 1.95/2.12      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.95/2.12         ((k2_enumset1 @ X4 @ X4 @ X5 @ X6) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 1.95/2.12      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.95/2.12  thf(t72_enumset1, axiom,
% 1.95/2.12    (![A:$i,B:$i,C:$i,D:$i]:
% 1.95/2.12     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 1.95/2.12  thf('10', plain,
% 1.95/2.12      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.95/2.12         ((k3_enumset1 @ X7 @ X7 @ X8 @ X9 @ X10)
% 1.95/2.12           = (k2_enumset1 @ X7 @ X8 @ X9 @ X10))),
% 1.95/2.12      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.95/2.12  thf(t73_enumset1, axiom,
% 1.95/2.12    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.95/2.12     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 1.95/2.12       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 1.95/2.12  thf('11', plain,
% 1.95/2.12      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 1.95/2.12         ((k4_enumset1 @ X11 @ X11 @ X12 @ X13 @ X14 @ X15)
% 1.95/2.12           = (k3_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15))),
% 1.95/2.12      inference('cnf', [status(esa)], [t73_enumset1])).
% 1.95/2.12  thf(t74_enumset1, axiom,
% 1.95/2.12    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.95/2.12     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 1.95/2.12       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 1.95/2.12  thf('12', plain,
% 1.95/2.12      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.95/2.12         ((k5_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21)
% 1.95/2.12           = (k4_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21))),
% 1.95/2.12      inference('cnf', [status(esa)], [t74_enumset1])).
% 1.95/2.12  thf(t75_enumset1, axiom,
% 1.95/2.12    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 1.95/2.12     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 1.95/2.12       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 1.95/2.12  thf('13', plain,
% 1.95/2.12      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.95/2.12         ((k6_enumset1 @ X22 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28)
% 1.95/2.12           = (k5_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28))),
% 1.95/2.12      inference('cnf', [status(esa)], [t75_enumset1])).
% 1.95/2.12  thf(d6_enumset1, axiom,
% 1.95/2.12    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 1.95/2.12     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 1.95/2.12       ( ![J:$i]:
% 1.95/2.12         ( ( r2_hidden @ J @ I ) <=>
% 1.95/2.12           ( ~( ( ( J ) != ( H ) ) & ( ( J ) != ( G ) ) & ( ( J ) != ( F ) ) & 
% 1.95/2.12                ( ( J ) != ( E ) ) & ( ( J ) != ( D ) ) & ( ( J ) != ( C ) ) & 
% 1.95/2.12                ( ( J ) != ( B ) ) & ( ( J ) != ( A ) ) ) ) ) ) ))).
% 1.95/2.12  thf(zf_stmt_1, type, zip_tseitin_0 :
% 1.95/2.12      $i > $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 1.95/2.12  thf(zf_stmt_2, axiom,
% 1.95/2.12    (![J:$i,H:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 1.95/2.12     ( ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) <=>
% 1.95/2.12       ( ( ( J ) != ( A ) ) & ( ( J ) != ( B ) ) & ( ( J ) != ( C ) ) & 
% 1.95/2.12         ( ( J ) != ( D ) ) & ( ( J ) != ( E ) ) & ( ( J ) != ( F ) ) & 
% 1.95/2.12         ( ( J ) != ( G ) ) & ( ( J ) != ( H ) ) ) ))).
% 1.95/2.12  thf(zf_stmt_3, axiom,
% 1.95/2.12    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 1.95/2.12     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 1.95/2.12       ( ![J:$i]:
% 1.95/2.12         ( ( r2_hidden @ J @ I ) <=>
% 1.95/2.12           ( ~( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 1.95/2.12  thf('14', plain,
% 1.95/2.12      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, 
% 1.95/2.12         X46 : $i, X47 : $i, X48 : $i]:
% 1.95/2.12         ((zip_tseitin_0 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47)
% 1.95/2.12          | (r2_hidden @ X39 @ X48)
% 1.95/2.12          | ((X48)
% 1.95/2.12              != (k6_enumset1 @ X47 @ X46 @ X45 @ X44 @ X43 @ X42 @ X41 @ X40)))),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.95/2.12  thf('15', plain,
% 1.95/2.12      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, 
% 1.95/2.12         X46 : $i, X47 : $i]:
% 1.95/2.12         ((r2_hidden @ X39 @ 
% 1.95/2.12           (k6_enumset1 @ X47 @ X46 @ X45 @ X44 @ X43 @ X42 @ X41 @ X40))
% 1.95/2.12          | (zip_tseitin_0 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ 
% 1.95/2.12             X47))),
% 1.95/2.12      inference('simplify', [status(thm)], ['14'])).
% 1.95/2.12  thf('16', plain,
% 1.95/2.12      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 1.95/2.12         ((r2_hidden @ X7 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 1.95/2.12          | (zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6))),
% 1.95/2.12      inference('sup+', [status(thm)], ['13', '15'])).
% 1.95/2.12  thf('17', plain,
% 1.95/2.12      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, 
% 1.95/2.12         X36 : $i, X37 : $i]:
% 1.95/2.12         (((X30) != (X31))
% 1.95/2.12          | ~ (zip_tseitin_0 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ 
% 1.95/2.12               X29))),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.95/2.12  thf('18', plain,
% 1.95/2.12      (![X29 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, 
% 1.95/2.12         X37 : $i]:
% 1.95/2.12         ~ (zip_tseitin_0 @ X31 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X29)),
% 1.95/2.12      inference('simplify', [status(thm)], ['17'])).
% 1.95/2.12  thf('19', plain,
% 1.95/2.12      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.95/2.12         (r2_hidden @ X6 @ (k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6))),
% 1.95/2.12      inference('sup-', [status(thm)], ['16', '18'])).
% 1.95/2.12  thf('20', plain,
% 1.95/2.12      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.95/2.12         (r2_hidden @ X0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 1.95/2.12      inference('sup+', [status(thm)], ['12', '19'])).
% 1.95/2.12  thf('21', plain,
% 1.95/2.12      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.95/2.12         (r2_hidden @ X0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 1.95/2.12      inference('sup+', [status(thm)], ['11', '20'])).
% 1.95/2.12  thf('22', plain,
% 1.95/2.12      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.95/2.12         (r2_hidden @ X0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 1.95/2.12      inference('sup+', [status(thm)], ['10', '21'])).
% 1.95/2.12  thf('23', plain,
% 1.95/2.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.95/2.12         (r2_hidden @ X0 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.95/2.12      inference('sup+', [status(thm)], ['9', '22'])).
% 1.95/2.12  thf('24', plain,
% 1.95/2.12      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 1.95/2.12      inference('sup+', [status(thm)], ['8', '23'])).
% 1.95/2.12  thf(t4_setfam_1, axiom,
% 1.95/2.12    (![A:$i,B:$i]:
% 1.95/2.12     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 1.95/2.12  thf('25', plain,
% 1.95/2.12      (![X53 : $i, X54 : $i]:
% 1.95/2.12         ((r1_tarski @ (k1_setfam_1 @ X53) @ X54) | ~ (r2_hidden @ X54 @ X53))),
% 1.95/2.12      inference('cnf', [status(esa)], [t4_setfam_1])).
% 1.95/2.12  thf('26', plain,
% 1.95/2.12      (![X0 : $i, X1 : $i]:
% 1.95/2.12         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 1.95/2.12      inference('sup-', [status(thm)], ['24', '25'])).
% 1.95/2.12  thf(t12_setfam_1, axiom,
% 1.95/2.12    (![A:$i,B:$i]:
% 1.95/2.12     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.95/2.12  thf('27', plain,
% 1.95/2.12      (![X51 : $i, X52 : $i]:
% 1.95/2.12         ((k1_setfam_1 @ (k2_tarski @ X51 @ X52)) = (k3_xboole_0 @ X51 @ X52))),
% 1.95/2.12      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.95/2.12  thf('28', plain,
% 1.95/2.12      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.95/2.12      inference('demod', [status(thm)], ['26', '27'])).
% 1.95/2.12  thf('29', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('30', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('31', plain,
% 1.95/2.12      (![X64 : $i, X65 : $i, X66 : $i]:
% 1.95/2.12         (~ (m1_pre_topc @ X64 @ X65)
% 1.95/2.12          | (v2_struct_0 @ X64)
% 1.95/2.12          | ~ (l1_pre_topc @ X65)
% 1.95/2.12          | (v2_struct_0 @ X65)
% 1.95/2.12          | (v2_struct_0 @ X66)
% 1.95/2.12          | ~ (m1_pre_topc @ X66 @ X65)
% 1.95/2.12          | (v1_pre_topc @ (k2_tsep_1 @ X65 @ X64 @ X66)))),
% 1.95/2.12      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 1.95/2.12  thf('32', plain,
% 1.95/2.12      (![X0 : $i]:
% 1.95/2.12         ((v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 1.95/2.12          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.12          | (v2_struct_0 @ X0)
% 1.95/2.12          | (v2_struct_0 @ sk_A)
% 1.95/2.12          | ~ (l1_pre_topc @ sk_A)
% 1.95/2.12          | (v2_struct_0 @ sk_B))),
% 1.95/2.12      inference('sup-', [status(thm)], ['30', '31'])).
% 1.95/2.12  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('34', plain,
% 1.95/2.12      (![X0 : $i]:
% 1.95/2.12         ((v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 1.95/2.12          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.95/2.12          | (v2_struct_0 @ X0)
% 1.95/2.12          | (v2_struct_0 @ sk_A)
% 1.95/2.12          | (v2_struct_0 @ sk_B))),
% 1.95/2.12      inference('demod', [status(thm)], ['32', '33'])).
% 1.95/2.12  thf('35', plain,
% 1.95/2.12      (((v2_struct_0 @ sk_B)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_C)
% 1.95/2.12        | (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.95/2.12      inference('sup-', [status(thm)], ['29', '34'])).
% 1.95/2.12  thf('36', plain,
% 1.95/2.12      (((v2_struct_0 @ sk_B)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_C)
% 1.95/2.12        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 1.95/2.12      inference('sup-', [status(thm)], ['1', '6'])).
% 1.95/2.12  thf(d5_tsep_1, axiom,
% 1.95/2.12    (![A:$i]:
% 1.95/2.12     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 1.95/2.12       ( ![B:$i]:
% 1.95/2.12         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.95/2.12           ( ![C:$i]:
% 1.95/2.12             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.95/2.12               ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 1.95/2.12                 ( ![D:$i]:
% 1.95/2.12                   ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 1.95/2.12                       ( m1_pre_topc @ D @ A ) ) =>
% 1.95/2.12                     ( ( ( D ) = ( k2_tsep_1 @ A @ B @ C ) ) <=>
% 1.95/2.12                       ( ( u1_struct_0 @ D ) =
% 1.95/2.12                         ( k3_xboole_0 @
% 1.95/2.12                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.95/2.12  thf('37', plain,
% 1.95/2.12      (![X60 : $i, X61 : $i, X62 : $i, X63 : $i]:
% 1.95/2.12         ((v2_struct_0 @ X60)
% 1.95/2.12          | ~ (m1_pre_topc @ X60 @ X61)
% 1.95/2.12          | (r1_tsep_1 @ X60 @ X62)
% 1.95/2.12          | (v2_struct_0 @ X63)
% 1.95/2.12          | ~ (v1_pre_topc @ X63)
% 1.95/2.12          | ~ (m1_pre_topc @ X63 @ X61)
% 1.95/2.12          | ((X63) != (k2_tsep_1 @ X61 @ X60 @ X62))
% 1.95/2.12          | ((u1_struct_0 @ X63)
% 1.95/2.12              = (k3_xboole_0 @ (u1_struct_0 @ X60) @ (u1_struct_0 @ X62)))
% 1.95/2.12          | ~ (m1_pre_topc @ X62 @ X61)
% 1.95/2.12          | (v2_struct_0 @ X62)
% 1.95/2.12          | ~ (l1_pre_topc @ X61)
% 1.95/2.12          | (v2_struct_0 @ X61))),
% 1.95/2.12      inference('cnf', [status(esa)], [d5_tsep_1])).
% 1.95/2.12  thf('38', plain,
% 1.95/2.12      (![X60 : $i, X61 : $i, X62 : $i]:
% 1.95/2.12         ((v2_struct_0 @ X61)
% 1.95/2.12          | ~ (l1_pre_topc @ X61)
% 1.95/2.12          | (v2_struct_0 @ X62)
% 1.95/2.12          | ~ (m1_pre_topc @ X62 @ X61)
% 1.95/2.12          | ((u1_struct_0 @ (k2_tsep_1 @ X61 @ X60 @ X62))
% 1.95/2.12              = (k3_xboole_0 @ (u1_struct_0 @ X60) @ (u1_struct_0 @ X62)))
% 1.95/2.12          | ~ (m1_pre_topc @ (k2_tsep_1 @ X61 @ X60 @ X62) @ X61)
% 1.95/2.12          | ~ (v1_pre_topc @ (k2_tsep_1 @ X61 @ X60 @ X62))
% 1.95/2.12          | (v2_struct_0 @ (k2_tsep_1 @ X61 @ X60 @ X62))
% 1.95/2.12          | (r1_tsep_1 @ X60 @ X62)
% 1.95/2.12          | ~ (m1_pre_topc @ X60 @ X61)
% 1.95/2.12          | (v2_struct_0 @ X60))),
% 1.95/2.12      inference('simplify', [status(thm)], ['37'])).
% 1.95/2.12  thf('39', plain,
% 1.95/2.12      (((v2_struct_0 @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_B)
% 1.95/2.12        | (v2_struct_0 @ sk_B)
% 1.95/2.12        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 1.95/2.12        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.95/2.12        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.95/2.12        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.95/2.12            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.95/2.12        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_C)
% 1.95/2.12        | ~ (l1_pre_topc @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_A))),
% 1.95/2.12      inference('sup-', [status(thm)], ['36', '38'])).
% 1.95/2.12  thf('40', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('41', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('43', plain,
% 1.95/2.12      (((v2_struct_0 @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_B)
% 1.95/2.12        | (v2_struct_0 @ sk_B)
% 1.95/2.12        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.95/2.12        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.95/2.12        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.95/2.12            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.95/2.12        | (v2_struct_0 @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_A))),
% 1.95/2.12      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 1.95/2.12  thf('44', plain,
% 1.95/2.12      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.95/2.12          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.95/2.12        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.95/2.12        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.95/2.12        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_B)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_C))),
% 1.95/2.12      inference('simplify', [status(thm)], ['43'])).
% 1.95/2.12  thf('45', plain,
% 1.95/2.12      (((v2_struct_0 @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_B)
% 1.95/2.12        | (v2_struct_0 @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_B)
% 1.95/2.12        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.95/2.12        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.95/2.12            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))),
% 1.95/2.12      inference('sup-', [status(thm)], ['35', '44'])).
% 1.95/2.12  thf('46', plain,
% 1.95/2.12      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.95/2.12          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.95/2.12        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.95/2.12        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_B)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_C))),
% 1.95/2.12      inference('simplify', [status(thm)], ['45'])).
% 1.95/2.12  thf('47', plain,
% 1.95/2.12      (![X64 : $i, X65 : $i, X66 : $i]:
% 1.95/2.12         (~ (m1_pre_topc @ X64 @ X65)
% 1.95/2.12          | (v2_struct_0 @ X64)
% 1.95/2.12          | ~ (l1_pre_topc @ X65)
% 1.95/2.12          | (v2_struct_0 @ X65)
% 1.95/2.12          | (v2_struct_0 @ X66)
% 1.95/2.12          | ~ (m1_pre_topc @ X66 @ X65)
% 1.95/2.12          | ~ (v2_struct_0 @ (k2_tsep_1 @ X65 @ X64 @ X66)))),
% 1.95/2.12      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 1.95/2.12  thf('48', plain,
% 1.95/2.12      (((v2_struct_0 @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_B)
% 1.95/2.12        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.95/2.12        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.95/2.12            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.95/2.12        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | ~ (l1_pre_topc @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_B)
% 1.95/2.12        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 1.95/2.12      inference('sup-', [status(thm)], ['46', '47'])).
% 1.95/2.12  thf('49', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('51', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('52', plain,
% 1.95/2.12      (((v2_struct_0 @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_B)
% 1.95/2.12        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.95/2.12        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.95/2.12            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.95/2.12        | (v2_struct_0 @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_B))),
% 1.95/2.12      inference('demod', [status(thm)], ['48', '49', '50', '51'])).
% 1.95/2.12  thf('53', plain,
% 1.95/2.12      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.95/2.12          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.95/2.12        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_B)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_C))),
% 1.95/2.12      inference('simplify', [status(thm)], ['52'])).
% 1.95/2.12  thf(t4_tsep_1, axiom,
% 1.95/2.12    (![A:$i]:
% 1.95/2.12     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.95/2.12       ( ![B:$i]:
% 1.95/2.12         ( ( m1_pre_topc @ B @ A ) =>
% 1.95/2.12           ( ![C:$i]:
% 1.95/2.12             ( ( m1_pre_topc @ C @ A ) =>
% 1.95/2.12               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 1.95/2.12                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 1.95/2.12  thf('54', plain,
% 1.95/2.12      (![X67 : $i, X68 : $i, X69 : $i]:
% 1.95/2.12         (~ (m1_pre_topc @ X67 @ X68)
% 1.95/2.12          | ~ (r1_tarski @ (u1_struct_0 @ X67) @ (u1_struct_0 @ X69))
% 1.95/2.12          | (m1_pre_topc @ X67 @ X69)
% 1.95/2.12          | ~ (m1_pre_topc @ X69 @ X68)
% 1.95/2.12          | ~ (l1_pre_topc @ X68)
% 1.95/2.12          | ~ (v2_pre_topc @ X68))),
% 1.95/2.12      inference('cnf', [status(esa)], [t4_tsep_1])).
% 1.95/2.12  thf('55', plain,
% 1.95/2.12      (![X0 : $i, X1 : $i]:
% 1.95/2.12         (~ (r1_tarski @ 
% 1.95/2.12             (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)) @ 
% 1.95/2.12             (u1_struct_0 @ X0))
% 1.95/2.12          | (v2_struct_0 @ sk_C)
% 1.95/2.12          | (v2_struct_0 @ sk_A)
% 1.95/2.12          | (v2_struct_0 @ sk_B)
% 1.95/2.12          | (r1_tsep_1 @ sk_B @ sk_C)
% 1.95/2.12          | ~ (v2_pre_topc @ X1)
% 1.95/2.12          | ~ (l1_pre_topc @ X1)
% 1.95/2.12          | ~ (m1_pre_topc @ X0 @ X1)
% 1.95/2.12          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 1.95/2.12          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X1))),
% 1.95/2.12      inference('sup-', [status(thm)], ['53', '54'])).
% 1.95/2.12  thf('56', plain,
% 1.95/2.12      (![X0 : $i]:
% 1.95/2.12         (~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 1.95/2.12          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C)
% 1.95/2.12          | ~ (m1_pre_topc @ sk_C @ X0)
% 1.95/2.12          | ~ (l1_pre_topc @ X0)
% 1.95/2.12          | ~ (v2_pre_topc @ X0)
% 1.95/2.12          | (r1_tsep_1 @ sk_B @ sk_C)
% 1.95/2.12          | (v2_struct_0 @ sk_B)
% 1.95/2.12          | (v2_struct_0 @ sk_A)
% 1.95/2.12          | (v2_struct_0 @ sk_C))),
% 1.95/2.12      inference('sup-', [status(thm)], ['28', '55'])).
% 1.95/2.12  thf('57', plain,
% 1.95/2.12      (((v2_struct_0 @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_B)
% 1.95/2.12        | (v2_struct_0 @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_B)
% 1.95/2.12        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.95/2.12        | ~ (v2_pre_topc @ sk_A)
% 1.95/2.12        | ~ (l1_pre_topc @ sk_A)
% 1.95/2.12        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.95/2.12        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C))),
% 1.95/2.12      inference('sup-', [status(thm)], ['7', '56'])).
% 1.95/2.12  thf('58', plain, ((v2_pre_topc @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('60', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('61', plain,
% 1.95/2.12      (((v2_struct_0 @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_B)
% 1.95/2.12        | (v2_struct_0 @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_B)
% 1.95/2.12        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.95/2.12        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C))),
% 1.95/2.12      inference('demod', [status(thm)], ['57', '58', '59', '60'])).
% 1.95/2.12  thf('62', plain,
% 1.95/2.12      (((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C)
% 1.95/2.12        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_B)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_C))),
% 1.95/2.12      inference('simplify', [status(thm)], ['61'])).
% 1.95/2.12  thf('63', plain,
% 1.95/2.12      ((m1_subset_1 @ sk_D @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf(t55_pre_topc, axiom,
% 1.95/2.12    (![A:$i]:
% 1.95/2.12     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 1.95/2.12       ( ![B:$i]:
% 1.95/2.12         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.95/2.12           ( ![C:$i]:
% 1.95/2.12             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 1.95/2.12               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 1.95/2.12  thf('64', plain,
% 1.95/2.12      (![X57 : $i, X58 : $i, X59 : $i]:
% 1.95/2.12         ((v2_struct_0 @ X57)
% 1.95/2.12          | ~ (m1_pre_topc @ X57 @ X58)
% 1.95/2.12          | (m1_subset_1 @ X59 @ (u1_struct_0 @ X58))
% 1.95/2.12          | ~ (m1_subset_1 @ X59 @ (u1_struct_0 @ X57))
% 1.95/2.12          | ~ (l1_pre_topc @ X58)
% 1.95/2.12          | (v2_struct_0 @ X58))),
% 1.95/2.12      inference('cnf', [status(esa)], [t55_pre_topc])).
% 1.95/2.12  thf('65', plain,
% 1.95/2.12      (![X0 : $i]:
% 1.95/2.12         ((v2_struct_0 @ X0)
% 1.95/2.12          | ~ (l1_pre_topc @ X0)
% 1.95/2.12          | (m1_subset_1 @ sk_D @ (u1_struct_0 @ X0))
% 1.95/2.12          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 1.95/2.12          | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.95/2.12      inference('sup-', [status(thm)], ['63', '64'])).
% 1.95/2.12  thf('66', plain,
% 1.95/2.12      (((v2_struct_0 @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_B)
% 1.95/2.12        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.95/2.12        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))
% 1.95/2.12        | ~ (l1_pre_topc @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_C))),
% 1.95/2.12      inference('sup-', [status(thm)], ['62', '65'])).
% 1.95/2.12  thf('67', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf(dt_m1_pre_topc, axiom,
% 1.95/2.12    (![A:$i]:
% 1.95/2.12     ( ( l1_pre_topc @ A ) =>
% 1.95/2.12       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.95/2.12  thf('68', plain,
% 1.95/2.12      (![X55 : $i, X56 : $i]:
% 1.95/2.12         (~ (m1_pre_topc @ X55 @ X56)
% 1.95/2.12          | (l1_pre_topc @ X55)
% 1.95/2.12          | ~ (l1_pre_topc @ X56))),
% 1.95/2.12      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.95/2.12  thf('69', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 1.95/2.12      inference('sup-', [status(thm)], ['67', '68'])).
% 1.95/2.12  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('71', plain, ((l1_pre_topc @ sk_C)),
% 1.95/2.12      inference('demod', [status(thm)], ['69', '70'])).
% 1.95/2.12  thf('72', plain,
% 1.95/2.12      (((v2_struct_0 @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_B)
% 1.95/2.12        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.95/2.12        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))
% 1.95/2.12        | (v2_struct_0 @ sk_C))),
% 1.95/2.12      inference('demod', [status(thm)], ['66', '71'])).
% 1.95/2.12  thf('73', plain,
% 1.95/2.12      (((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))
% 1.95/2.12        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.95/2.12        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_B)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_C))),
% 1.95/2.12      inference('simplify', [status(thm)], ['72'])).
% 1.95/2.12  thf('74', plain,
% 1.95/2.12      (![X64 : $i, X65 : $i, X66 : $i]:
% 1.95/2.12         (~ (m1_pre_topc @ X64 @ X65)
% 1.95/2.12          | (v2_struct_0 @ X64)
% 1.95/2.12          | ~ (l1_pre_topc @ X65)
% 1.95/2.12          | (v2_struct_0 @ X65)
% 1.95/2.12          | (v2_struct_0 @ X66)
% 1.95/2.12          | ~ (m1_pre_topc @ X66 @ X65)
% 1.95/2.12          | ~ (v2_struct_0 @ (k2_tsep_1 @ X65 @ X64 @ X66)))),
% 1.95/2.12      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 1.95/2.12  thf('75', plain,
% 1.95/2.12      (((v2_struct_0 @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_B)
% 1.95/2.12        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.95/2.12        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))
% 1.95/2.12        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | ~ (l1_pre_topc @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_B)
% 1.95/2.12        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 1.95/2.12      inference('sup-', [status(thm)], ['73', '74'])).
% 1.95/2.12  thf('76', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('78', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('79', plain,
% 1.95/2.12      (((v2_struct_0 @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_B)
% 1.95/2.12        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.95/2.12        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))
% 1.95/2.12        | (v2_struct_0 @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_B))),
% 1.95/2.12      inference('demod', [status(thm)], ['75', '76', '77', '78'])).
% 1.95/2.12  thf('80', plain,
% 1.95/2.12      (((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))
% 1.95/2.12        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_B)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_C))),
% 1.95/2.12      inference('simplify', [status(thm)], ['79'])).
% 1.95/2.12  thf('81', plain,
% 1.95/2.12      (![X70 : $i, X71 : $i]:
% 1.95/2.12         (~ (m1_subset_1 @ X70 @ (u1_struct_0 @ sk_B))
% 1.95/2.12          | ((X70) != (sk_D))
% 1.95/2.12          | ~ (m1_subset_1 @ X71 @ (u1_struct_0 @ sk_C))
% 1.95/2.12          | ((X71) != (sk_D)))),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('82', plain,
% 1.95/2.12      ((![X71 : $i]:
% 1.95/2.12          (((X71) != (sk_D)) | ~ (m1_subset_1 @ X71 @ (u1_struct_0 @ sk_C))))
% 1.95/2.12         <= ((![X71 : $i]:
% 1.95/2.12                (((X71) != (sk_D))
% 1.95/2.12                 | ~ (m1_subset_1 @ X71 @ (u1_struct_0 @ sk_C)))))),
% 1.95/2.12      inference('split', [status(esa)], ['81'])).
% 1.95/2.12  thf('83', plain,
% 1.95/2.12      ((~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 1.95/2.12         <= ((![X71 : $i]:
% 1.95/2.12                (((X71) != (sk_D))
% 1.95/2.12                 | ~ (m1_subset_1 @ X71 @ (u1_struct_0 @ sk_C)))))),
% 1.95/2.12      inference('simplify', [status(thm)], ['82'])).
% 1.95/2.12  thf('84', plain,
% 1.95/2.12      (((v2_struct_0 @ sk_B)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_C)
% 1.95/2.12        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 1.95/2.12      inference('sup-', [status(thm)], ['1', '6'])).
% 1.95/2.12  thf(t17_xboole_1, axiom,
% 1.95/2.12    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.95/2.12  thf('85', plain,
% 1.95/2.12      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 1.95/2.12      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.95/2.12  thf('86', plain,
% 1.95/2.12      (![X0 : $i, X1 : $i]:
% 1.95/2.12         (~ (r1_tarski @ 
% 1.95/2.12             (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)) @ 
% 1.95/2.12             (u1_struct_0 @ X0))
% 1.95/2.12          | (v2_struct_0 @ sk_C)
% 1.95/2.12          | (v2_struct_0 @ sk_A)
% 1.95/2.12          | (v2_struct_0 @ sk_B)
% 1.95/2.12          | (r1_tsep_1 @ sk_B @ sk_C)
% 1.95/2.12          | ~ (v2_pre_topc @ X1)
% 1.95/2.12          | ~ (l1_pre_topc @ X1)
% 1.95/2.12          | ~ (m1_pre_topc @ X0 @ X1)
% 1.95/2.12          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 1.95/2.12          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X1))),
% 1.95/2.12      inference('sup-', [status(thm)], ['53', '54'])).
% 1.95/2.12  thf('87', plain,
% 1.95/2.12      (![X0 : $i]:
% 1.95/2.12         (~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 1.95/2.12          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B)
% 1.95/2.12          | ~ (m1_pre_topc @ sk_B @ X0)
% 1.95/2.12          | ~ (l1_pre_topc @ X0)
% 1.95/2.12          | ~ (v2_pre_topc @ X0)
% 1.95/2.12          | (r1_tsep_1 @ sk_B @ sk_C)
% 1.95/2.12          | (v2_struct_0 @ sk_B)
% 1.95/2.12          | (v2_struct_0 @ sk_A)
% 1.95/2.12          | (v2_struct_0 @ sk_C))),
% 1.95/2.12      inference('sup-', [status(thm)], ['85', '86'])).
% 1.95/2.12  thf('88', plain,
% 1.95/2.12      (((v2_struct_0 @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_B)
% 1.95/2.12        | (v2_struct_0 @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_B)
% 1.95/2.12        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.95/2.12        | ~ (v2_pre_topc @ sk_A)
% 1.95/2.12        | ~ (l1_pre_topc @ sk_A)
% 1.95/2.12        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 1.95/2.12        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B))),
% 1.95/2.12      inference('sup-', [status(thm)], ['84', '87'])).
% 1.95/2.12  thf('89', plain, ((v2_pre_topc @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('91', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('92', plain,
% 1.95/2.12      (((v2_struct_0 @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_B)
% 1.95/2.12        | (v2_struct_0 @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_B)
% 1.95/2.12        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.95/2.12        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B))),
% 1.95/2.12      inference('demod', [status(thm)], ['88', '89', '90', '91'])).
% 1.95/2.12  thf('93', plain,
% 1.95/2.12      (((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B)
% 1.95/2.12        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_B)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_C))),
% 1.95/2.12      inference('simplify', [status(thm)], ['92'])).
% 1.95/2.12  thf('94', plain,
% 1.95/2.12      (![X0 : $i]:
% 1.95/2.12         ((v2_struct_0 @ X0)
% 1.95/2.12          | ~ (l1_pre_topc @ X0)
% 1.95/2.12          | (m1_subset_1 @ sk_D @ (u1_struct_0 @ X0))
% 1.95/2.12          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 1.95/2.12          | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.95/2.12      inference('sup-', [status(thm)], ['63', '64'])).
% 1.95/2.12  thf('95', plain,
% 1.95/2.12      (((v2_struct_0 @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_B)
% 1.95/2.12        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.95/2.12        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))
% 1.95/2.12        | ~ (l1_pre_topc @ sk_B)
% 1.95/2.12        | (v2_struct_0 @ sk_B))),
% 1.95/2.12      inference('sup-', [status(thm)], ['93', '94'])).
% 1.95/2.12  thf('96', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('97', plain,
% 1.95/2.12      (![X55 : $i, X56 : $i]:
% 1.95/2.12         (~ (m1_pre_topc @ X55 @ X56)
% 1.95/2.12          | (l1_pre_topc @ X55)
% 1.95/2.12          | ~ (l1_pre_topc @ X56))),
% 1.95/2.12      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.95/2.12  thf('98', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 1.95/2.12      inference('sup-', [status(thm)], ['96', '97'])).
% 1.95/2.12  thf('99', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('100', plain, ((l1_pre_topc @ sk_B)),
% 1.95/2.12      inference('demod', [status(thm)], ['98', '99'])).
% 1.95/2.12  thf('101', plain,
% 1.95/2.12      (((v2_struct_0 @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_B)
% 1.95/2.12        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.95/2.12        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))
% 1.95/2.12        | (v2_struct_0 @ sk_B))),
% 1.95/2.12      inference('demod', [status(thm)], ['95', '100'])).
% 1.95/2.12  thf('102', plain,
% 1.95/2.12      (((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))
% 1.95/2.12        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.95/2.12        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_B)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_C))),
% 1.95/2.12      inference('simplify', [status(thm)], ['101'])).
% 1.95/2.12  thf('103', plain,
% 1.95/2.12      (![X64 : $i, X65 : $i, X66 : $i]:
% 1.95/2.12         (~ (m1_pre_topc @ X64 @ X65)
% 1.95/2.12          | (v2_struct_0 @ X64)
% 1.95/2.12          | ~ (l1_pre_topc @ X65)
% 1.95/2.12          | (v2_struct_0 @ X65)
% 1.95/2.12          | (v2_struct_0 @ X66)
% 1.95/2.12          | ~ (m1_pre_topc @ X66 @ X65)
% 1.95/2.12          | ~ (v2_struct_0 @ (k2_tsep_1 @ X65 @ X64 @ X66)))),
% 1.95/2.12      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 1.95/2.12  thf('104', plain,
% 1.95/2.12      (((v2_struct_0 @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_B)
% 1.95/2.12        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.95/2.12        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))
% 1.95/2.12        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | ~ (l1_pre_topc @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_B)
% 1.95/2.12        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 1.95/2.12      inference('sup-', [status(thm)], ['102', '103'])).
% 1.95/2.12  thf('105', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('106', plain, ((l1_pre_topc @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('107', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('108', plain,
% 1.95/2.12      (((v2_struct_0 @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_B)
% 1.95/2.12        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.95/2.12        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))
% 1.95/2.12        | (v2_struct_0 @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_B))),
% 1.95/2.12      inference('demod', [status(thm)], ['104', '105', '106', '107'])).
% 1.95/2.12  thf('109', plain,
% 1.95/2.12      (((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))
% 1.95/2.12        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_B)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_C))),
% 1.95/2.12      inference('simplify', [status(thm)], ['108'])).
% 1.95/2.12  thf('110', plain,
% 1.95/2.12      ((![X70 : $i]:
% 1.95/2.12          (((X70) != (sk_D)) | ~ (m1_subset_1 @ X70 @ (u1_struct_0 @ sk_B))))
% 1.95/2.12         <= ((![X70 : $i]:
% 1.95/2.12                (((X70) != (sk_D))
% 1.95/2.12                 | ~ (m1_subset_1 @ X70 @ (u1_struct_0 @ sk_B)))))),
% 1.95/2.12      inference('split', [status(esa)], ['81'])).
% 1.95/2.12  thf('111', plain,
% 1.95/2.12      ((~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B)))
% 1.95/2.12         <= ((![X70 : $i]:
% 1.95/2.12                (((X70) != (sk_D))
% 1.95/2.12                 | ~ (m1_subset_1 @ X70 @ (u1_struct_0 @ sk_B)))))),
% 1.95/2.12      inference('simplify', [status(thm)], ['110'])).
% 1.95/2.12  thf('112', plain,
% 1.95/2.12      ((((v2_struct_0 @ sk_C)
% 1.95/2.12         | (v2_struct_0 @ sk_A)
% 1.95/2.12         | (v2_struct_0 @ sk_B)
% 1.95/2.12         | (r1_tsep_1 @ sk_B @ sk_C)))
% 1.95/2.12         <= ((![X70 : $i]:
% 1.95/2.12                (((X70) != (sk_D))
% 1.95/2.12                 | ~ (m1_subset_1 @ X70 @ (u1_struct_0 @ sk_B)))))),
% 1.95/2.12      inference('sup-', [status(thm)], ['109', '111'])).
% 1.95/2.12  thf('113', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('114', plain,
% 1.95/2.12      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C)))
% 1.95/2.12         <= ((![X70 : $i]:
% 1.95/2.12                (((X70) != (sk_D))
% 1.95/2.12                 | ~ (m1_subset_1 @ X70 @ (u1_struct_0 @ sk_B)))))),
% 1.95/2.12      inference('sup-', [status(thm)], ['112', '113'])).
% 1.95/2.12  thf('115', plain, (~ (v2_struct_0 @ sk_B)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('116', plain,
% 1.95/2.12      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A)))
% 1.95/2.12         <= ((![X70 : $i]:
% 1.95/2.12                (((X70) != (sk_D))
% 1.95/2.12                 | ~ (m1_subset_1 @ X70 @ (u1_struct_0 @ sk_B)))))),
% 1.95/2.12      inference('clc', [status(thm)], ['114', '115'])).
% 1.95/2.12  thf('117', plain, (~ (v2_struct_0 @ sk_C)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('118', plain,
% 1.95/2.12      (((v2_struct_0 @ sk_A))
% 1.95/2.12         <= ((![X70 : $i]:
% 1.95/2.12                (((X70) != (sk_D))
% 1.95/2.12                 | ~ (m1_subset_1 @ X70 @ (u1_struct_0 @ sk_B)))))),
% 1.95/2.12      inference('clc', [status(thm)], ['116', '117'])).
% 1.95/2.12  thf('119', plain, (~ (v2_struct_0 @ sk_A)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('120', plain,
% 1.95/2.12      (~
% 1.95/2.12       (![X70 : $i]:
% 1.95/2.12          (((X70) != (sk_D)) | ~ (m1_subset_1 @ X70 @ (u1_struct_0 @ sk_B))))),
% 1.95/2.12      inference('sup-', [status(thm)], ['118', '119'])).
% 1.95/2.12  thf('121', plain,
% 1.95/2.12      ((![X71 : $i]:
% 1.95/2.12          (((X71) != (sk_D)) | ~ (m1_subset_1 @ X71 @ (u1_struct_0 @ sk_C)))) | 
% 1.95/2.12       (![X70 : $i]:
% 1.95/2.12          (((X70) != (sk_D)) | ~ (m1_subset_1 @ X70 @ (u1_struct_0 @ sk_B))))),
% 1.95/2.12      inference('split', [status(esa)], ['81'])).
% 1.95/2.12  thf('122', plain,
% 1.95/2.12      ((![X71 : $i]:
% 1.95/2.12          (((X71) != (sk_D)) | ~ (m1_subset_1 @ X71 @ (u1_struct_0 @ sk_C))))),
% 1.95/2.12      inference('sat_resolution*', [status(thm)], ['120', '121'])).
% 1.95/2.12  thf('123', plain, (~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))),
% 1.95/2.12      inference('simpl_trail', [status(thm)], ['83', '122'])).
% 1.95/2.12  thf('124', plain,
% 1.95/2.12      (((v2_struct_0 @ sk_C)
% 1.95/2.12        | (v2_struct_0 @ sk_A)
% 1.95/2.12        | (v2_struct_0 @ sk_B)
% 1.95/2.12        | (r1_tsep_1 @ sk_B @ sk_C))),
% 1.95/2.12      inference('sup-', [status(thm)], ['80', '123'])).
% 1.95/2.12  thf('125', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('126', plain,
% 1.95/2.12      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 1.95/2.12      inference('sup-', [status(thm)], ['124', '125'])).
% 1.95/2.12  thf('127', plain, (~ (v2_struct_0 @ sk_B)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('128', plain, (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 1.95/2.12      inference('clc', [status(thm)], ['126', '127'])).
% 1.95/2.12  thf('129', plain, (~ (v2_struct_0 @ sk_C)),
% 1.95/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.95/2.12  thf('130', plain, ((v2_struct_0 @ sk_A)),
% 1.95/2.12      inference('clc', [status(thm)], ['128', '129'])).
% 1.95/2.12  thf('131', plain, ($false), inference('demod', [status(thm)], ['0', '130'])).
% 1.95/2.12  
% 1.95/2.12  % SZS output end Refutation
% 1.95/2.12  
% 1.95/2.13  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
