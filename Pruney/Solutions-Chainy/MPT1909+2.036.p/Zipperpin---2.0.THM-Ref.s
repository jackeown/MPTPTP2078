%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0Q1Tmw6Sbm

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:52 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 352 expanded)
%              Number of leaves         :   54 ( 127 expanded)
%              Depth                    :   29
%              Number of atoms          : 1727 (10541 expanded)
%              Number of equality atoms :   77 ( 339 expanded)
%              Maximal formula depth    :   29 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v4_tex_2_type,type,(
    v4_tex_2: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v3_borsuk_1_type,type,(
    v3_borsuk_1: $i > $i > $i > $o )).

thf(t77_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_tex_2 @ B @ A )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( v5_pre_topc @ C @ A @ B )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( v3_borsuk_1 @ C @ A @ B )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                       => ( ( D = E )
                         => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) )
                            = ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v3_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v4_tex_2 @ B @ A )
              & ( m1_pre_topc @ B @ A ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( v5_pre_topc @ C @ A @ B )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( ( v3_borsuk_1 @ C @ A @ B )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) )
                     => ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                         => ( ( D = E )
                           => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) )
                              = ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_tex_2])).

thf('0',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( m1_pre_topc @ X50 @ X51 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X50 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ~ ( l1_pre_topc @ X51 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t46_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( v3_tex_2 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( v1_xboole_0 @ X55 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ~ ( v3_tex_2 @ X55 @ X56 )
      | ~ ( l1_pre_topc @ X56 )
      | ~ ( v2_pre_topc @ X56 )
      | ( v2_struct_0 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t46_tex_2])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tex_2 @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_tex_2 @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v3_tex_2 @ ( u1_struct_0 @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d8_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v4_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( C
                    = ( u1_struct_0 @ B ) )
                 => ( v3_tex_2 @ C @ A ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( m1_pre_topc @ X52 @ X53 )
      | ~ ( v4_tex_2 @ X52 @ X53 )
      | ( X54
       != ( u1_struct_0 @ X52 ) )
      | ( v3_tex_2 @ X54 @ X53 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
      | ~ ( l1_pre_topc @ X53 )
      | ( v2_struct_0 @ X53 ) ) ),
    inference(cnf,[status(esa)],[d8_tex_2])).

thf('14',plain,(
    ! [X52: $i,X53: $i] :
      ( ( v2_struct_0 @ X53 )
      | ~ ( l1_pre_topc @ X53 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X52 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
      | ( v3_tex_2 @ ( u1_struct_0 @ X52 ) @ X53 )
      | ~ ( v4_tex_2 @ X52 @ X53 )
      | ~ ( m1_pre_topc @ X52 @ X53 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v4_tex_2 @ sk_B_1 @ sk_A )
    | ( v3_tex_2 @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v4_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v3_tex_2 @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16','17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v3_tex_2 @ ( u1_struct_0 @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['11','21'])).

thf(t34_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) )).

thf('23',plain,(
    ! [X40: $i] :
      ( ( X40 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X40 ) @ X40 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf('24',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('27',plain,(
    ! [X48: $i,X49: $i] :
      ( ( v1_xboole_0 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ X48 )
      | ( ( k6_domain_1 @ X48 @ X49 )
        = ( k1_tarski @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('28',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t62_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ A )
         => ! [D: $i] :
              ( ( m1_subset_1 @ D @ A )
             => ! [E: $i] :
                  ( ( m1_subset_1 @ E @ A )
                 => ! [F: $i] :
                      ( ( m1_subset_1 @ F @ A )
                     => ! [G: $i] :
                          ( ( m1_subset_1 @ G @ A )
                         => ! [H: $i] :
                              ( ( m1_subset_1 @ H @ A )
                             => ! [I: $i] :
                                  ( ( m1_subset_1 @ I @ A )
                                 => ( ( A != k1_xboole_0 )
                                   => ( m1_subset_1 @ ( k6_enumset1 @ B @ C @ D @ E @ F @ G @ H @ I ) @ ( k1_zfmisc_1 @ A ) ) ) ) ) ) ) ) ) ) ) )).

thf('38',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ X29 )
      | ~ ( m1_subset_1 @ X31 @ X29 )
      | ~ ( m1_subset_1 @ X32 @ X29 )
      | ( m1_subset_1 @ ( k6_enumset1 @ X33 @ X28 @ X34 @ X30 @ X35 @ X31 @ X36 @ X32 ) @ ( k1_zfmisc_1 @ X29 ) )
      | ( X29 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X36 @ X29 )
      | ~ ( m1_subset_1 @ X35 @ X29 )
      | ~ ( m1_subset_1 @ X34 @ X29 )
      | ~ ( m1_subset_1 @ X33 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t62_subset_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( ( u1_struct_0 @ sk_B_1 )
        = k1_xboole_0 )
      | ( m1_subset_1 @ ( k6_enumset1 @ X0 @ sk_D @ X1 @ X6 @ X2 @ X5 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( m1_subset_1 @ ( k6_enumset1 @ sk_D @ sk_D @ X5 @ X0 @ X4 @ X1 @ X3 @ X2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ( ( u1_struct_0 @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('41',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k6_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 )
      = ( k5_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( m1_subset_1 @ ( k5_enumset1 @ sk_D @ X5 @ X0 @ X4 @ X1 @ X3 @ X2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ( ( u1_struct_0 @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( ( u1_struct_0 @ sk_B_1 )
        = k1_xboole_0 )
      | ( m1_subset_1 @ ( k5_enumset1 @ sk_D @ X0 @ sk_D @ X1 @ X4 @ X2 @ X3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['35','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( m1_subset_1 @ ( k5_enumset1 @ sk_D @ sk_D @ sk_D @ X3 @ X0 @ X2 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ( ( u1_struct_0 @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['34','43'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('45',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k5_enumset1 @ X15 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k4_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('46',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k4_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 @ X14 )
      = ( k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( m1_subset_1 @ ( k3_enumset1 @ sk_D @ X3 @ X0 @ X2 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ( ( u1_struct_0 @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( ( u1_struct_0 @ sk_B_1 )
        = k1_xboole_0 )
      | ( m1_subset_1 @ ( k3_enumset1 @ sk_D @ X0 @ sk_D @ X1 @ X2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['33','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( m1_subset_1 @ ( k3_enumset1 @ sk_D @ sk_D @ sk_D @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ( ( u1_struct_0 @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['32','48'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('50',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k3_enumset1 @ X6 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('51',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X3 @ X3 @ X4 @ X5 )
      = ( k1_enumset1 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( m1_subset_1 @ ( k1_enumset1 @ sk_D @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ( ( u1_struct_0 @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( ( u1_struct_0 @ sk_B_1 )
        = k1_xboole_0 )
      | ( m1_subset_1 @ ( k1_enumset1 @ sk_D @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['31','52'])).

thf('54',plain,
    ( ( m1_subset_1 @ ( k1_enumset1 @ sk_D @ sk_D @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','53'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('55',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X2 )
      = ( k2_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('57',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('58',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_pre_topc @ X45 @ X46 )
      | ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( l1_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('64',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t76_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_tex_2 @ B @ A )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( v5_pre_topc @ C @ A @ B )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( v3_borsuk_1 @ C @ A @ B )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ( ( D = E )
                         => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D )
                            = ( k2_pre_topc @ A @ E ) ) ) ) ) ) ) ) ) )).

thf('65',plain,(
    ! [X57: $i,X58: $i,X59: $i,X60: $i,X61: $i] :
      ( ( v2_struct_0 @ X57 )
      | ~ ( v4_tex_2 @ X57 @ X58 )
      | ~ ( m1_pre_topc @ X57 @ X58 )
      | ~ ( v3_borsuk_1 @ X59 @ X58 @ X57 )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X57 ) ) )
      | ( X60 != X61 )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X58 ) @ ( u1_struct_0 @ X57 ) @ X59 @ X60 )
        = ( k2_pre_topc @ X58 @ X61 ) )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X58 ) ) )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X58 ) @ ( u1_struct_0 @ X57 ) ) ) )
      | ~ ( v5_pre_topc @ X59 @ X58 @ X57 )
      | ~ ( v1_funct_2 @ X59 @ ( u1_struct_0 @ X58 ) @ ( u1_struct_0 @ X57 ) )
      | ~ ( v1_funct_1 @ X59 )
      | ~ ( l1_pre_topc @ X58 )
      | ~ ( v3_tdlat_3 @ X58 )
      | ~ ( v2_pre_topc @ X58 )
      | ( v2_struct_0 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t76_tex_2])).

thf('66',plain,(
    ! [X57: $i,X58: $i,X59: $i,X61: $i] :
      ( ( v2_struct_0 @ X58 )
      | ~ ( v2_pre_topc @ X58 )
      | ~ ( v3_tdlat_3 @ X58 )
      | ~ ( l1_pre_topc @ X58 )
      | ~ ( v1_funct_1 @ X59 )
      | ~ ( v1_funct_2 @ X59 @ ( u1_struct_0 @ X58 ) @ ( u1_struct_0 @ X57 ) )
      | ~ ( v5_pre_topc @ X59 @ X58 @ X57 )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X58 ) @ ( u1_struct_0 @ X57 ) ) ) )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X58 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X58 ) @ ( u1_struct_0 @ X57 ) @ X59 @ X61 )
        = ( k2_pre_topc @ X58 @ X61 ) )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X57 ) ) )
      | ~ ( v3_borsuk_1 @ X59 @ X58 @ X57 )
      | ~ ( m1_pre_topc @ X57 @ X58 )
      | ~ ( v4_tex_2 @ X57 @ X58 )
      | ( v2_struct_0 @ X57 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( v4_tex_2 @ sk_B_1 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
      | ~ ( v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,(
    v4_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68','69','70','71','72','73','74','75','76'])).

thf('78',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['63','77'])).

thf('79',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','78'])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X48: $i,X49: $i] :
      ( ( v1_xboole_0 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ X48 )
      | ( ( k6_domain_1 @ X48 @ X49 )
        = ( k1_tarski @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('83',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['80','87'])).

thf('89',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','88'])).

thf('90',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('92',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( r2_hidden @ X37 @ X38 )
      | ~ ( v1_xboole_0 @ X39 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ( ( u1_struct_0 @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('95',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['23','94'])).

thf('96',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['11','21'])).

thf('98',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['100','101'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('103',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('104',plain,(
    $false ),
    inference(demod,[status(thm)],['22','102','103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0Q1Tmw6Sbm
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:09:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.36/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.54  % Solved by: fo/fo7.sh
% 0.36/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.54  % done 75 iterations in 0.064s
% 0.36/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.54  % SZS output start Refutation
% 0.36/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.36/0.54  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.36/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.54  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.36/0.54  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.36/0.54  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.36/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.54  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.36/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.36/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.54  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.36/0.54  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.36/0.54                                           $i > $i).
% 0.36/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.54  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.36/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.36/0.54  thf(v4_tex_2_type, type, v4_tex_2: $i > $i > $o).
% 0.36/0.54  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.36/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.54  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.36/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.54  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.36/0.54  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.36/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.36/0.54  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.36/0.54  thf(sk_E_type, type, sk_E: $i).
% 0.36/0.54  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.36/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.54  thf(v3_borsuk_1_type, type, v3_borsuk_1: $i > $i > $i > $o).
% 0.36/0.54  thf(t77_tex_2, conjecture,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.36/0.54         ( l1_pre_topc @ A ) ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.36/0.54             ( m1_pre_topc @ B @ A ) ) =>
% 0.36/0.54           ( ![C:$i]:
% 0.36/0.54             ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.54                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.54                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.36/0.54                 ( m1_subset_1 @
% 0.36/0.54                   C @ 
% 0.36/0.54                   ( k1_zfmisc_1 @
% 0.36/0.54                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.54               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.36/0.54                 ( ![D:$i]:
% 0.36/0.54                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.36/0.54                     ( ![E:$i]:
% 0.36/0.54                       ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.54                         ( ( ( D ) = ( E ) ) =>
% 0.36/0.54                           ( ( k8_relset_1 @
% 0.36/0.54                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.36/0.54                               ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.36/0.54                             ( k2_pre_topc @
% 0.36/0.54                               A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.54    (~( ![A:$i]:
% 0.36/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.36/0.54            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.54          ( ![B:$i]:
% 0.36/0.54            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.36/0.54                ( m1_pre_topc @ B @ A ) ) =>
% 0.36/0.54              ( ![C:$i]:
% 0.36/0.54                ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.54                    ( v1_funct_2 @
% 0.36/0.54                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.54                    ( v5_pre_topc @ C @ A @ B ) & 
% 0.36/0.54                    ( m1_subset_1 @
% 0.36/0.54                      C @ 
% 0.36/0.54                      ( k1_zfmisc_1 @
% 0.36/0.54                        ( k2_zfmisc_1 @
% 0.36/0.54                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.54                  ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.36/0.54                    ( ![D:$i]:
% 0.36/0.54                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.36/0.54                        ( ![E:$i]:
% 0.36/0.54                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.54                            ( ( ( D ) = ( E ) ) =>
% 0.36/0.54                              ( ( k8_relset_1 @
% 0.36/0.54                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.36/0.54                                  C @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.36/0.54                                ( k2_pre_topc @
% 0.36/0.54                                  A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.36/0.54    inference('cnf.neg', [status(esa)], [t77_tex_2])).
% 0.36/0.54  thf('0', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(t1_tsep_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( l1_pre_topc @ A ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( m1_pre_topc @ B @ A ) =>
% 0.36/0.54           ( m1_subset_1 @
% 0.36/0.54             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.36/0.54  thf('1', plain,
% 0.36/0.54      (![X50 : $i, X51 : $i]:
% 0.36/0.54         (~ (m1_pre_topc @ X50 @ X51)
% 0.36/0.54          | (m1_subset_1 @ (u1_struct_0 @ X50) @ 
% 0.36/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 0.36/0.54          | ~ (l1_pre_topc @ X51))),
% 0.36/0.54      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.36/0.54  thf('2', plain,
% 0.36/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.54        | (m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.36/0.54  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('4', plain,
% 0.36/0.54      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.54      inference('demod', [status(thm)], ['2', '3'])).
% 0.36/0.54  thf(t46_tex_2, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( ( v1_xboole_0 @ B ) & 
% 0.36/0.54             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.54           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.36/0.54  thf('5', plain,
% 0.36/0.54      (![X55 : $i, X56 : $i]:
% 0.36/0.54         (~ (v1_xboole_0 @ X55)
% 0.36/0.54          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (u1_struct_0 @ X56)))
% 0.36/0.54          | ~ (v3_tex_2 @ X55 @ X56)
% 0.36/0.54          | ~ (l1_pre_topc @ X56)
% 0.36/0.54          | ~ (v2_pre_topc @ X56)
% 0.36/0.54          | (v2_struct_0 @ X56))),
% 0.36/0.54      inference('cnf', [status(esa)], [t46_tex_2])).
% 0.36/0.54  thf('6', plain,
% 0.36/0.54      (((v2_struct_0 @ sk_A)
% 0.36/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.36/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.54        | ~ (v3_tex_2 @ (u1_struct_0 @ sk_B_1) @ sk_A)
% 0.36/0.54        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.54  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('9', plain,
% 0.36/0.54      (((v2_struct_0 @ sk_A)
% 0.36/0.54        | ~ (v3_tex_2 @ (u1_struct_0 @ sk_B_1) @ sk_A)
% 0.36/0.54        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.36/0.54      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.36/0.54  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('11', plain,
% 0.36/0.54      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.54        | ~ (v3_tex_2 @ (u1_struct_0 @ sk_B_1) @ sk_A))),
% 0.36/0.54      inference('clc', [status(thm)], ['9', '10'])).
% 0.36/0.54  thf('12', plain,
% 0.36/0.54      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.54      inference('demod', [status(thm)], ['2', '3'])).
% 0.36/0.54  thf(d8_tex_2, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( m1_pre_topc @ B @ A ) =>
% 0.36/0.54           ( ( v4_tex_2 @ B @ A ) <=>
% 0.36/0.54             ( ![C:$i]:
% 0.36/0.54               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.54                 ( ( ( C ) = ( u1_struct_0 @ B ) ) => ( v3_tex_2 @ C @ A ) ) ) ) ) ) ) ))).
% 0.36/0.54  thf('13', plain,
% 0.36/0.54      (![X52 : $i, X53 : $i, X54 : $i]:
% 0.36/0.54         (~ (m1_pre_topc @ X52 @ X53)
% 0.36/0.54          | ~ (v4_tex_2 @ X52 @ X53)
% 0.36/0.54          | ((X54) != (u1_struct_0 @ X52))
% 0.36/0.54          | (v3_tex_2 @ X54 @ X53)
% 0.36/0.54          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 0.36/0.54          | ~ (l1_pre_topc @ X53)
% 0.36/0.54          | (v2_struct_0 @ X53))),
% 0.36/0.54      inference('cnf', [status(esa)], [d8_tex_2])).
% 0.36/0.54  thf('14', plain,
% 0.36/0.54      (![X52 : $i, X53 : $i]:
% 0.36/0.54         ((v2_struct_0 @ X53)
% 0.36/0.54          | ~ (l1_pre_topc @ X53)
% 0.36/0.54          | ~ (m1_subset_1 @ (u1_struct_0 @ X52) @ 
% 0.36/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 0.36/0.54          | (v3_tex_2 @ (u1_struct_0 @ X52) @ X53)
% 0.36/0.54          | ~ (v4_tex_2 @ X52 @ X53)
% 0.36/0.54          | ~ (m1_pre_topc @ X52 @ X53))),
% 0.36/0.54      inference('simplify', [status(thm)], ['13'])).
% 0.36/0.54  thf('15', plain,
% 0.36/0.54      ((~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.36/0.54        | ~ (v4_tex_2 @ sk_B_1 @ sk_A)
% 0.36/0.54        | (v3_tex_2 @ (u1_struct_0 @ sk_B_1) @ sk_A)
% 0.36/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.54        | (v2_struct_0 @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['12', '14'])).
% 0.36/0.54  thf('16', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('17', plain, ((v4_tex_2 @ sk_B_1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('19', plain,
% 0.36/0.54      (((v3_tex_2 @ (u1_struct_0 @ sk_B_1) @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['15', '16', '17', '18'])).
% 0.36/0.54  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('21', plain, ((v3_tex_2 @ (u1_struct_0 @ sk_B_1) @ sk_A)),
% 0.36/0.54      inference('clc', [status(thm)], ['19', '20'])).
% 0.36/0.54  thf('22', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 0.36/0.54      inference('demod', [status(thm)], ['11', '21'])).
% 0.36/0.54  thf(t34_mcart_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.36/0.54          ( ![B:$i]:
% 0.36/0.54            ( ~( ( r2_hidden @ B @ A ) & 
% 0.36/0.54                 ( ![C:$i,D:$i,E:$i,F:$i]:
% 0.36/0.54                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.36/0.54                        ( ( B ) = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.54  thf('23', plain,
% 0.36/0.54      (![X40 : $i]:
% 0.36/0.54         (((X40) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X40) @ X40))),
% 0.36/0.54      inference('cnf', [status(esa)], [t34_mcart_1])).
% 0.36/0.54  thf('24', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_A))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('25', plain, (((sk_D) = (sk_E))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('26', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['24', '25'])).
% 0.36/0.54  thf(redefinition_k6_domain_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.36/0.54       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.36/0.54  thf('27', plain,
% 0.36/0.54      (![X48 : $i, X49 : $i]:
% 0.36/0.54         ((v1_xboole_0 @ X48)
% 0.36/0.54          | ~ (m1_subset_1 @ X49 @ X48)
% 0.36/0.54          | ((k6_domain_1 @ X48 @ X49) = (k1_tarski @ X49)))),
% 0.36/0.54      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.36/0.54  thf('28', plain,
% 0.36/0.54      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D) = (k1_tarski @ sk_D))
% 0.36/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['26', '27'])).
% 0.36/0.54  thf('29', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('30', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B_1))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('31', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B_1))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('32', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B_1))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('33', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B_1))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('34', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B_1))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('35', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B_1))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('36', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B_1))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('37', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B_1))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(t62_subset_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ B @ A ) =>
% 0.36/0.54       ( ![C:$i]:
% 0.36/0.54         ( ( m1_subset_1 @ C @ A ) =>
% 0.36/0.54           ( ![D:$i]:
% 0.36/0.54             ( ( m1_subset_1 @ D @ A ) =>
% 0.36/0.54               ( ![E:$i]:
% 0.36/0.54                 ( ( m1_subset_1 @ E @ A ) =>
% 0.36/0.54                   ( ![F:$i]:
% 0.36/0.54                     ( ( m1_subset_1 @ F @ A ) =>
% 0.36/0.54                       ( ![G:$i]:
% 0.36/0.54                         ( ( m1_subset_1 @ G @ A ) =>
% 0.36/0.54                           ( ![H:$i]:
% 0.36/0.54                             ( ( m1_subset_1 @ H @ A ) =>
% 0.36/0.54                               ( ![I:$i]:
% 0.36/0.54                                 ( ( m1_subset_1 @ I @ A ) =>
% 0.36/0.54                                   ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.36/0.54                                     ( m1_subset_1 @
% 0.36/0.54                                       ( k6_enumset1 @
% 0.36/0.54                                         B @ C @ D @ E @ F @ G @ H @ I ) @ 
% 0.36/0.54                                       ( k1_zfmisc_1 @ A ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.54  thf('38', plain,
% 0.36/0.54      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, 
% 0.36/0.54         X35 : $i, X36 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X28 @ X29)
% 0.36/0.54          | ~ (m1_subset_1 @ X30 @ X29)
% 0.36/0.54          | ~ (m1_subset_1 @ X31 @ X29)
% 0.36/0.54          | ~ (m1_subset_1 @ X32 @ X29)
% 0.36/0.54          | (m1_subset_1 @ 
% 0.36/0.54             (k6_enumset1 @ X33 @ X28 @ X34 @ X30 @ X35 @ X31 @ X36 @ X32) @ 
% 0.36/0.54             (k1_zfmisc_1 @ X29))
% 0.36/0.54          | ((X29) = (k1_xboole_0))
% 0.36/0.54          | ~ (m1_subset_1 @ X36 @ X29)
% 0.36/0.54          | ~ (m1_subset_1 @ X35 @ X29)
% 0.36/0.54          | ~ (m1_subset_1 @ X34 @ X29)
% 0.36/0.54          | ~ (m1_subset_1 @ X33 @ X29))),
% 0.36/0.54      inference('cnf', [status(esa)], [t62_subset_1])).
% 0.36/0.54  thf('39', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.54          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.54          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.54          | ((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.36/0.54          | (m1_subset_1 @ 
% 0.36/0.54             (k6_enumset1 @ X0 @ sk_D @ X1 @ X6 @ X2 @ X5 @ X3 @ X4) @ 
% 0.36/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.36/0.54          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.54          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.54          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ sk_B_1)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['37', '38'])).
% 0.36/0.54  thf('40', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.54          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.54          | (m1_subset_1 @ 
% 0.36/0.54             (k6_enumset1 @ sk_D @ sk_D @ X5 @ X0 @ X4 @ X1 @ X3 @ X2) @ 
% 0.36/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.36/0.54          | ((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.36/0.54          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.54          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.54          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ sk_B_1)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['36', '39'])).
% 0.36/0.54  thf(t75_enumset1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.36/0.54     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.36/0.54       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.36/0.54  thf('41', plain,
% 0.36/0.54      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.36/0.54         ((k6_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27)
% 0.36/0.54           = (k5_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27))),
% 0.36/0.54      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.36/0.54  thf('42', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.54          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.54          | (m1_subset_1 @ 
% 0.36/0.54             (k5_enumset1 @ sk_D @ X5 @ X0 @ X4 @ X1 @ X3 @ X2) @ 
% 0.36/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.36/0.54          | ((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.36/0.54          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.54          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.54          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ sk_B_1)))),
% 0.36/0.54      inference('demod', [status(thm)], ['40', '41'])).
% 0.36/0.54  thf('43', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.54          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.54          | ((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.36/0.54          | (m1_subset_1 @ 
% 0.36/0.54             (k5_enumset1 @ sk_D @ X0 @ sk_D @ X1 @ X4 @ X2 @ X3) @ 
% 0.36/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.36/0.54          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.54          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ sk_B_1)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['35', '42'])).
% 0.36/0.54  thf('44', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.54          | (m1_subset_1 @ 
% 0.36/0.54             (k5_enumset1 @ sk_D @ sk_D @ sk_D @ X3 @ X0 @ X2 @ X1) @ 
% 0.36/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.36/0.54          | ((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.36/0.54          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.54          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_B_1)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['34', '43'])).
% 0.36/0.54  thf(t74_enumset1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.36/0.54     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.36/0.54       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.36/0.54  thf('45', plain,
% 0.36/0.54      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.36/0.54         ((k5_enumset1 @ X15 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20)
% 0.36/0.54           = (k4_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20))),
% 0.36/0.54      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.36/0.54  thf(t73_enumset1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.36/0.54     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.36/0.54       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.36/0.54  thf('46', plain,
% 0.36/0.54      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.36/0.54         ((k4_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 @ X14)
% 0.36/0.54           = (k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14))),
% 0.36/0.54      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.36/0.54  thf('47', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.54          | (m1_subset_1 @ (k3_enumset1 @ sk_D @ X3 @ X0 @ X2 @ X1) @ 
% 0.36/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.36/0.54          | ((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.36/0.54          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.54          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_B_1)))),
% 0.36/0.54      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.36/0.54  thf('48', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.54          | ((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.36/0.54          | (m1_subset_1 @ (k3_enumset1 @ sk_D @ X0 @ sk_D @ X1 @ X2) @ 
% 0.36/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.36/0.54          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_B_1)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['33', '47'])).
% 0.36/0.54  thf('49', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.54          | (m1_subset_1 @ (k3_enumset1 @ sk_D @ sk_D @ sk_D @ X1 @ X0) @ 
% 0.36/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.36/0.54          | ((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.36/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B_1)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['32', '48'])).
% 0.36/0.54  thf(t72_enumset1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.54     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.36/0.54  thf('50', plain,
% 0.36/0.54      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.36/0.54         ((k3_enumset1 @ X6 @ X6 @ X7 @ X8 @ X9)
% 0.36/0.54           = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 0.36/0.54      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.36/0.54  thf(t71_enumset1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.36/0.54  thf('51', plain,
% 0.36/0.54      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.54         ((k2_enumset1 @ X3 @ X3 @ X4 @ X5) = (k1_enumset1 @ X3 @ X4 @ X5))),
% 0.36/0.54      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.36/0.54  thf('52', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.54          | (m1_subset_1 @ (k1_enumset1 @ sk_D @ X1 @ X0) @ 
% 0.36/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.36/0.54          | ((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.36/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B_1)))),
% 0.36/0.54      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.36/0.54  thf('53', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.54          | ((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.36/0.54          | (m1_subset_1 @ (k1_enumset1 @ sk_D @ X0 @ sk_D) @ 
% 0.36/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['31', '52'])).
% 0.36/0.54  thf('54', plain,
% 0.36/0.54      (((m1_subset_1 @ (k1_enumset1 @ sk_D @ sk_D @ sk_D) @ 
% 0.36/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.36/0.54        | ((u1_struct_0 @ sk_B_1) = (k1_xboole_0)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['30', '53'])).
% 0.36/0.54  thf(t70_enumset1, axiom,
% 0.36/0.54    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.36/0.54  thf('55', plain,
% 0.36/0.54      (![X1 : $i, X2 : $i]:
% 0.36/0.54         ((k1_enumset1 @ X1 @ X1 @ X2) = (k2_tarski @ X1 @ X2))),
% 0.36/0.54      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.36/0.54  thf(t69_enumset1, axiom,
% 0.36/0.54    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.36/0.54  thf('56', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.36/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.54  thf('57', plain,
% 0.36/0.54      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.36/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.36/0.54        | ((u1_struct_0 @ sk_B_1) = (k1_xboole_0)))),
% 0.36/0.54      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.36/0.54  thf(t39_pre_topc, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( l1_pre_topc @ A ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( m1_pre_topc @ B @ A ) =>
% 0.36/0.54           ( ![C:$i]:
% 0.36/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.36/0.54               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.36/0.54  thf('58', plain,
% 0.36/0.54      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.36/0.54         (~ (m1_pre_topc @ X45 @ X46)
% 0.36/0.54          | (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.36/0.54          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 0.36/0.54          | ~ (l1_pre_topc @ X46))),
% 0.36/0.54      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.36/0.54  thf('59', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.36/0.54          | ~ (l1_pre_topc @ X0)
% 0.36/0.54          | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.36/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.36/0.54          | ~ (m1_pre_topc @ sk_B_1 @ X0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['57', '58'])).
% 0.36/0.54  thf('60', plain,
% 0.36/0.54      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.36/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.54        | ((u1_struct_0 @ sk_B_1) = (k1_xboole_0)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['29', '59'])).
% 0.36/0.54  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('62', plain,
% 0.36/0.54      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.36/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.54        | ((u1_struct_0 @ sk_B_1) = (k1_xboole_0)))),
% 0.36/0.54      inference('demod', [status(thm)], ['60', '61'])).
% 0.36/0.54  thf('63', plain,
% 0.36/0.54      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.36/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.36/0.54        | ((u1_struct_0 @ sk_B_1) = (k1_xboole_0)))),
% 0.36/0.54      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.36/0.54  thf('64', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_C_1 @ 
% 0.36/0.54        (k1_zfmisc_1 @ 
% 0.36/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(t76_tex_2, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.36/0.54         ( l1_pre_topc @ A ) ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.36/0.54             ( m1_pre_topc @ B @ A ) ) =>
% 0.36/0.54           ( ![C:$i]:
% 0.36/0.54             ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.54                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.54                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.36/0.54                 ( m1_subset_1 @
% 0.36/0.54                   C @ 
% 0.36/0.54                   ( k1_zfmisc_1 @
% 0.36/0.54                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.54               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.36/0.54                 ( ![D:$i]:
% 0.36/0.54                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.36/0.54                     ( ![E:$i]:
% 0.36/0.54                       ( ( m1_subset_1 @
% 0.36/0.54                           E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.54                         ( ( ( D ) = ( E ) ) =>
% 0.36/0.54                           ( ( k8_relset_1 @
% 0.36/0.54                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.36/0.54                               D ) =
% 0.36/0.54                             ( k2_pre_topc @ A @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.54  thf('65', plain,
% 0.36/0.54      (![X57 : $i, X58 : $i, X59 : $i, X60 : $i, X61 : $i]:
% 0.36/0.54         ((v2_struct_0 @ X57)
% 0.36/0.54          | ~ (v4_tex_2 @ X57 @ X58)
% 0.36/0.54          | ~ (m1_pre_topc @ X57 @ X58)
% 0.36/0.54          | ~ (v3_borsuk_1 @ X59 @ X58 @ X57)
% 0.36/0.54          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (u1_struct_0 @ X57)))
% 0.36/0.54          | ((X60) != (X61))
% 0.36/0.54          | ((k8_relset_1 @ (u1_struct_0 @ X58) @ (u1_struct_0 @ X57) @ X59 @ 
% 0.36/0.54              X60) = (k2_pre_topc @ X58 @ X61))
% 0.36/0.54          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (u1_struct_0 @ X58)))
% 0.36/0.54          | ~ (m1_subset_1 @ X59 @ 
% 0.36/0.54               (k1_zfmisc_1 @ 
% 0.36/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X58) @ (u1_struct_0 @ X57))))
% 0.36/0.54          | ~ (v5_pre_topc @ X59 @ X58 @ X57)
% 0.36/0.54          | ~ (v1_funct_2 @ X59 @ (u1_struct_0 @ X58) @ (u1_struct_0 @ X57))
% 0.36/0.54          | ~ (v1_funct_1 @ X59)
% 0.36/0.54          | ~ (l1_pre_topc @ X58)
% 0.36/0.54          | ~ (v3_tdlat_3 @ X58)
% 0.36/0.54          | ~ (v2_pre_topc @ X58)
% 0.36/0.54          | (v2_struct_0 @ X58))),
% 0.36/0.54      inference('cnf', [status(esa)], [t76_tex_2])).
% 0.36/0.54  thf('66', plain,
% 0.36/0.54      (![X57 : $i, X58 : $i, X59 : $i, X61 : $i]:
% 0.36/0.54         ((v2_struct_0 @ X58)
% 0.36/0.54          | ~ (v2_pre_topc @ X58)
% 0.36/0.54          | ~ (v3_tdlat_3 @ X58)
% 0.36/0.54          | ~ (l1_pre_topc @ X58)
% 0.36/0.54          | ~ (v1_funct_1 @ X59)
% 0.36/0.54          | ~ (v1_funct_2 @ X59 @ (u1_struct_0 @ X58) @ (u1_struct_0 @ X57))
% 0.36/0.54          | ~ (v5_pre_topc @ X59 @ X58 @ X57)
% 0.36/0.54          | ~ (m1_subset_1 @ X59 @ 
% 0.36/0.54               (k1_zfmisc_1 @ 
% 0.36/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X58) @ (u1_struct_0 @ X57))))
% 0.36/0.54          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (u1_struct_0 @ X58)))
% 0.36/0.54          | ((k8_relset_1 @ (u1_struct_0 @ X58) @ (u1_struct_0 @ X57) @ X59 @ 
% 0.36/0.54              X61) = (k2_pre_topc @ X58 @ X61))
% 0.36/0.54          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (u1_struct_0 @ X57)))
% 0.36/0.54          | ~ (v3_borsuk_1 @ X59 @ X58 @ X57)
% 0.36/0.54          | ~ (m1_pre_topc @ X57 @ X58)
% 0.36/0.54          | ~ (v4_tex_2 @ X57 @ X58)
% 0.36/0.54          | (v2_struct_0 @ X57))),
% 0.36/0.54      inference('simplify', [status(thm)], ['65'])).
% 0.36/0.54  thf('67', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((v2_struct_0 @ sk_B_1)
% 0.36/0.54          | ~ (v4_tex_2 @ sk_B_1 @ sk_A)
% 0.36/0.54          | ~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.36/0.54          | ~ (v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B_1)
% 0.36/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.36/0.54          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.54              sk_C_1 @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.36/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.54          | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)
% 0.36/0.54          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.54               (u1_struct_0 @ sk_B_1))
% 0.36/0.54          | ~ (v1_funct_1 @ sk_C_1)
% 0.36/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.54          | ~ (v3_tdlat_3 @ sk_A)
% 0.36/0.54          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.54          | (v2_struct_0 @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['64', '66'])).
% 0.36/0.54  thf('68', plain, ((v4_tex_2 @ sk_B_1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('69', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('70', plain, ((v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B_1)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('71', plain, ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_1)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('72', plain,
% 0.36/0.54      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('73', plain, ((v1_funct_1 @ sk_C_1)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('75', plain, ((v3_tdlat_3 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('76', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('77', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((v2_struct_0 @ sk_B_1)
% 0.36/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.36/0.54          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.54              sk_C_1 @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.36/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.54          | (v2_struct_0 @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)],
% 0.36/0.54                ['67', '68', '69', '70', '71', '72', '73', '74', '75', '76'])).
% 0.36/0.54  thf('78', plain,
% 0.36/0.54      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.36/0.54        | (v2_struct_0 @ sk_A)
% 0.36/0.54        | ~ (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.36/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.54        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.54            sk_C_1 @ (k1_tarski @ sk_D))
% 0.36/0.54            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.36/0.54        | (v2_struct_0 @ sk_B_1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['63', '77'])).
% 0.36/0.54  thf('79', plain,
% 0.36/0.54      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.36/0.54        | (v2_struct_0 @ sk_B_1)
% 0.36/0.54        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.54            sk_C_1 @ (k1_tarski @ sk_D))
% 0.36/0.54            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.36/0.54        | (v2_struct_0 @ sk_A)
% 0.36/0.54        | ((u1_struct_0 @ sk_B_1) = (k1_xboole_0)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['62', '78'])).
% 0.36/0.54  thf('80', plain,
% 0.36/0.54      (((v2_struct_0 @ sk_A)
% 0.36/0.54        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.54            sk_C_1 @ (k1_tarski @ sk_D))
% 0.36/0.54            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.36/0.54        | (v2_struct_0 @ sk_B_1)
% 0.36/0.54        | ((u1_struct_0 @ sk_B_1) = (k1_xboole_0)))),
% 0.36/0.54      inference('simplify', [status(thm)], ['79'])).
% 0.36/0.54  thf('81', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B_1))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('82', plain,
% 0.36/0.54      (![X48 : $i, X49 : $i]:
% 0.36/0.54         ((v1_xboole_0 @ X48)
% 0.36/0.54          | ~ (m1_subset_1 @ X49 @ X48)
% 0.36/0.54          | ((k6_domain_1 @ X48 @ X49) = (k1_tarski @ X49)))),
% 0.36/0.54      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.36/0.54  thf('83', plain,
% 0.36/0.54      ((((k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D) = (k1_tarski @ sk_D))
% 0.36/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['81', '82'])).
% 0.36/0.54  thf('84', plain,
% 0.36/0.54      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.54         sk_C_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D))
% 0.36/0.54         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_E)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('85', plain, (((sk_D) = (sk_E))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('86', plain,
% 0.36/0.54      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.54         sk_C_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D))
% 0.36/0.54         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 0.36/0.54      inference('demod', [status(thm)], ['84', '85'])).
% 0.36/0.54  thf('87', plain,
% 0.36/0.54      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.54          sk_C_1 @ (k1_tarski @ sk_D))
% 0.36/0.54          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.36/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['83', '86'])).
% 0.36/0.54  thf('88', plain,
% 0.36/0.54      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.36/0.54          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.36/0.54        | ((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.36/0.54        | (v2_struct_0 @ sk_B_1)
% 0.36/0.54        | (v2_struct_0 @ sk_A)
% 0.36/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['80', '87'])).
% 0.36/0.54  thf('89', plain,
% 0.36/0.54      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.36/0.54          != (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.36/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.54        | (v2_struct_0 @ sk_A)
% 0.36/0.54        | (v2_struct_0 @ sk_B_1)
% 0.36/0.54        | ((u1_struct_0 @ sk_B_1) = (k1_xboole_0)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['28', '88'])).
% 0.36/0.54  thf('90', plain,
% 0.36/0.54      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.36/0.54        | (v2_struct_0 @ sk_B_1)
% 0.36/0.54        | (v2_struct_0 @ sk_A)
% 0.36/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.54      inference('simplify', [status(thm)], ['89'])).
% 0.36/0.54  thf('91', plain,
% 0.36/0.54      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.36/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.54      inference('demod', [status(thm)], ['2', '3'])).
% 0.36/0.54  thf(t5_subset, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.36/0.54          ( v1_xboole_0 @ C ) ) ))).
% 0.36/0.54  thf('92', plain,
% 0.36/0.54      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X37 @ X38)
% 0.36/0.54          | ~ (v1_xboole_0 @ X39)
% 0.36/0.54          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t5_subset])).
% 0.36/0.54  thf('93', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.54          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_B_1)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['91', '92'])).
% 0.36/0.54  thf('94', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.54          | (v2_struct_0 @ sk_A)
% 0.36/0.54          | (v2_struct_0 @ sk_B_1)
% 0.36/0.54          | ((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.36/0.54          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_B_1)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['90', '93'])).
% 0.36/0.54  thf('95', plain,
% 0.36/0.54      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.36/0.54        | ((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.36/0.54        | (v2_struct_0 @ sk_B_1)
% 0.36/0.54        | (v2_struct_0 @ sk_A)
% 0.36/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['23', '94'])).
% 0.36/0.54  thf('96', plain,
% 0.36/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.36/0.54        | (v2_struct_0 @ sk_A)
% 0.36/0.54        | (v2_struct_0 @ sk_B_1)
% 0.36/0.54        | ((u1_struct_0 @ sk_B_1) = (k1_xboole_0)))),
% 0.36/0.54      inference('simplify', [status(thm)], ['95'])).
% 0.36/0.54  thf('97', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 0.36/0.54      inference('demod', [status(thm)], ['11', '21'])).
% 0.36/0.54  thf('98', plain,
% 0.36/0.54      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.36/0.54        | (v2_struct_0 @ sk_B_1)
% 0.36/0.54        | (v2_struct_0 @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['96', '97'])).
% 0.36/0.54  thf('99', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('100', plain,
% 0.36/0.54      (((v2_struct_0 @ sk_A) | ((u1_struct_0 @ sk_B_1) = (k1_xboole_0)))),
% 0.36/0.54      inference('clc', [status(thm)], ['98', '99'])).
% 0.36/0.54  thf('101', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('102', plain, (((u1_struct_0 @ sk_B_1) = (k1_xboole_0))),
% 0.36/0.54      inference('clc', [status(thm)], ['100', '101'])).
% 0.36/0.54  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.36/0.54  thf('103', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.54  thf('104', plain, ($false),
% 0.36/0.54      inference('demod', [status(thm)], ['22', '102', '103'])).
% 0.36/0.54  
% 0.36/0.54  % SZS output end Refutation
% 0.36/0.54  
% 0.36/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
