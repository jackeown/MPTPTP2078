%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Cbc2MSCm1z

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:13 EST 2020

% Result     : Theorem 13.60s
% Output     : Refutation 13.60s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 348 expanded)
%              Number of leaves         :   33 ( 109 expanded)
%              Depth                    :   36
%              Number of atoms          : 1810 (7596 expanded)
%              Number of equality atoms :   44 ( 300 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tsep_1_type,type,(
    k2_tsep_1: $i > $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( m1_pre_topc @ X51 @ X52 )
      | ( v2_struct_0 @ X51 )
      | ~ ( l1_pre_topc @ X52 )
      | ( v2_struct_0 @ X52 )
      | ( v2_struct_0 @ X53 )
      | ~ ( m1_pre_topc @ X53 @ X52 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X52 @ X51 @ X53 ) @ X52 ) ) ),
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

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X30 ) @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('9',plain,(
    ! [X29: $i] :
      ( ( k2_subset_1 @ X29 )
      = X29 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('10',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X31 @ X32 @ X33 ) @ ( k1_zfmisc_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X39: $i,X40: $i] :
      ( ( r1_tarski @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k9_subset_1 @ X36 @ X34 @ X35 )
        = ( k3_xboole_0 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X37 @ X38 ) )
      = ( k3_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('18',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k9_subset_1 @ X36 @ X34 @ X35 )
        = ( k1_setfam_1 @ ( k2_tarski @ X34 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('21',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( m1_pre_topc @ X51 @ X52 )
      | ( v2_struct_0 @ X51 )
      | ~ ( l1_pre_topc @ X52 )
      | ( v2_struct_0 @ X52 )
      | ( v2_struct_0 @ X53 )
      | ~ ( m1_pre_topc @ X53 @ X52 )
      | ( v1_pre_topc @ ( k2_tsep_1 @ X52 @ X51 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,
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

thf('29',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( v2_struct_0 @ X47 )
      | ~ ( m1_pre_topc @ X47 @ X48 )
      | ( r1_tsep_1 @ X47 @ X49 )
      | ( v2_struct_0 @ X50 )
      | ~ ( v1_pre_topc @ X50 )
      | ~ ( m1_pre_topc @ X50 @ X48 )
      | ( X50
       != ( k2_tsep_1 @ X48 @ X47 @ X49 ) )
      | ( ( u1_struct_0 @ X50 )
        = ( k3_xboole_0 @ ( u1_struct_0 @ X47 ) @ ( u1_struct_0 @ X49 ) ) )
      | ~ ( m1_pre_topc @ X49 @ X48 )
      | ( v2_struct_0 @ X49 )
      | ~ ( l1_pre_topc @ X48 )
      | ( v2_struct_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[d5_tsep_1])).

thf('30',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( v2_struct_0 @ X48 )
      | ~ ( l1_pre_topc @ X48 )
      | ( v2_struct_0 @ X49 )
      | ~ ( m1_pre_topc @ X49 @ X48 )
      | ( ( u1_struct_0 @ ( k2_tsep_1 @ X48 @ X47 @ X49 ) )
        = ( k3_xboole_0 @ ( u1_struct_0 @ X47 ) @ ( u1_struct_0 @ X49 ) ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ X48 @ X47 @ X49 ) @ X48 )
      | ~ ( v1_pre_topc @ ( k2_tsep_1 @ X48 @ X47 @ X49 ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ X48 @ X47 @ X49 ) )
      | ( r1_tsep_1 @ X47 @ X49 )
      | ~ ( m1_pre_topc @ X47 @ X48 )
      | ( v2_struct_0 @ X47 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X37 @ X38 ) )
      = ( k3_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('32',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( v2_struct_0 @ X48 )
      | ~ ( l1_pre_topc @ X48 )
      | ( v2_struct_0 @ X49 )
      | ~ ( m1_pre_topc @ X49 @ X48 )
      | ( ( u1_struct_0 @ ( k2_tsep_1 @ X48 @ X47 @ X49 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ ( u1_struct_0 @ X47 ) @ ( u1_struct_0 @ X49 ) ) ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ X48 @ X47 @ X49 ) @ X48 )
      | ~ ( v1_pre_topc @ ( k2_tsep_1 @ X48 @ X47 @ X49 ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ X48 @ X47 @ X49 ) )
      | ( r1_tsep_1 @ X47 @ X49 )
      | ~ ( m1_pre_topc @ X47 @ X48 )
      | ( v2_struct_0 @ X47 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k1_setfam_1 @ ( k2_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','32'])).

thf('34',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k1_setfam_1 @ ( k2_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','35','36'])).

thf('38',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k1_setfam_1 @ ( k2_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) )
    | ~ ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k1_setfam_1 @ ( k2_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['27','38'])).

thf('40',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k1_setfam_1 @ ( k2_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( m1_pre_topc @ X51 @ X52 )
      | ( v2_struct_0 @ X51 )
      | ~ ( l1_pre_topc @ X52 )
      | ( v2_struct_0 @ X52 )
      | ( v2_struct_0 @ X53 )
      | ~ ( m1_pre_topc @ X53 @ X52 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X52 @ X51 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k1_setfam_1 @ ( k2_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k1_setfam_1 @ ( k2_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k1_setfam_1 @ ( k2_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['46'])).

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

thf('48',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ~ ( m1_pre_topc @ X54 @ X55 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X54 ) @ ( u1_struct_0 @ X56 ) )
      | ( m1_pre_topc @ X54 @ X56 )
      | ~ ( m1_pre_topc @ X56 @ X55 )
      | ~ ( l1_pre_topc @ X55 )
      | ~ ( v2_pre_topc @ X55 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
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
    inference('sup-',[status(thm)],['20','49'])).

thf('51',plain,
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
    inference('sup-',[status(thm)],['7','50'])).

thf('52',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('56',plain,
    ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
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

thf('58',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( v2_struct_0 @ X44 )
      | ~ ( m1_pre_topc @ X44 @ X45 )
      | ( m1_subset_1 @ X46 @ ( u1_struct_0 @ X45 ) )
      | ~ ( m1_subset_1 @ X46 @ ( u1_struct_0 @ X44 ) )
      | ~ ( l1_pre_topc @ X45 )
      | ( v2_struct_0 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t55_pre_topc])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
    | ~ ( l1_pre_topc @ sk_C )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('62',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_pre_topc @ X42 @ X43 )
      | ( l1_pre_topc @ X42 )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('63',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['60','65'])).

thf('67',plain,
    ( ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( m1_pre_topc @ X51 @ X52 )
      | ( v2_struct_0 @ X51 )
      | ~ ( l1_pre_topc @ X52 )
      | ( v2_struct_0 @ X52 )
      | ( v2_struct_0 @ X53 )
      | ~ ( m1_pre_topc @ X53 @ X52 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X52 @ X51 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('69',plain,
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
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['69','70','71','72'])).

thf('74',plain,
    ( ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( m1_subset_1 @ X57 @ ( u1_struct_0 @ sk_B ) )
      | ( X57 != sk_D )
      | ~ ( m1_subset_1 @ X58 @ ( u1_struct_0 @ sk_C ) )
      | ( X58 != sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ! [X58: $i] :
        ( ( X58 != sk_D )
        | ~ ( m1_subset_1 @ X58 @ ( u1_struct_0 @ sk_C ) ) )
   <= ! [X58: $i] :
        ( ( X58 != sk_D )
        | ~ ( m1_subset_1 @ X58 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(split,[status(esa)],['75'])).

thf('77',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
   <= ! [X58: $i] :
        ( ( X58 != sk_D )
        | ~ ( m1_subset_1 @ X58 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('80',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X37 @ X38 ) )
      = ( k3_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('83',plain,(
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
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
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
    inference('sup-',[status(thm)],['78','83'])).

thf('85',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['84','85','86','87'])).

thf('89',plain,
    ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_pre_topc @ X42 @ X43 )
      | ( l1_pre_topc @ X42 )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('94',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['91','96'])).

thf('98',plain,
    ( ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( m1_pre_topc @ X51 @ X52 )
      | ( v2_struct_0 @ X51 )
      | ~ ( l1_pre_topc @ X52 )
      | ( v2_struct_0 @ X52 )
      | ( v2_struct_0 @ X53 )
      | ~ ( m1_pre_topc @ X53 @ X52 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X52 @ X51 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('100',plain,
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
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['100','101','102','103'])).

thf('105',plain,
    ( ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,
    ( ! [X57: $i] :
        ( ( X57 != sk_D )
        | ~ ( m1_subset_1 @ X57 @ ( u1_struct_0 @ sk_B ) ) )
   <= ! [X57: $i] :
        ( ( X57 != sk_D )
        | ~ ( m1_subset_1 @ X57 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(split,[status(esa)],['75'])).

thf('107',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
   <= ! [X57: $i] :
        ( ( X57 != sk_D )
        | ~ ( m1_subset_1 @ X57 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C ) )
   <= ! [X57: $i] :
        ( ( X57 != sk_D )
        | ~ ( m1_subset_1 @ X57 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['105','107'])).

thf('109',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ! [X57: $i] :
        ( ( X57 != sk_D )
        | ~ ( m1_subset_1 @ X57 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X57: $i] :
        ( ( X57 != sk_D )
        | ~ ( m1_subset_1 @ X57 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ! [X57: $i] :
        ( ( X57 != sk_D )
        | ~ ( m1_subset_1 @ X57 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ~ ! [X57: $i] :
        ( ( X57 != sk_D )
        | ~ ( m1_subset_1 @ X57 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ! [X58: $i] :
        ( ( X58 != sk_D )
        | ~ ( m1_subset_1 @ X58 @ ( u1_struct_0 @ sk_C ) ) )
    | ! [X57: $i] :
        ( ( X57 != sk_D )
        | ~ ( m1_subset_1 @ X57 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(split,[status(esa)],['75'])).

thf('118',plain,(
    ! [X58: $i] :
      ( ( X58 != sk_D )
      | ~ ( m1_subset_1 @ X58 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sat_resolution*',[status(thm)],['116','117'])).

thf('119',plain,(
    ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['77','118'])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['74','119'])).

thf('121',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,(
    $false ),
    inference(demod,[status(thm)],['0','126'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Cbc2MSCm1z
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:36:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 13.60/13.83  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 13.60/13.83  % Solved by: fo/fo7.sh
% 13.60/13.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 13.60/13.83  % done 7454 iterations in 13.363s
% 13.60/13.83  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 13.60/13.83  % SZS output start Refutation
% 13.60/13.83  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 13.60/13.83  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 13.60/13.83  thf(sk_C_type, type, sk_C: $i).
% 13.60/13.83  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 13.60/13.83  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 13.60/13.83  thf(sk_D_type, type, sk_D: $i).
% 13.60/13.83  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 13.60/13.83  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 13.60/13.83  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 13.60/13.83  thf(k2_tsep_1_type, type, k2_tsep_1: $i > $i > $i > $i).
% 13.60/13.83  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 13.60/13.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 13.60/13.83  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 13.60/13.83  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 13.60/13.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 13.60/13.83  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 13.60/13.83  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 13.60/13.83  thf(sk_B_type, type, sk_B: $i).
% 13.60/13.83  thf(sk_A_type, type, sk_A: $i).
% 13.60/13.83  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 13.60/13.83  thf(t17_tmap_1, conjecture,
% 13.60/13.83    (![A:$i]:
% 13.60/13.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 13.60/13.83       ( ![B:$i]:
% 13.60/13.83         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 13.60/13.83           ( ![C:$i]:
% 13.60/13.83             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 13.60/13.83               ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 13.60/13.83                 ( ![D:$i]:
% 13.60/13.83                   ( ( m1_subset_1 @
% 13.60/13.83                       D @ ( u1_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) =>
% 13.60/13.83                     ( ( ?[E:$i]:
% 13.60/13.83                         ( ( ( E ) = ( D ) ) & 
% 13.60/13.83                           ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) & 
% 13.60/13.83                       ( ?[E:$i]:
% 13.60/13.83                         ( ( ( E ) = ( D ) ) & 
% 13.60/13.83                           ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 13.60/13.83  thf(zf_stmt_0, negated_conjecture,
% 13.60/13.83    (~( ![A:$i]:
% 13.60/13.83        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 13.60/13.83            ( l1_pre_topc @ A ) ) =>
% 13.60/13.83          ( ![B:$i]:
% 13.60/13.83            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 13.60/13.83              ( ![C:$i]:
% 13.60/13.83                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 13.60/13.83                  ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 13.60/13.83                    ( ![D:$i]:
% 13.60/13.83                      ( ( m1_subset_1 @
% 13.60/13.83                          D @ ( u1_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) =>
% 13.60/13.83                        ( ( ?[E:$i]:
% 13.60/13.83                            ( ( ( E ) = ( D ) ) & 
% 13.60/13.83                              ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) & 
% 13.60/13.83                          ( ?[E:$i]:
% 13.60/13.83                            ( ( ( E ) = ( D ) ) & 
% 13.60/13.83                              ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 13.60/13.83    inference('cnf.neg', [status(esa)], [t17_tmap_1])).
% 13.60/13.83  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 13.60/13.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.60/13.83  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 13.60/13.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.60/13.83  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 13.60/13.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.60/13.83  thf(dt_k2_tsep_1, axiom,
% 13.60/13.83    (![A:$i,B:$i,C:$i]:
% 13.60/13.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 13.60/13.83         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 13.60/13.83         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 13.60/13.83       ( ( ~( v2_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) & 
% 13.60/13.83         ( v1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) ) & 
% 13.60/13.83         ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 13.60/13.83  thf('3', plain,
% 13.60/13.83      (![X51 : $i, X52 : $i, X53 : $i]:
% 13.60/13.83         (~ (m1_pre_topc @ X51 @ X52)
% 13.60/13.83          | (v2_struct_0 @ X51)
% 13.60/13.83          | ~ (l1_pre_topc @ X52)
% 13.60/13.83          | (v2_struct_0 @ X52)
% 13.60/13.83          | (v2_struct_0 @ X53)
% 13.60/13.83          | ~ (m1_pre_topc @ X53 @ X52)
% 13.60/13.83          | (m1_pre_topc @ (k2_tsep_1 @ X52 @ X51 @ X53) @ X52))),
% 13.60/13.83      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 13.60/13.83  thf('4', plain,
% 13.60/13.83      (![X0 : $i]:
% 13.60/13.83         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 13.60/13.83          | ~ (m1_pre_topc @ X0 @ sk_A)
% 13.60/13.83          | (v2_struct_0 @ X0)
% 13.60/13.83          | (v2_struct_0 @ sk_A)
% 13.60/13.83          | ~ (l1_pre_topc @ sk_A)
% 13.60/13.83          | (v2_struct_0 @ sk_B))),
% 13.60/13.83      inference('sup-', [status(thm)], ['2', '3'])).
% 13.60/13.83  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 13.60/13.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.60/13.83  thf('6', plain,
% 13.60/13.83      (![X0 : $i]:
% 13.60/13.83         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 13.60/13.83          | ~ (m1_pre_topc @ X0 @ sk_A)
% 13.60/13.83          | (v2_struct_0 @ X0)
% 13.60/13.83          | (v2_struct_0 @ sk_A)
% 13.60/13.83          | (v2_struct_0 @ sk_B))),
% 13.60/13.83      inference('demod', [status(thm)], ['4', '5'])).
% 13.60/13.83  thf('7', plain,
% 13.60/13.83      (((v2_struct_0 @ sk_B)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_C)
% 13.60/13.83        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 13.60/13.83      inference('sup-', [status(thm)], ['1', '6'])).
% 13.60/13.83  thf(dt_k2_subset_1, axiom,
% 13.60/13.83    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 13.60/13.83  thf('8', plain,
% 13.60/13.83      (![X30 : $i]: (m1_subset_1 @ (k2_subset_1 @ X30) @ (k1_zfmisc_1 @ X30))),
% 13.60/13.83      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 13.60/13.83  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 13.60/13.83  thf('9', plain, (![X29 : $i]: ((k2_subset_1 @ X29) = (X29))),
% 13.60/13.83      inference('cnf', [status(esa)], [d4_subset_1])).
% 13.60/13.83  thf('10', plain, (![X30 : $i]: (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X30))),
% 13.60/13.83      inference('demod', [status(thm)], ['8', '9'])).
% 13.60/13.83  thf(dt_k9_subset_1, axiom,
% 13.60/13.83    (![A:$i,B:$i,C:$i]:
% 13.60/13.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 13.60/13.83       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 13.60/13.83  thf('11', plain,
% 13.60/13.83      (![X31 : $i, X32 : $i, X33 : $i]:
% 13.60/13.83         ((m1_subset_1 @ (k9_subset_1 @ X31 @ X32 @ X33) @ (k1_zfmisc_1 @ X31))
% 13.60/13.83          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X31)))),
% 13.60/13.83      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 13.60/13.83  thf('12', plain,
% 13.60/13.83      (![X0 : $i, X1 : $i]:
% 13.60/13.83         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 13.60/13.83      inference('sup-', [status(thm)], ['10', '11'])).
% 13.60/13.83  thf(t3_subset, axiom,
% 13.60/13.83    (![A:$i,B:$i]:
% 13.60/13.83     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 13.60/13.83  thf('13', plain,
% 13.60/13.83      (![X39 : $i, X40 : $i]:
% 13.60/13.83         ((r1_tarski @ X39 @ X40) | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40)))),
% 13.60/13.83      inference('cnf', [status(esa)], [t3_subset])).
% 13.60/13.83  thf('14', plain,
% 13.60/13.83      (![X0 : $i, X1 : $i]: (r1_tarski @ (k9_subset_1 @ X0 @ X1 @ X0) @ X0)),
% 13.60/13.83      inference('sup-', [status(thm)], ['12', '13'])).
% 13.60/13.83  thf('15', plain, (![X30 : $i]: (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X30))),
% 13.60/13.83      inference('demod', [status(thm)], ['8', '9'])).
% 13.60/13.83  thf(redefinition_k9_subset_1, axiom,
% 13.60/13.83    (![A:$i,B:$i,C:$i]:
% 13.60/13.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 13.60/13.83       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 13.60/13.83  thf('16', plain,
% 13.60/13.83      (![X34 : $i, X35 : $i, X36 : $i]:
% 13.60/13.83         (((k9_subset_1 @ X36 @ X34 @ X35) = (k3_xboole_0 @ X34 @ X35))
% 13.60/13.83          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36)))),
% 13.60/13.83      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 13.60/13.83  thf(t12_setfam_1, axiom,
% 13.60/13.83    (![A:$i,B:$i]:
% 13.60/13.83     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 13.60/13.83  thf('17', plain,
% 13.60/13.83      (![X37 : $i, X38 : $i]:
% 13.60/13.83         ((k1_setfam_1 @ (k2_tarski @ X37 @ X38)) = (k3_xboole_0 @ X37 @ X38))),
% 13.60/13.83      inference('cnf', [status(esa)], [t12_setfam_1])).
% 13.60/13.83  thf('18', plain,
% 13.60/13.83      (![X34 : $i, X35 : $i, X36 : $i]:
% 13.60/13.83         (((k9_subset_1 @ X36 @ X34 @ X35)
% 13.60/13.83            = (k1_setfam_1 @ (k2_tarski @ X34 @ X35)))
% 13.60/13.83          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36)))),
% 13.60/13.83      inference('demod', [status(thm)], ['16', '17'])).
% 13.60/13.83  thf('19', plain,
% 13.60/13.83      (![X0 : $i, X1 : $i]:
% 13.60/13.83         ((k9_subset_1 @ X0 @ X1 @ X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 13.60/13.83      inference('sup-', [status(thm)], ['15', '18'])).
% 13.60/13.83  thf('20', plain,
% 13.60/13.83      (![X0 : $i, X1 : $i]:
% 13.60/13.83         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 13.60/13.83      inference('demod', [status(thm)], ['14', '19'])).
% 13.60/13.83  thf('21', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 13.60/13.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.60/13.83  thf('22', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 13.60/13.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.60/13.83  thf('23', plain,
% 13.60/13.83      (![X51 : $i, X52 : $i, X53 : $i]:
% 13.60/13.83         (~ (m1_pre_topc @ X51 @ X52)
% 13.60/13.83          | (v2_struct_0 @ X51)
% 13.60/13.83          | ~ (l1_pre_topc @ X52)
% 13.60/13.83          | (v2_struct_0 @ X52)
% 13.60/13.83          | (v2_struct_0 @ X53)
% 13.60/13.83          | ~ (m1_pre_topc @ X53 @ X52)
% 13.60/13.83          | (v1_pre_topc @ (k2_tsep_1 @ X52 @ X51 @ X53)))),
% 13.60/13.83      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 13.60/13.83  thf('24', plain,
% 13.60/13.83      (![X0 : $i]:
% 13.60/13.83         ((v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 13.60/13.83          | ~ (m1_pre_topc @ X0 @ sk_A)
% 13.60/13.83          | (v2_struct_0 @ X0)
% 13.60/13.83          | (v2_struct_0 @ sk_A)
% 13.60/13.83          | ~ (l1_pre_topc @ sk_A)
% 13.60/13.83          | (v2_struct_0 @ sk_B))),
% 13.60/13.83      inference('sup-', [status(thm)], ['22', '23'])).
% 13.60/13.83  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 13.60/13.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.60/13.83  thf('26', plain,
% 13.60/13.83      (![X0 : $i]:
% 13.60/13.83         ((v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 13.60/13.83          | ~ (m1_pre_topc @ X0 @ sk_A)
% 13.60/13.83          | (v2_struct_0 @ X0)
% 13.60/13.83          | (v2_struct_0 @ sk_A)
% 13.60/13.83          | (v2_struct_0 @ sk_B))),
% 13.60/13.83      inference('demod', [status(thm)], ['24', '25'])).
% 13.60/13.83  thf('27', plain,
% 13.60/13.83      (((v2_struct_0 @ sk_B)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_C)
% 13.60/13.83        | (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 13.60/13.83      inference('sup-', [status(thm)], ['21', '26'])).
% 13.60/13.83  thf('28', plain,
% 13.60/13.83      (((v2_struct_0 @ sk_B)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_C)
% 13.60/13.83        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 13.60/13.83      inference('sup-', [status(thm)], ['1', '6'])).
% 13.60/13.83  thf(d5_tsep_1, axiom,
% 13.60/13.83    (![A:$i]:
% 13.60/13.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 13.60/13.83       ( ![B:$i]:
% 13.60/13.83         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 13.60/13.83           ( ![C:$i]:
% 13.60/13.83             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 13.60/13.83               ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 13.60/13.83                 ( ![D:$i]:
% 13.60/13.83                   ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 13.60/13.83                       ( m1_pre_topc @ D @ A ) ) =>
% 13.60/13.83                     ( ( ( D ) = ( k2_tsep_1 @ A @ B @ C ) ) <=>
% 13.60/13.83                       ( ( u1_struct_0 @ D ) =
% 13.60/13.83                         ( k3_xboole_0 @
% 13.60/13.83                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 13.60/13.83  thf('29', plain,
% 13.60/13.83      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 13.60/13.83         ((v2_struct_0 @ X47)
% 13.60/13.83          | ~ (m1_pre_topc @ X47 @ X48)
% 13.60/13.83          | (r1_tsep_1 @ X47 @ X49)
% 13.60/13.83          | (v2_struct_0 @ X50)
% 13.60/13.83          | ~ (v1_pre_topc @ X50)
% 13.60/13.83          | ~ (m1_pre_topc @ X50 @ X48)
% 13.60/13.83          | ((X50) != (k2_tsep_1 @ X48 @ X47 @ X49))
% 13.60/13.83          | ((u1_struct_0 @ X50)
% 13.60/13.83              = (k3_xboole_0 @ (u1_struct_0 @ X47) @ (u1_struct_0 @ X49)))
% 13.60/13.83          | ~ (m1_pre_topc @ X49 @ X48)
% 13.60/13.83          | (v2_struct_0 @ X49)
% 13.60/13.83          | ~ (l1_pre_topc @ X48)
% 13.60/13.83          | (v2_struct_0 @ X48))),
% 13.60/13.83      inference('cnf', [status(esa)], [d5_tsep_1])).
% 13.60/13.83  thf('30', plain,
% 13.60/13.83      (![X47 : $i, X48 : $i, X49 : $i]:
% 13.60/13.83         ((v2_struct_0 @ X48)
% 13.60/13.83          | ~ (l1_pre_topc @ X48)
% 13.60/13.83          | (v2_struct_0 @ X49)
% 13.60/13.83          | ~ (m1_pre_topc @ X49 @ X48)
% 13.60/13.83          | ((u1_struct_0 @ (k2_tsep_1 @ X48 @ X47 @ X49))
% 13.60/13.83              = (k3_xboole_0 @ (u1_struct_0 @ X47) @ (u1_struct_0 @ X49)))
% 13.60/13.83          | ~ (m1_pre_topc @ (k2_tsep_1 @ X48 @ X47 @ X49) @ X48)
% 13.60/13.83          | ~ (v1_pre_topc @ (k2_tsep_1 @ X48 @ X47 @ X49))
% 13.60/13.83          | (v2_struct_0 @ (k2_tsep_1 @ X48 @ X47 @ X49))
% 13.60/13.83          | (r1_tsep_1 @ X47 @ X49)
% 13.60/13.83          | ~ (m1_pre_topc @ X47 @ X48)
% 13.60/13.83          | (v2_struct_0 @ X47))),
% 13.60/13.83      inference('simplify', [status(thm)], ['29'])).
% 13.60/13.83  thf('31', plain,
% 13.60/13.83      (![X37 : $i, X38 : $i]:
% 13.60/13.83         ((k1_setfam_1 @ (k2_tarski @ X37 @ X38)) = (k3_xboole_0 @ X37 @ X38))),
% 13.60/13.83      inference('cnf', [status(esa)], [t12_setfam_1])).
% 13.60/13.83  thf('32', plain,
% 13.60/13.83      (![X47 : $i, X48 : $i, X49 : $i]:
% 13.60/13.83         ((v2_struct_0 @ X48)
% 13.60/13.83          | ~ (l1_pre_topc @ X48)
% 13.60/13.83          | (v2_struct_0 @ X49)
% 13.60/13.83          | ~ (m1_pre_topc @ X49 @ X48)
% 13.60/13.83          | ((u1_struct_0 @ (k2_tsep_1 @ X48 @ X47 @ X49))
% 13.60/13.83              = (k1_setfam_1 @ 
% 13.60/13.83                 (k2_tarski @ (u1_struct_0 @ X47) @ (u1_struct_0 @ X49))))
% 13.60/13.83          | ~ (m1_pre_topc @ (k2_tsep_1 @ X48 @ X47 @ X49) @ X48)
% 13.60/13.83          | ~ (v1_pre_topc @ (k2_tsep_1 @ X48 @ X47 @ X49))
% 13.60/13.83          | (v2_struct_0 @ (k2_tsep_1 @ X48 @ X47 @ X49))
% 13.60/13.83          | (r1_tsep_1 @ X47 @ X49)
% 13.60/13.83          | ~ (m1_pre_topc @ X47 @ X48)
% 13.60/13.83          | (v2_struct_0 @ X47))),
% 13.60/13.83      inference('demod', [status(thm)], ['30', '31'])).
% 13.60/13.83  thf('33', plain,
% 13.60/13.83      (((v2_struct_0 @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_B)
% 13.60/13.83        | (v2_struct_0 @ sk_B)
% 13.60/13.83        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 13.60/13.83        | (r1_tsep_1 @ sk_B @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 13.60/13.83        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 13.60/13.83        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 13.60/13.83            = (k1_setfam_1 @ 
% 13.60/13.83               (k2_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))
% 13.60/13.83        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_C)
% 13.60/13.83        | ~ (l1_pre_topc @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_A))),
% 13.60/13.83      inference('sup-', [status(thm)], ['28', '32'])).
% 13.60/13.83  thf('34', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 13.60/13.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.60/13.83  thf('35', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 13.60/13.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.60/13.83  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 13.60/13.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.60/13.83  thf('37', plain,
% 13.60/13.83      (((v2_struct_0 @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_B)
% 13.60/13.83        | (v2_struct_0 @ sk_B)
% 13.60/13.83        | (r1_tsep_1 @ sk_B @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 13.60/13.83        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 13.60/13.83        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 13.60/13.83            = (k1_setfam_1 @ 
% 13.60/13.83               (k2_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))
% 13.60/13.83        | (v2_struct_0 @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ sk_A))),
% 13.60/13.83      inference('demod', [status(thm)], ['33', '34', '35', '36'])).
% 13.60/13.83  thf('38', plain,
% 13.60/13.83      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 13.60/13.83          = (k1_setfam_1 @ 
% 13.60/13.83             (k2_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))
% 13.60/13.83        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 13.60/13.83        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 13.60/13.83        | (r1_tsep_1 @ sk_B @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ sk_B)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_C))),
% 13.60/13.83      inference('simplify', [status(thm)], ['37'])).
% 13.60/13.83  thf('39', plain,
% 13.60/13.83      (((v2_struct_0 @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_B)
% 13.60/13.83        | (v2_struct_0 @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_B)
% 13.60/13.83        | (r1_tsep_1 @ sk_B @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 13.60/13.83        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 13.60/13.83            = (k1_setfam_1 @ 
% 13.60/13.83               (k2_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))))),
% 13.60/13.83      inference('sup-', [status(thm)], ['27', '38'])).
% 13.60/13.83  thf('40', plain,
% 13.60/13.83      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 13.60/13.83          = (k1_setfam_1 @ 
% 13.60/13.83             (k2_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))
% 13.60/13.83        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 13.60/13.83        | (r1_tsep_1 @ sk_B @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ sk_B)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_C))),
% 13.60/13.83      inference('simplify', [status(thm)], ['39'])).
% 13.60/13.83  thf('41', plain,
% 13.60/13.83      (![X51 : $i, X52 : $i, X53 : $i]:
% 13.60/13.83         (~ (m1_pre_topc @ X51 @ X52)
% 13.60/13.83          | (v2_struct_0 @ X51)
% 13.60/13.83          | ~ (l1_pre_topc @ X52)
% 13.60/13.83          | (v2_struct_0 @ X52)
% 13.60/13.83          | (v2_struct_0 @ X53)
% 13.60/13.83          | ~ (m1_pre_topc @ X53 @ X52)
% 13.60/13.83          | ~ (v2_struct_0 @ (k2_tsep_1 @ X52 @ X51 @ X53)))),
% 13.60/13.83      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 13.60/13.83  thf('42', plain,
% 13.60/13.83      (((v2_struct_0 @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_B)
% 13.60/13.83        | (r1_tsep_1 @ sk_B @ sk_C)
% 13.60/13.83        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 13.60/13.83            = (k1_setfam_1 @ 
% 13.60/13.83               (k2_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))
% 13.60/13.83        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | ~ (l1_pre_topc @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_B)
% 13.60/13.83        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 13.60/13.83      inference('sup-', [status(thm)], ['40', '41'])).
% 13.60/13.83  thf('43', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 13.60/13.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.60/13.83  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 13.60/13.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.60/13.83  thf('45', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 13.60/13.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.60/13.83  thf('46', plain,
% 13.60/13.83      (((v2_struct_0 @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_B)
% 13.60/13.83        | (r1_tsep_1 @ sk_B @ sk_C)
% 13.60/13.83        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 13.60/13.83            = (k1_setfam_1 @ 
% 13.60/13.83               (k2_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))
% 13.60/13.83        | (v2_struct_0 @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_B))),
% 13.60/13.83      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 13.60/13.83  thf('47', plain,
% 13.60/13.83      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 13.60/13.83          = (k1_setfam_1 @ 
% 13.60/13.83             (k2_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))
% 13.60/13.83        | (r1_tsep_1 @ sk_B @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ sk_B)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_C))),
% 13.60/13.83      inference('simplify', [status(thm)], ['46'])).
% 13.60/13.83  thf(t4_tsep_1, axiom,
% 13.60/13.83    (![A:$i]:
% 13.60/13.83     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 13.60/13.83       ( ![B:$i]:
% 13.60/13.83         ( ( m1_pre_topc @ B @ A ) =>
% 13.60/13.83           ( ![C:$i]:
% 13.60/13.83             ( ( m1_pre_topc @ C @ A ) =>
% 13.60/13.83               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 13.60/13.83                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 13.60/13.83  thf('48', plain,
% 13.60/13.83      (![X54 : $i, X55 : $i, X56 : $i]:
% 13.60/13.83         (~ (m1_pre_topc @ X54 @ X55)
% 13.60/13.83          | ~ (r1_tarski @ (u1_struct_0 @ X54) @ (u1_struct_0 @ X56))
% 13.60/13.83          | (m1_pre_topc @ X54 @ X56)
% 13.60/13.83          | ~ (m1_pre_topc @ X56 @ X55)
% 13.60/13.83          | ~ (l1_pre_topc @ X55)
% 13.60/13.83          | ~ (v2_pre_topc @ X55))),
% 13.60/13.83      inference('cnf', [status(esa)], [t4_tsep_1])).
% 13.60/13.83  thf('49', plain,
% 13.60/13.83      (![X0 : $i, X1 : $i]:
% 13.60/13.83         (~ (r1_tarski @ 
% 13.60/13.83             (k1_setfam_1 @ 
% 13.60/13.83              (k2_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))) @ 
% 13.60/13.83             (u1_struct_0 @ X0))
% 13.60/13.83          | (v2_struct_0 @ sk_C)
% 13.60/13.83          | (v2_struct_0 @ sk_A)
% 13.60/13.83          | (v2_struct_0 @ sk_B)
% 13.60/13.83          | (r1_tsep_1 @ sk_B @ sk_C)
% 13.60/13.83          | ~ (v2_pre_topc @ X1)
% 13.60/13.83          | ~ (l1_pre_topc @ X1)
% 13.60/13.83          | ~ (m1_pre_topc @ X0 @ X1)
% 13.60/13.83          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 13.60/13.83          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X1))),
% 13.60/13.83      inference('sup-', [status(thm)], ['47', '48'])).
% 13.60/13.83  thf('50', plain,
% 13.60/13.83      (![X0 : $i]:
% 13.60/13.83         (~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 13.60/13.83          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C)
% 13.60/13.83          | ~ (m1_pre_topc @ sk_C @ X0)
% 13.60/13.83          | ~ (l1_pre_topc @ X0)
% 13.60/13.83          | ~ (v2_pre_topc @ X0)
% 13.60/13.83          | (r1_tsep_1 @ sk_B @ sk_C)
% 13.60/13.83          | (v2_struct_0 @ sk_B)
% 13.60/13.83          | (v2_struct_0 @ sk_A)
% 13.60/13.83          | (v2_struct_0 @ sk_C))),
% 13.60/13.83      inference('sup-', [status(thm)], ['20', '49'])).
% 13.60/13.83  thf('51', plain,
% 13.60/13.83      (((v2_struct_0 @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_B)
% 13.60/13.83        | (v2_struct_0 @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_B)
% 13.60/13.83        | (r1_tsep_1 @ sk_B @ sk_C)
% 13.60/13.83        | ~ (v2_pre_topc @ sk_A)
% 13.60/13.83        | ~ (l1_pre_topc @ sk_A)
% 13.60/13.83        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 13.60/13.83        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C))),
% 13.60/13.83      inference('sup-', [status(thm)], ['7', '50'])).
% 13.60/13.83  thf('52', plain, ((v2_pre_topc @ sk_A)),
% 13.60/13.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.60/13.83  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 13.60/13.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.60/13.83  thf('54', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 13.60/13.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.60/13.83  thf('55', plain,
% 13.60/13.83      (((v2_struct_0 @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_B)
% 13.60/13.83        | (v2_struct_0 @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_B)
% 13.60/13.83        | (r1_tsep_1 @ sk_B @ sk_C)
% 13.60/13.83        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C))),
% 13.60/13.83      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 13.60/13.83  thf('56', plain,
% 13.60/13.83      (((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C)
% 13.60/13.83        | (r1_tsep_1 @ sk_B @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ sk_B)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_C))),
% 13.60/13.83      inference('simplify', [status(thm)], ['55'])).
% 13.60/13.83  thf('57', plain,
% 13.60/13.83      ((m1_subset_1 @ sk_D @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 13.60/13.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.60/13.83  thf(t55_pre_topc, axiom,
% 13.60/13.83    (![A:$i]:
% 13.60/13.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 13.60/13.83       ( ![B:$i]:
% 13.60/13.83         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 13.60/13.83           ( ![C:$i]:
% 13.60/13.83             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 13.60/13.83               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 13.60/13.83  thf('58', plain,
% 13.60/13.83      (![X44 : $i, X45 : $i, X46 : $i]:
% 13.60/13.83         ((v2_struct_0 @ X44)
% 13.60/13.83          | ~ (m1_pre_topc @ X44 @ X45)
% 13.60/13.83          | (m1_subset_1 @ X46 @ (u1_struct_0 @ X45))
% 13.60/13.83          | ~ (m1_subset_1 @ X46 @ (u1_struct_0 @ X44))
% 13.60/13.83          | ~ (l1_pre_topc @ X45)
% 13.60/13.83          | (v2_struct_0 @ X45))),
% 13.60/13.83      inference('cnf', [status(esa)], [t55_pre_topc])).
% 13.60/13.83  thf('59', plain,
% 13.60/13.83      (![X0 : $i]:
% 13.60/13.83         ((v2_struct_0 @ X0)
% 13.60/13.83          | ~ (l1_pre_topc @ X0)
% 13.60/13.83          | (m1_subset_1 @ sk_D @ (u1_struct_0 @ X0))
% 13.60/13.83          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 13.60/13.83          | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 13.60/13.83      inference('sup-', [status(thm)], ['57', '58'])).
% 13.60/13.83  thf('60', plain,
% 13.60/13.83      (((v2_struct_0 @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_B)
% 13.60/13.83        | (r1_tsep_1 @ sk_B @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 13.60/13.83        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))
% 13.60/13.83        | ~ (l1_pre_topc @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ sk_C))),
% 13.60/13.83      inference('sup-', [status(thm)], ['56', '59'])).
% 13.60/13.83  thf('61', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 13.60/13.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.60/13.83  thf(dt_m1_pre_topc, axiom,
% 13.60/13.83    (![A:$i]:
% 13.60/13.83     ( ( l1_pre_topc @ A ) =>
% 13.60/13.83       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 13.60/13.83  thf('62', plain,
% 13.60/13.83      (![X42 : $i, X43 : $i]:
% 13.60/13.83         (~ (m1_pre_topc @ X42 @ X43)
% 13.60/13.83          | (l1_pre_topc @ X42)
% 13.60/13.83          | ~ (l1_pre_topc @ X43))),
% 13.60/13.83      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 13.60/13.83  thf('63', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 13.60/13.83      inference('sup-', [status(thm)], ['61', '62'])).
% 13.60/13.83  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 13.60/13.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.60/13.83  thf('65', plain, ((l1_pre_topc @ sk_C)),
% 13.60/13.83      inference('demod', [status(thm)], ['63', '64'])).
% 13.60/13.83  thf('66', plain,
% 13.60/13.83      (((v2_struct_0 @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_B)
% 13.60/13.83        | (r1_tsep_1 @ sk_B @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 13.60/13.83        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))
% 13.60/13.83        | (v2_struct_0 @ sk_C))),
% 13.60/13.83      inference('demod', [status(thm)], ['60', '65'])).
% 13.60/13.83  thf('67', plain,
% 13.60/13.83      (((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))
% 13.60/13.83        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 13.60/13.83        | (r1_tsep_1 @ sk_B @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ sk_B)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_C))),
% 13.60/13.83      inference('simplify', [status(thm)], ['66'])).
% 13.60/13.83  thf('68', plain,
% 13.60/13.83      (![X51 : $i, X52 : $i, X53 : $i]:
% 13.60/13.83         (~ (m1_pre_topc @ X51 @ X52)
% 13.60/13.83          | (v2_struct_0 @ X51)
% 13.60/13.83          | ~ (l1_pre_topc @ X52)
% 13.60/13.83          | (v2_struct_0 @ X52)
% 13.60/13.83          | (v2_struct_0 @ X53)
% 13.60/13.83          | ~ (m1_pre_topc @ X53 @ X52)
% 13.60/13.83          | ~ (v2_struct_0 @ (k2_tsep_1 @ X52 @ X51 @ X53)))),
% 13.60/13.83      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 13.60/13.83  thf('69', plain,
% 13.60/13.83      (((v2_struct_0 @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_B)
% 13.60/13.83        | (r1_tsep_1 @ sk_B @ sk_C)
% 13.60/13.83        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))
% 13.60/13.83        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | ~ (l1_pre_topc @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_B)
% 13.60/13.83        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 13.60/13.83      inference('sup-', [status(thm)], ['67', '68'])).
% 13.60/13.83  thf('70', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 13.60/13.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.60/13.83  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 13.60/13.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.60/13.83  thf('72', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 13.60/13.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.60/13.83  thf('73', plain,
% 13.60/13.83      (((v2_struct_0 @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_B)
% 13.60/13.83        | (r1_tsep_1 @ sk_B @ sk_C)
% 13.60/13.83        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))
% 13.60/13.83        | (v2_struct_0 @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_B))),
% 13.60/13.83      inference('demod', [status(thm)], ['69', '70', '71', '72'])).
% 13.60/13.83  thf('74', plain,
% 13.60/13.83      (((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))
% 13.60/13.83        | (r1_tsep_1 @ sk_B @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ sk_B)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_C))),
% 13.60/13.83      inference('simplify', [status(thm)], ['73'])).
% 13.60/13.83  thf('75', plain,
% 13.60/13.83      (![X57 : $i, X58 : $i]:
% 13.60/13.83         (~ (m1_subset_1 @ X57 @ (u1_struct_0 @ sk_B))
% 13.60/13.83          | ((X57) != (sk_D))
% 13.60/13.83          | ~ (m1_subset_1 @ X58 @ (u1_struct_0 @ sk_C))
% 13.60/13.83          | ((X58) != (sk_D)))),
% 13.60/13.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.60/13.83  thf('76', plain,
% 13.60/13.83      ((![X58 : $i]:
% 13.60/13.83          (((X58) != (sk_D)) | ~ (m1_subset_1 @ X58 @ (u1_struct_0 @ sk_C))))
% 13.60/13.83         <= ((![X58 : $i]:
% 13.60/13.83                (((X58) != (sk_D))
% 13.60/13.83                 | ~ (m1_subset_1 @ X58 @ (u1_struct_0 @ sk_C)))))),
% 13.60/13.83      inference('split', [status(esa)], ['75'])).
% 13.60/13.83  thf('77', plain,
% 13.60/13.83      ((~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 13.60/13.83         <= ((![X58 : $i]:
% 13.60/13.83                (((X58) != (sk_D))
% 13.60/13.83                 | ~ (m1_subset_1 @ X58 @ (u1_struct_0 @ sk_C)))))),
% 13.60/13.83      inference('simplify', [status(thm)], ['76'])).
% 13.60/13.83  thf('78', plain,
% 13.60/13.83      (((v2_struct_0 @ sk_B)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_C)
% 13.60/13.83        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 13.60/13.83      inference('sup-', [status(thm)], ['1', '6'])).
% 13.60/13.83  thf(t17_xboole_1, axiom,
% 13.60/13.83    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 13.60/13.83  thf('79', plain,
% 13.60/13.83      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 13.60/13.83      inference('cnf', [status(esa)], [t17_xboole_1])).
% 13.60/13.83  thf('80', plain,
% 13.60/13.83      (![X37 : $i, X38 : $i]:
% 13.60/13.83         ((k1_setfam_1 @ (k2_tarski @ X37 @ X38)) = (k3_xboole_0 @ X37 @ X38))),
% 13.60/13.83      inference('cnf', [status(esa)], [t12_setfam_1])).
% 13.60/13.83  thf('81', plain,
% 13.60/13.83      (![X0 : $i, X1 : $i]:
% 13.60/13.83         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0)),
% 13.60/13.83      inference('demod', [status(thm)], ['79', '80'])).
% 13.60/13.83  thf('82', plain,
% 13.60/13.83      (![X0 : $i, X1 : $i]:
% 13.60/13.83         (~ (r1_tarski @ 
% 13.60/13.83             (k1_setfam_1 @ 
% 13.60/13.83              (k2_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))) @ 
% 13.60/13.83             (u1_struct_0 @ X0))
% 13.60/13.83          | (v2_struct_0 @ sk_C)
% 13.60/13.83          | (v2_struct_0 @ sk_A)
% 13.60/13.83          | (v2_struct_0 @ sk_B)
% 13.60/13.83          | (r1_tsep_1 @ sk_B @ sk_C)
% 13.60/13.83          | ~ (v2_pre_topc @ X1)
% 13.60/13.83          | ~ (l1_pre_topc @ X1)
% 13.60/13.83          | ~ (m1_pre_topc @ X0 @ X1)
% 13.60/13.83          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 13.60/13.83          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X1))),
% 13.60/13.83      inference('sup-', [status(thm)], ['47', '48'])).
% 13.60/13.83  thf('83', plain,
% 13.60/13.83      (![X0 : $i]:
% 13.60/13.83         (~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 13.60/13.83          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B)
% 13.60/13.83          | ~ (m1_pre_topc @ sk_B @ X0)
% 13.60/13.83          | ~ (l1_pre_topc @ X0)
% 13.60/13.83          | ~ (v2_pre_topc @ X0)
% 13.60/13.83          | (r1_tsep_1 @ sk_B @ sk_C)
% 13.60/13.83          | (v2_struct_0 @ sk_B)
% 13.60/13.83          | (v2_struct_0 @ sk_A)
% 13.60/13.83          | (v2_struct_0 @ sk_C))),
% 13.60/13.83      inference('sup-', [status(thm)], ['81', '82'])).
% 13.60/13.83  thf('84', plain,
% 13.60/13.83      (((v2_struct_0 @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_B)
% 13.60/13.83        | (v2_struct_0 @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_B)
% 13.60/13.83        | (r1_tsep_1 @ sk_B @ sk_C)
% 13.60/13.83        | ~ (v2_pre_topc @ sk_A)
% 13.60/13.83        | ~ (l1_pre_topc @ sk_A)
% 13.60/13.83        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 13.60/13.83        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B))),
% 13.60/13.83      inference('sup-', [status(thm)], ['78', '83'])).
% 13.60/13.83  thf('85', plain, ((v2_pre_topc @ sk_A)),
% 13.60/13.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.60/13.83  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 13.60/13.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.60/13.83  thf('87', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 13.60/13.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.60/13.83  thf('88', plain,
% 13.60/13.83      (((v2_struct_0 @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_B)
% 13.60/13.83        | (v2_struct_0 @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_B)
% 13.60/13.83        | (r1_tsep_1 @ sk_B @ sk_C)
% 13.60/13.83        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B))),
% 13.60/13.83      inference('demod', [status(thm)], ['84', '85', '86', '87'])).
% 13.60/13.83  thf('89', plain,
% 13.60/13.83      (((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B)
% 13.60/13.83        | (r1_tsep_1 @ sk_B @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ sk_B)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_C))),
% 13.60/13.83      inference('simplify', [status(thm)], ['88'])).
% 13.60/13.83  thf('90', plain,
% 13.60/13.83      (![X0 : $i]:
% 13.60/13.83         ((v2_struct_0 @ X0)
% 13.60/13.83          | ~ (l1_pre_topc @ X0)
% 13.60/13.83          | (m1_subset_1 @ sk_D @ (u1_struct_0 @ X0))
% 13.60/13.83          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0)
% 13.60/13.83          | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 13.60/13.83      inference('sup-', [status(thm)], ['57', '58'])).
% 13.60/13.83  thf('91', plain,
% 13.60/13.83      (((v2_struct_0 @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_B)
% 13.60/13.83        | (r1_tsep_1 @ sk_B @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 13.60/13.83        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))
% 13.60/13.83        | ~ (l1_pre_topc @ sk_B)
% 13.60/13.83        | (v2_struct_0 @ sk_B))),
% 13.60/13.83      inference('sup-', [status(thm)], ['89', '90'])).
% 13.60/13.83  thf('92', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 13.60/13.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.60/13.83  thf('93', plain,
% 13.60/13.83      (![X42 : $i, X43 : $i]:
% 13.60/13.83         (~ (m1_pre_topc @ X42 @ X43)
% 13.60/13.83          | (l1_pre_topc @ X42)
% 13.60/13.83          | ~ (l1_pre_topc @ X43))),
% 13.60/13.83      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 13.60/13.83  thf('94', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 13.60/13.83      inference('sup-', [status(thm)], ['92', '93'])).
% 13.60/13.83  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 13.60/13.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.60/13.83  thf('96', plain, ((l1_pre_topc @ sk_B)),
% 13.60/13.83      inference('demod', [status(thm)], ['94', '95'])).
% 13.60/13.83  thf('97', plain,
% 13.60/13.83      (((v2_struct_0 @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_B)
% 13.60/13.83        | (r1_tsep_1 @ sk_B @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 13.60/13.83        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))
% 13.60/13.83        | (v2_struct_0 @ sk_B))),
% 13.60/13.83      inference('demod', [status(thm)], ['91', '96'])).
% 13.60/13.83  thf('98', plain,
% 13.60/13.83      (((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))
% 13.60/13.83        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 13.60/13.83        | (r1_tsep_1 @ sk_B @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ sk_B)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_C))),
% 13.60/13.83      inference('simplify', [status(thm)], ['97'])).
% 13.60/13.83  thf('99', plain,
% 13.60/13.83      (![X51 : $i, X52 : $i, X53 : $i]:
% 13.60/13.83         (~ (m1_pre_topc @ X51 @ X52)
% 13.60/13.83          | (v2_struct_0 @ X51)
% 13.60/13.83          | ~ (l1_pre_topc @ X52)
% 13.60/13.83          | (v2_struct_0 @ X52)
% 13.60/13.83          | (v2_struct_0 @ X53)
% 13.60/13.83          | ~ (m1_pre_topc @ X53 @ X52)
% 13.60/13.83          | ~ (v2_struct_0 @ (k2_tsep_1 @ X52 @ X51 @ X53)))),
% 13.60/13.83      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 13.60/13.83  thf('100', plain,
% 13.60/13.83      (((v2_struct_0 @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_B)
% 13.60/13.83        | (r1_tsep_1 @ sk_B @ sk_C)
% 13.60/13.83        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))
% 13.60/13.83        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | ~ (l1_pre_topc @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_B)
% 13.60/13.83        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 13.60/13.83      inference('sup-', [status(thm)], ['98', '99'])).
% 13.60/13.83  thf('101', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 13.60/13.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.60/13.83  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 13.60/13.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.60/13.83  thf('103', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 13.60/13.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.60/13.83  thf('104', plain,
% 13.60/13.83      (((v2_struct_0 @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_B)
% 13.60/13.83        | (r1_tsep_1 @ sk_B @ sk_C)
% 13.60/13.83        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))
% 13.60/13.83        | (v2_struct_0 @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_B))),
% 13.60/13.83      inference('demod', [status(thm)], ['100', '101', '102', '103'])).
% 13.60/13.83  thf('105', plain,
% 13.60/13.83      (((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))
% 13.60/13.83        | (r1_tsep_1 @ sk_B @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ sk_B)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_C))),
% 13.60/13.83      inference('simplify', [status(thm)], ['104'])).
% 13.60/13.83  thf('106', plain,
% 13.60/13.83      ((![X57 : $i]:
% 13.60/13.83          (((X57) != (sk_D)) | ~ (m1_subset_1 @ X57 @ (u1_struct_0 @ sk_B))))
% 13.60/13.83         <= ((![X57 : $i]:
% 13.60/13.83                (((X57) != (sk_D))
% 13.60/13.83                 | ~ (m1_subset_1 @ X57 @ (u1_struct_0 @ sk_B)))))),
% 13.60/13.83      inference('split', [status(esa)], ['75'])).
% 13.60/13.83  thf('107', plain,
% 13.60/13.83      ((~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B)))
% 13.60/13.83         <= ((![X57 : $i]:
% 13.60/13.83                (((X57) != (sk_D))
% 13.60/13.83                 | ~ (m1_subset_1 @ X57 @ (u1_struct_0 @ sk_B)))))),
% 13.60/13.83      inference('simplify', [status(thm)], ['106'])).
% 13.60/13.83  thf('108', plain,
% 13.60/13.83      ((((v2_struct_0 @ sk_C)
% 13.60/13.83         | (v2_struct_0 @ sk_A)
% 13.60/13.83         | (v2_struct_0 @ sk_B)
% 13.60/13.83         | (r1_tsep_1 @ sk_B @ sk_C)))
% 13.60/13.83         <= ((![X57 : $i]:
% 13.60/13.83                (((X57) != (sk_D))
% 13.60/13.83                 | ~ (m1_subset_1 @ X57 @ (u1_struct_0 @ sk_B)))))),
% 13.60/13.83      inference('sup-', [status(thm)], ['105', '107'])).
% 13.60/13.83  thf('109', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 13.60/13.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.60/13.83  thf('110', plain,
% 13.60/13.83      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C)))
% 13.60/13.83         <= ((![X57 : $i]:
% 13.60/13.83                (((X57) != (sk_D))
% 13.60/13.83                 | ~ (m1_subset_1 @ X57 @ (u1_struct_0 @ sk_B)))))),
% 13.60/13.83      inference('sup-', [status(thm)], ['108', '109'])).
% 13.60/13.83  thf('111', plain, (~ (v2_struct_0 @ sk_B)),
% 13.60/13.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.60/13.83  thf('112', plain,
% 13.60/13.83      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A)))
% 13.60/13.83         <= ((![X57 : $i]:
% 13.60/13.83                (((X57) != (sk_D))
% 13.60/13.83                 | ~ (m1_subset_1 @ X57 @ (u1_struct_0 @ sk_B)))))),
% 13.60/13.83      inference('clc', [status(thm)], ['110', '111'])).
% 13.60/13.83  thf('113', plain, (~ (v2_struct_0 @ sk_C)),
% 13.60/13.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.60/13.83  thf('114', plain,
% 13.60/13.83      (((v2_struct_0 @ sk_A))
% 13.60/13.83         <= ((![X57 : $i]:
% 13.60/13.83                (((X57) != (sk_D))
% 13.60/13.83                 | ~ (m1_subset_1 @ X57 @ (u1_struct_0 @ sk_B)))))),
% 13.60/13.83      inference('clc', [status(thm)], ['112', '113'])).
% 13.60/13.83  thf('115', plain, (~ (v2_struct_0 @ sk_A)),
% 13.60/13.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.60/13.83  thf('116', plain,
% 13.60/13.83      (~
% 13.60/13.83       (![X57 : $i]:
% 13.60/13.83          (((X57) != (sk_D)) | ~ (m1_subset_1 @ X57 @ (u1_struct_0 @ sk_B))))),
% 13.60/13.83      inference('sup-', [status(thm)], ['114', '115'])).
% 13.60/13.83  thf('117', plain,
% 13.60/13.83      ((![X58 : $i]:
% 13.60/13.83          (((X58) != (sk_D)) | ~ (m1_subset_1 @ X58 @ (u1_struct_0 @ sk_C)))) | 
% 13.60/13.83       (![X57 : $i]:
% 13.60/13.83          (((X57) != (sk_D)) | ~ (m1_subset_1 @ X57 @ (u1_struct_0 @ sk_B))))),
% 13.60/13.83      inference('split', [status(esa)], ['75'])).
% 13.60/13.83  thf('118', plain,
% 13.60/13.83      ((![X58 : $i]:
% 13.60/13.83          (((X58) != (sk_D)) | ~ (m1_subset_1 @ X58 @ (u1_struct_0 @ sk_C))))),
% 13.60/13.83      inference('sat_resolution*', [status(thm)], ['116', '117'])).
% 13.60/13.83  thf('119', plain, (~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))),
% 13.60/13.83      inference('simpl_trail', [status(thm)], ['77', '118'])).
% 13.60/13.83  thf('120', plain,
% 13.60/13.83      (((v2_struct_0 @ sk_C)
% 13.60/13.83        | (v2_struct_0 @ sk_A)
% 13.60/13.83        | (v2_struct_0 @ sk_B)
% 13.60/13.83        | (r1_tsep_1 @ sk_B @ sk_C))),
% 13.60/13.83      inference('sup-', [status(thm)], ['74', '119'])).
% 13.60/13.83  thf('121', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 13.60/13.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.60/13.83  thf('122', plain,
% 13.60/13.83      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 13.60/13.83      inference('sup-', [status(thm)], ['120', '121'])).
% 13.60/13.83  thf('123', plain, (~ (v2_struct_0 @ sk_B)),
% 13.60/13.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.60/13.83  thf('124', plain, (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 13.60/13.83      inference('clc', [status(thm)], ['122', '123'])).
% 13.60/13.83  thf('125', plain, (~ (v2_struct_0 @ sk_C)),
% 13.60/13.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.60/13.83  thf('126', plain, ((v2_struct_0 @ sk_A)),
% 13.60/13.83      inference('clc', [status(thm)], ['124', '125'])).
% 13.60/13.83  thf('127', plain, ($false), inference('demod', [status(thm)], ['0', '126'])).
% 13.60/13.83  
% 13.60/13.83  % SZS output end Refutation
% 13.60/13.83  
% 13.60/13.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
