%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zDiepRWL9q

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:46 EST 2020

% Result     : Theorem 4.26s
% Output     : Refutation 4.35s
% Verified   : 
% Statistics : Number of formulae       :  270 (4070 expanded)
%              Number of leaves         :   52 (1175 expanded)
%              Depth                    :   35
%              Number of atoms          : 2606 (133517 expanded)
%              Number of equality atoms :   65 (3569 expanded)
%              Maximal formula depth    :   23 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_borsuk_1_type,type,(
    v3_borsuk_1: $i > $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_tex_2_type,type,(
    v4_tex_2: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('1',plain,(
    ! [X29: $i] :
      ( ( m1_pre_topc @ X29 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('5',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t26_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( v2_tex_2 @ C @ A )
                <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( v2_struct_0 @ X36 )
      | ~ ( m1_pre_topc @ X36 @ X37 )
      | ( X38
       != ( u1_struct_0 @ X36 ) )
      | ~ ( v1_tdlat_3 @ X36 )
      | ( v2_tex_2 @ X38 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( l1_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t26_tex_2])).

thf('7',plain,(
    ! [X36: $i,X37: $i] :
      ( ( v2_struct_0 @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X36 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ X36 ) @ X37 )
      | ~ ( v1_tdlat_3 @ X36 )
      | ~ ( m1_pre_topc @ X36 @ X37 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t65_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ~ ( ( v2_tex_2 @ B @ A )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ~ ( ( r1_tarski @ B @ C )
                      & ( v3_tex_2 @ C @ A ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( v2_tex_2 @ X41 @ X42 )
      | ( m1_subset_1 @ ( sk_C @ X41 @ X42 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v3_tdlat_3 @ X42 )
      | ~ ( v2_pre_topc @ X42 )
      | ( v2_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( r1_tarski @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('20',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('21',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( v2_tex_2 @ X41 @ X42 )
      | ( r1_tarski @ X41 @ ( sk_C @ X41 @ X42 ) )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v3_tdlat_3 @ X42 )
      | ~ ( v2_pre_topc @ X42 )
      | ( v2_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('30',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('31',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( v2_tex_2 @ X41 @ X42 )
      | ( v3_tex_2 @ ( sk_C @ X41 @ X42 ) @ X42 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v3_tdlat_3 @ X42 )
      | ~ ( v2_pre_topc @ X42 )
      | ( v2_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( v3_tex_2 @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ( v3_tex_2 @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t62_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tex_2 @ B @ A )
           => ( v1_tops_1 @ B @ A ) ) ) ) )).

thf('38',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( v1_tops_1 @ X39 @ X40 )
      | ~ ( v3_tex_2 @ X39 @ X40 )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v3_tdlat_3 @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t62_tex_2])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(d2_tops_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( u1_struct_0 @ A ) ) ) ) ) )).

thf('43',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( v1_tops_1 @ X34 @ X35 )
      | ( ( k2_pre_topc @ X35 @ X34 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('48',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('49',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v1_tops_1 @ X25 @ X26 )
      | ( ( k2_pre_topc @ X26 @ X25 )
        = ( k2_struct_0 @ X26 ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['55','56'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('58',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ X23 )
      | ( ( k6_domain_1 @ X23 @ X24 )
        = ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('59',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('61',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('62',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( v2_tex_2 @ X41 @ X42 )
      | ( m1_subset_1 @ ( sk_C @ X41 @ X42 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v3_tdlat_3 @ X42 )
      | ~ ( v2_pre_topc @ X42 )
      | ( v2_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('71',plain,(
    ! [X36: $i,X37: $i] :
      ( ( v2_struct_0 @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X36 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ X36 ) @ X37 )
      | ~ ( v1_tdlat_3 @ X36 )
      | ~ ( m1_pre_topc @ X36 @ X37 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_B )
    | ( v2_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc35_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( ~ ( v2_struct_0 @ B )
              & ( v4_tex_2 @ B @ A ) )
           => ( ~ ( v2_struct_0 @ B )
              & ( v1_tdlat_3 @ B ) ) ) ) ) )).

thf('75',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_pre_topc @ X32 @ X33 )
      | ( v1_tdlat_3 @ X32 )
      | ~ ( v4_tex_2 @ X32 @ X33 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[cc35_tex_2])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v4_tex_2 @ sk_B @ sk_A )
    | ( v1_tdlat_3 @ sk_B ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v4_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_tdlat_3 @ sk_B ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( v1_tdlat_3 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_tdlat_3 @ sk_B ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73','83','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v2_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['66','67','68','69','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    m1_subset_1 @ ( sk_C @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v1_tops_1 @ X25 @ X26 )
      | ( ( k2_pre_topc @ X26 @ X25 )
        = ( k2_struct_0 @ X26 ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('94',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( sk_C @ ( u1_struct_0 @ sk_B ) @ sk_A ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( sk_C @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( sk_C @ ( u1_struct_0 @ sk_B ) @ sk_A ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( sk_C @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    m1_subset_1 @ ( sk_C @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('98',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( v1_tops_1 @ X34 @ X35 )
      | ( ( k2_pre_topc @ X35 @ X34 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('99',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( sk_C @ ( u1_struct_0 @ sk_B ) @ sk_A ) )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( sk_C @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( sk_C @ ( u1_struct_0 @ sk_B ) @ sk_A ) )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( sk_C @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    m1_subset_1 @ ( sk_C @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('103',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( v1_tops_1 @ X39 @ X40 )
      | ~ ( v3_tex_2 @ X39 @ X40 )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v3_tdlat_3 @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t62_tex_2])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tex_2 @ ( sk_C @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A )
    | ( v1_tops_1 @ ( sk_C @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('109',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( v2_tex_2 @ X41 @ X42 )
      | ( v3_tex_2 @ ( sk_C @ X41 @ X42 ) @ X42 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v3_tdlat_3 @ X42 )
      | ~ ( v2_pre_topc @ X42 )
      | ( v2_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ ( sk_C @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v2_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['87','88'])).

thf('115',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v3_tex_2 @ ( sk_C @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['110','111','112','113','114'])).

thf('116',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v3_tex_2 @ ( sk_C @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tops_1 @ ( sk_C @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['104','105','106','107','117'])).

thf('119',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v1_tops_1 @ ( sk_C @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,
    ( ( k2_pre_topc @ sk_A @ ( sk_C @ ( u1_struct_0 @ sk_B ) @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['101','120'])).

thf('122',plain,(
    v1_tops_1 @ ( sk_C @ ( u1_struct_0 @ sk_B ) @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['118','119'])).

thf('123',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['96','121','122'])).

thf('124',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['96','121','122'])).

thf('125',plain,
    ( ( ( k6_domain_1 @ ( k2_struct_0 @ sk_A ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','123','124'])).

thf('126',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ X23 )
      | ( ( k6_domain_1 @ X23 @ X24 )
        = ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('129',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('131',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ X21 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('132',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['129','132'])).

thf('134',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('135',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['126','136'])).

thf('138',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['96','121','122'])).

thf('141',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('143',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('144',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( v2_struct_0 @ X43 )
      | ~ ( v4_tex_2 @ X43 @ X44 )
      | ~ ( m1_pre_topc @ X43 @ X44 )
      | ~ ( v3_borsuk_1 @ X45 @ X44 @ X43 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ( X46 != X47 )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X43 ) @ X45 @ X46 )
        = ( k2_pre_topc @ X44 @ X47 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X43 ) ) ) )
      | ~ ( v5_pre_topc @ X45 @ X44 @ X43 )
      | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X43 ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( l1_pre_topc @ X44 )
      | ~ ( v3_tdlat_3 @ X44 )
      | ~ ( v2_pre_topc @ X44 )
      | ( v2_struct_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t76_tex_2])).

thf('145',plain,(
    ! [X43: $i,X44: $i,X45: $i,X47: $i] :
      ( ( v2_struct_0 @ X44 )
      | ~ ( v2_pre_topc @ X44 )
      | ~ ( v3_tdlat_3 @ X44 )
      | ~ ( l1_pre_topc @ X44 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X43 ) )
      | ~ ( v5_pre_topc @ X45 @ X44 @ X43 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X43 ) ) ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X43 ) @ X45 @ X47 )
        = ( k2_pre_topc @ X44 @ X47 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( v3_borsuk_1 @ X45 @ X44 @ X43 )
      | ~ ( m1_pre_topc @ X43 @ X44 )
      | ~ ( v4_tex_2 @ X43 @ X44 )
      | ( v2_struct_0 @ X43 ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v4_tex_2 @ sk_B @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ~ ( v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['143','145'])).

thf('147',plain,(
    v4_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v5_pre_topc @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['146','147','148','149','150','151','152','153','154','155'])).

thf('157',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['96','121','122'])).

thf('158',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['96','121','122'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['156','157','158'])).

thf('160',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['142','159'])).

thf('161',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['141','160'])).

thf('162',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('164',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['163','166'])).

thf('168',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['96','121','122'])).

thf('169',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['96','121','122'])).

thf('170',plain,
    ( ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( k2_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['167','168','169'])).

thf('171',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( k2_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['162','170'])).

thf('172',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( k2_struct_0 @ sk_A ) @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['125','172'])).

thf('174',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( v3_tdlat_3 @ sk_B )
    | ~ ( v1_tdlat_3 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['54','174'])).

thf('176',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('177',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('178',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['178','179','180'])).

thf('182',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc18_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_tdlat_3 @ B )
           => ( v3_tdlat_3 @ B ) ) ) ) )).

thf('183',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( v3_tdlat_3 @ X30 )
      | ~ ( v1_tdlat_3 @ X30 )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[cc18_tex_2])).

thf('184',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_B )
    | ( v3_tdlat_3 @ sk_B ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_B )
    | ( v3_tdlat_3 @ sk_B ) ),
    inference(demod,[status(thm)],['184','185'])).

thf('187',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,
    ( ( v3_tdlat_3 @ sk_B )
    | ~ ( v1_tdlat_3 @ sk_B ) ),
    inference(clc,[status(thm)],['186','187'])).

thf('189',plain,(
    v1_tdlat_3 @ sk_B ),
    inference(clc,[status(thm)],['81','82'])).

thf('190',plain,(
    v3_tdlat_3 @ sk_B ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,(
    v1_tdlat_3 @ sk_B ),
    inference(clc,[status(thm)],['81','82'])).

thf('192',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('193',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( l1_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('194',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['194','195'])).

thf('197',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['175','181','190','191','196'])).

thf('198',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['197'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('199',plain,(
    ! [X17: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('200',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('202',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('203',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['200','203'])).

thf('205',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['204'])).

thf('206',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['205','206'])).

thf('208',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['207','208'])).

thf('210',plain,(
    ! [X17: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('211',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['209','210'])).

thf('212',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['194','195'])).

thf('213',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('214',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['212','213'])).

thf('215',plain,(
    v2_struct_0 @ sk_B ),
    inference(demod,[status(thm)],['211','214'])).

thf('216',plain,(
    $false ),
    inference(demod,[status(thm)],['0','215'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zDiepRWL9q
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:23:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.26/4.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.26/4.53  % Solved by: fo/fo7.sh
% 4.26/4.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.26/4.53  % done 7228 iterations in 4.070s
% 4.26/4.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.26/4.53  % SZS output start Refutation
% 4.26/4.53  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 4.26/4.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.26/4.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 4.26/4.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 4.26/4.53  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 4.26/4.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 4.26/4.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 4.26/4.53  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 4.26/4.53  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 4.26/4.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.26/4.53  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 4.26/4.53  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 4.26/4.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.26/4.53  thf(sk_D_type, type, sk_D: $i).
% 4.26/4.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 4.26/4.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.26/4.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.26/4.53  thf(v3_borsuk_1_type, type, v3_borsuk_1: $i > $i > $i > $o).
% 4.26/4.53  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 4.26/4.53  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 4.26/4.53  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 4.26/4.53  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 4.26/4.53  thf(sk_A_type, type, sk_A: $i).
% 4.26/4.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 4.26/4.53  thf(v4_tex_2_type, type, v4_tex_2: $i > $i > $o).
% 4.26/4.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.26/4.53  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 4.26/4.53  thf(sk_E_type, type, sk_E: $i).
% 4.26/4.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.26/4.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.26/4.53  thf(sk_B_type, type, sk_B: $i).
% 4.26/4.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 4.26/4.53  thf(t77_tex_2, conjecture,
% 4.26/4.53    (![A:$i]:
% 4.26/4.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 4.26/4.53         ( l1_pre_topc @ A ) ) =>
% 4.26/4.53       ( ![B:$i]:
% 4.26/4.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 4.26/4.53             ( m1_pre_topc @ B @ A ) ) =>
% 4.26/4.53           ( ![C:$i]:
% 4.26/4.53             ( ( ( v1_funct_1 @ C ) & 
% 4.26/4.53                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 4.26/4.53                 ( v5_pre_topc @ C @ A @ B ) & 
% 4.26/4.53                 ( m1_subset_1 @
% 4.26/4.53                   C @ 
% 4.26/4.53                   ( k1_zfmisc_1 @
% 4.26/4.53                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 4.26/4.53               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 4.26/4.53                 ( ![D:$i]:
% 4.26/4.53                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 4.26/4.53                     ( ![E:$i]:
% 4.26/4.53                       ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 4.26/4.53                         ( ( ( D ) = ( E ) ) =>
% 4.26/4.53                           ( ( k8_relset_1 @
% 4.26/4.53                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 4.26/4.53                               ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 4.26/4.53                             ( k2_pre_topc @
% 4.26/4.53                               A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 4.26/4.53  thf(zf_stmt_0, negated_conjecture,
% 4.26/4.53    (~( ![A:$i]:
% 4.26/4.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 4.26/4.53            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.26/4.53          ( ![B:$i]:
% 4.26/4.53            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 4.26/4.53                ( m1_pre_topc @ B @ A ) ) =>
% 4.26/4.53              ( ![C:$i]:
% 4.26/4.53                ( ( ( v1_funct_1 @ C ) & 
% 4.26/4.53                    ( v1_funct_2 @
% 4.26/4.53                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 4.26/4.53                    ( v5_pre_topc @ C @ A @ B ) & 
% 4.26/4.53                    ( m1_subset_1 @
% 4.26/4.53                      C @ 
% 4.26/4.53                      ( k1_zfmisc_1 @
% 4.26/4.53                        ( k2_zfmisc_1 @
% 4.26/4.53                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 4.26/4.53                  ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 4.26/4.53                    ( ![D:$i]:
% 4.26/4.53                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 4.26/4.53                        ( ![E:$i]:
% 4.26/4.53                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 4.26/4.53                            ( ( ( D ) = ( E ) ) =>
% 4.26/4.53                              ( ( k8_relset_1 @
% 4.26/4.53                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 4.26/4.53                                  C @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 4.26/4.53                                ( k2_pre_topc @
% 4.26/4.53                                  A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 4.26/4.53    inference('cnf.neg', [status(esa)], [t77_tex_2])).
% 4.26/4.53  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 4.26/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.26/4.53  thf(t2_tsep_1, axiom,
% 4.26/4.53    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 4.26/4.53  thf('1', plain,
% 4.26/4.53      (![X29 : $i]: ((m1_pre_topc @ X29 @ X29) | ~ (l1_pre_topc @ X29))),
% 4.26/4.53      inference('cnf', [status(esa)], [t2_tsep_1])).
% 4.26/4.53  thf(d10_xboole_0, axiom,
% 4.26/4.53    (![A:$i,B:$i]:
% 4.26/4.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.26/4.53  thf('2', plain,
% 4.26/4.53      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 4.26/4.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.26/4.53  thf('3', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 4.26/4.53      inference('simplify', [status(thm)], ['2'])).
% 4.26/4.53  thf(t3_subset, axiom,
% 4.26/4.53    (![A:$i,B:$i]:
% 4.26/4.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 4.26/4.53  thf('4', plain,
% 4.26/4.53      (![X6 : $i, X8 : $i]:
% 4.26/4.53         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 4.26/4.53      inference('cnf', [status(esa)], [t3_subset])).
% 4.26/4.53  thf('5', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 4.26/4.53      inference('sup-', [status(thm)], ['3', '4'])).
% 4.26/4.53  thf(t26_tex_2, axiom,
% 4.26/4.53    (![A:$i]:
% 4.26/4.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 4.26/4.53       ( ![B:$i]:
% 4.26/4.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 4.26/4.53           ( ![C:$i]:
% 4.26/4.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.26/4.53               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 4.26/4.53                 ( ( v2_tex_2 @ C @ A ) <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) ) ))).
% 4.26/4.53  thf('6', plain,
% 4.26/4.53      (![X36 : $i, X37 : $i, X38 : $i]:
% 4.26/4.53         ((v2_struct_0 @ X36)
% 4.26/4.53          | ~ (m1_pre_topc @ X36 @ X37)
% 4.26/4.53          | ((X38) != (u1_struct_0 @ X36))
% 4.26/4.53          | ~ (v1_tdlat_3 @ X36)
% 4.26/4.53          | (v2_tex_2 @ X38 @ X37)
% 4.26/4.53          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 4.26/4.53          | ~ (l1_pre_topc @ X37)
% 4.26/4.53          | (v2_struct_0 @ X37))),
% 4.26/4.53      inference('cnf', [status(esa)], [t26_tex_2])).
% 4.26/4.53  thf('7', plain,
% 4.26/4.53      (![X36 : $i, X37 : $i]:
% 4.26/4.53         ((v2_struct_0 @ X37)
% 4.26/4.53          | ~ (l1_pre_topc @ X37)
% 4.26/4.53          | ~ (m1_subset_1 @ (u1_struct_0 @ X36) @ 
% 4.26/4.53               (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 4.26/4.53          | (v2_tex_2 @ (u1_struct_0 @ X36) @ X37)
% 4.26/4.53          | ~ (v1_tdlat_3 @ X36)
% 4.26/4.53          | ~ (m1_pre_topc @ X36 @ X37)
% 4.26/4.53          | (v2_struct_0 @ X36))),
% 4.26/4.53      inference('simplify', [status(thm)], ['6'])).
% 4.26/4.53  thf('8', plain,
% 4.26/4.53      (![X0 : $i]:
% 4.26/4.53         ((v2_struct_0 @ X0)
% 4.26/4.53          | ~ (m1_pre_topc @ X0 @ X0)
% 4.26/4.53          | ~ (v1_tdlat_3 @ X0)
% 4.26/4.53          | (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 4.26/4.53          | ~ (l1_pre_topc @ X0)
% 4.26/4.53          | (v2_struct_0 @ X0))),
% 4.26/4.53      inference('sup-', [status(thm)], ['5', '7'])).
% 4.26/4.53  thf('9', plain,
% 4.26/4.53      (![X0 : $i]:
% 4.26/4.53         (~ (l1_pre_topc @ X0)
% 4.26/4.53          | (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 4.26/4.53          | ~ (v1_tdlat_3 @ X0)
% 4.26/4.53          | ~ (m1_pre_topc @ X0 @ X0)
% 4.26/4.53          | (v2_struct_0 @ X0))),
% 4.26/4.53      inference('simplify', [status(thm)], ['8'])).
% 4.26/4.53  thf('10', plain,
% 4.26/4.53      (![X0 : $i]:
% 4.26/4.53         (~ (l1_pre_topc @ X0)
% 4.26/4.53          | (v2_struct_0 @ X0)
% 4.26/4.53          | ~ (v1_tdlat_3 @ X0)
% 4.26/4.53          | (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 4.26/4.53          | ~ (l1_pre_topc @ X0))),
% 4.26/4.53      inference('sup-', [status(thm)], ['1', '9'])).
% 4.26/4.53  thf('11', plain,
% 4.26/4.53      (![X0 : $i]:
% 4.26/4.53         ((v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 4.26/4.53          | ~ (v1_tdlat_3 @ X0)
% 4.26/4.53          | (v2_struct_0 @ X0)
% 4.26/4.53          | ~ (l1_pre_topc @ X0))),
% 4.26/4.53      inference('simplify', [status(thm)], ['10'])).
% 4.26/4.53  thf('12', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 4.26/4.53      inference('sup-', [status(thm)], ['3', '4'])).
% 4.26/4.53  thf(t65_tex_2, axiom,
% 4.26/4.53    (![A:$i]:
% 4.26/4.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 4.26/4.53         ( l1_pre_topc @ A ) ) =>
% 4.26/4.53       ( ![B:$i]:
% 4.26/4.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.26/4.53           ( ~( ( v2_tex_2 @ B @ A ) & 
% 4.26/4.53                ( ![C:$i]:
% 4.26/4.53                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.26/4.53                    ( ~( ( r1_tarski @ B @ C ) & ( v3_tex_2 @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 4.26/4.53  thf('13', plain,
% 4.26/4.53      (![X41 : $i, X42 : $i]:
% 4.26/4.53         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 4.26/4.53          | ~ (v2_tex_2 @ X41 @ X42)
% 4.26/4.53          | (m1_subset_1 @ (sk_C @ X41 @ X42) @ 
% 4.26/4.53             (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 4.26/4.53          | ~ (l1_pre_topc @ X42)
% 4.26/4.53          | ~ (v3_tdlat_3 @ X42)
% 4.26/4.53          | ~ (v2_pre_topc @ X42)
% 4.26/4.53          | (v2_struct_0 @ X42))),
% 4.26/4.53      inference('cnf', [status(esa)], [t65_tex_2])).
% 4.26/4.53  thf('14', plain,
% 4.26/4.53      (![X0 : $i]:
% 4.26/4.53         ((v2_struct_0 @ X0)
% 4.26/4.53          | ~ (v2_pre_topc @ X0)
% 4.26/4.53          | ~ (v3_tdlat_3 @ X0)
% 4.26/4.53          | ~ (l1_pre_topc @ X0)
% 4.26/4.53          | (m1_subset_1 @ (sk_C @ (u1_struct_0 @ X0) @ X0) @ 
% 4.26/4.53             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 4.26/4.53          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 4.26/4.53      inference('sup-', [status(thm)], ['12', '13'])).
% 4.26/4.53  thf('15', plain,
% 4.26/4.53      (![X0 : $i]:
% 4.26/4.53         (~ (l1_pre_topc @ X0)
% 4.26/4.53          | (v2_struct_0 @ X0)
% 4.26/4.53          | ~ (v1_tdlat_3 @ X0)
% 4.26/4.53          | (m1_subset_1 @ (sk_C @ (u1_struct_0 @ X0) @ X0) @ 
% 4.26/4.53             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 4.26/4.53          | ~ (l1_pre_topc @ X0)
% 4.26/4.53          | ~ (v3_tdlat_3 @ X0)
% 4.26/4.53          | ~ (v2_pre_topc @ X0)
% 4.26/4.53          | (v2_struct_0 @ X0))),
% 4.26/4.53      inference('sup-', [status(thm)], ['11', '14'])).
% 4.26/4.53  thf('16', plain,
% 4.26/4.53      (![X0 : $i]:
% 4.26/4.53         (~ (v2_pre_topc @ X0)
% 4.26/4.53          | ~ (v3_tdlat_3 @ X0)
% 4.26/4.53          | (m1_subset_1 @ (sk_C @ (u1_struct_0 @ X0) @ X0) @ 
% 4.26/4.53             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 4.26/4.53          | ~ (v1_tdlat_3 @ X0)
% 4.26/4.53          | (v2_struct_0 @ X0)
% 4.26/4.53          | ~ (l1_pre_topc @ X0))),
% 4.26/4.53      inference('simplify', [status(thm)], ['15'])).
% 4.26/4.53  thf('17', plain,
% 4.26/4.53      (![X6 : $i, X7 : $i]:
% 4.26/4.53         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 4.26/4.53      inference('cnf', [status(esa)], [t3_subset])).
% 4.26/4.53  thf('18', plain,
% 4.26/4.53      (![X0 : $i]:
% 4.35/4.53         (~ (l1_pre_topc @ X0)
% 4.35/4.53          | (v2_struct_0 @ X0)
% 4.35/4.53          | ~ (v1_tdlat_3 @ X0)
% 4.35/4.53          | ~ (v3_tdlat_3 @ X0)
% 4.35/4.53          | ~ (v2_pre_topc @ X0)
% 4.35/4.53          | (r1_tarski @ (sk_C @ (u1_struct_0 @ X0) @ X0) @ (u1_struct_0 @ X0)))),
% 4.35/4.53      inference('sup-', [status(thm)], ['16', '17'])).
% 4.35/4.53  thf('19', plain,
% 4.35/4.53      (![X0 : $i]:
% 4.35/4.53         ((v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 4.35/4.53          | ~ (v1_tdlat_3 @ X0)
% 4.35/4.53          | (v2_struct_0 @ X0)
% 4.35/4.53          | ~ (l1_pre_topc @ X0))),
% 4.35/4.53      inference('simplify', [status(thm)], ['10'])).
% 4.35/4.53  thf('20', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 4.35/4.53      inference('sup-', [status(thm)], ['3', '4'])).
% 4.35/4.53  thf('21', plain,
% 4.35/4.53      (![X41 : $i, X42 : $i]:
% 4.35/4.53         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 4.35/4.53          | ~ (v2_tex_2 @ X41 @ X42)
% 4.35/4.53          | (r1_tarski @ X41 @ (sk_C @ X41 @ X42))
% 4.35/4.53          | ~ (l1_pre_topc @ X42)
% 4.35/4.53          | ~ (v3_tdlat_3 @ X42)
% 4.35/4.53          | ~ (v2_pre_topc @ X42)
% 4.35/4.53          | (v2_struct_0 @ X42))),
% 4.35/4.53      inference('cnf', [status(esa)], [t65_tex_2])).
% 4.35/4.53  thf('22', plain,
% 4.35/4.53      (![X0 : $i]:
% 4.35/4.53         ((v2_struct_0 @ X0)
% 4.35/4.53          | ~ (v2_pre_topc @ X0)
% 4.35/4.53          | ~ (v3_tdlat_3 @ X0)
% 4.35/4.53          | ~ (l1_pre_topc @ X0)
% 4.35/4.53          | (r1_tarski @ (u1_struct_0 @ X0) @ (sk_C @ (u1_struct_0 @ X0) @ X0))
% 4.35/4.53          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 4.35/4.53      inference('sup-', [status(thm)], ['20', '21'])).
% 4.35/4.53  thf('23', plain,
% 4.35/4.53      (![X0 : $i]:
% 4.35/4.53         (~ (l1_pre_topc @ X0)
% 4.35/4.53          | (v2_struct_0 @ X0)
% 4.35/4.53          | ~ (v1_tdlat_3 @ X0)
% 4.35/4.53          | (r1_tarski @ (u1_struct_0 @ X0) @ (sk_C @ (u1_struct_0 @ X0) @ X0))
% 4.35/4.53          | ~ (l1_pre_topc @ X0)
% 4.35/4.53          | ~ (v3_tdlat_3 @ X0)
% 4.35/4.53          | ~ (v2_pre_topc @ X0)
% 4.35/4.53          | (v2_struct_0 @ X0))),
% 4.35/4.53      inference('sup-', [status(thm)], ['19', '22'])).
% 4.35/4.53  thf('24', plain,
% 4.35/4.53      (![X0 : $i]:
% 4.35/4.53         (~ (v2_pre_topc @ X0)
% 4.35/4.53          | ~ (v3_tdlat_3 @ X0)
% 4.35/4.53          | (r1_tarski @ (u1_struct_0 @ X0) @ (sk_C @ (u1_struct_0 @ X0) @ X0))
% 4.35/4.53          | ~ (v1_tdlat_3 @ X0)
% 4.35/4.53          | (v2_struct_0 @ X0)
% 4.35/4.53          | ~ (l1_pre_topc @ X0))),
% 4.35/4.53      inference('simplify', [status(thm)], ['23'])).
% 4.35/4.53  thf('25', plain,
% 4.35/4.53      (![X0 : $i, X2 : $i]:
% 4.35/4.53         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 4.35/4.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.35/4.53  thf('26', plain,
% 4.35/4.53      (![X0 : $i]:
% 4.35/4.53         (~ (l1_pre_topc @ X0)
% 4.35/4.53          | (v2_struct_0 @ X0)
% 4.35/4.53          | ~ (v1_tdlat_3 @ X0)
% 4.35/4.53          | ~ (v3_tdlat_3 @ X0)
% 4.35/4.53          | ~ (v2_pre_topc @ X0)
% 4.35/4.53          | ~ (r1_tarski @ (sk_C @ (u1_struct_0 @ X0) @ X0) @ 
% 4.35/4.53               (u1_struct_0 @ X0))
% 4.35/4.53          | ((sk_C @ (u1_struct_0 @ X0) @ X0) = (u1_struct_0 @ X0)))),
% 4.35/4.53      inference('sup-', [status(thm)], ['24', '25'])).
% 4.35/4.53  thf('27', plain,
% 4.35/4.53      (![X0 : $i]:
% 4.35/4.53         (~ (v2_pre_topc @ X0)
% 4.35/4.53          | ~ (v3_tdlat_3 @ X0)
% 4.35/4.53          | ~ (v1_tdlat_3 @ X0)
% 4.35/4.53          | (v2_struct_0 @ X0)
% 4.35/4.53          | ~ (l1_pre_topc @ X0)
% 4.35/4.53          | ((sk_C @ (u1_struct_0 @ X0) @ X0) = (u1_struct_0 @ X0))
% 4.35/4.53          | ~ (v2_pre_topc @ X0)
% 4.35/4.53          | ~ (v3_tdlat_3 @ X0)
% 4.35/4.53          | ~ (v1_tdlat_3 @ X0)
% 4.35/4.53          | (v2_struct_0 @ X0)
% 4.35/4.53          | ~ (l1_pre_topc @ X0))),
% 4.35/4.53      inference('sup-', [status(thm)], ['18', '26'])).
% 4.35/4.53  thf('28', plain,
% 4.35/4.53      (![X0 : $i]:
% 4.35/4.53         (((sk_C @ (u1_struct_0 @ X0) @ X0) = (u1_struct_0 @ X0))
% 4.35/4.53          | ~ (l1_pre_topc @ X0)
% 4.35/4.53          | (v2_struct_0 @ X0)
% 4.35/4.53          | ~ (v1_tdlat_3 @ X0)
% 4.35/4.53          | ~ (v3_tdlat_3 @ X0)
% 4.35/4.53          | ~ (v2_pre_topc @ X0))),
% 4.35/4.53      inference('simplify', [status(thm)], ['27'])).
% 4.35/4.53  thf('29', plain,
% 4.35/4.53      (![X0 : $i]:
% 4.35/4.53         ((v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 4.35/4.53          | ~ (v1_tdlat_3 @ X0)
% 4.35/4.53          | (v2_struct_0 @ X0)
% 4.35/4.53          | ~ (l1_pre_topc @ X0))),
% 4.35/4.53      inference('simplify', [status(thm)], ['10'])).
% 4.35/4.53  thf('30', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 4.35/4.53      inference('sup-', [status(thm)], ['3', '4'])).
% 4.35/4.53  thf('31', plain,
% 4.35/4.53      (![X41 : $i, X42 : $i]:
% 4.35/4.53         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 4.35/4.53          | ~ (v2_tex_2 @ X41 @ X42)
% 4.35/4.53          | (v3_tex_2 @ (sk_C @ X41 @ X42) @ X42)
% 4.35/4.53          | ~ (l1_pre_topc @ X42)
% 4.35/4.53          | ~ (v3_tdlat_3 @ X42)
% 4.35/4.53          | ~ (v2_pre_topc @ X42)
% 4.35/4.53          | (v2_struct_0 @ X42))),
% 4.35/4.53      inference('cnf', [status(esa)], [t65_tex_2])).
% 4.35/4.53  thf('32', plain,
% 4.35/4.53      (![X0 : $i]:
% 4.35/4.53         ((v2_struct_0 @ X0)
% 4.35/4.53          | ~ (v2_pre_topc @ X0)
% 4.35/4.53          | ~ (v3_tdlat_3 @ X0)
% 4.35/4.53          | ~ (l1_pre_topc @ X0)
% 4.35/4.53          | (v3_tex_2 @ (sk_C @ (u1_struct_0 @ X0) @ X0) @ X0)
% 4.35/4.53          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 4.35/4.53      inference('sup-', [status(thm)], ['30', '31'])).
% 4.35/4.53  thf('33', plain,
% 4.35/4.53      (![X0 : $i]:
% 4.35/4.53         (~ (l1_pre_topc @ X0)
% 4.35/4.53          | (v2_struct_0 @ X0)
% 4.35/4.53          | ~ (v1_tdlat_3 @ X0)
% 4.35/4.53          | (v3_tex_2 @ (sk_C @ (u1_struct_0 @ X0) @ X0) @ X0)
% 4.35/4.53          | ~ (l1_pre_topc @ X0)
% 4.35/4.53          | ~ (v3_tdlat_3 @ X0)
% 4.35/4.53          | ~ (v2_pre_topc @ X0)
% 4.35/4.53          | (v2_struct_0 @ X0))),
% 4.35/4.53      inference('sup-', [status(thm)], ['29', '32'])).
% 4.35/4.53  thf('34', plain,
% 4.35/4.53      (![X0 : $i]:
% 4.35/4.53         (~ (v2_pre_topc @ X0)
% 4.35/4.53          | ~ (v3_tdlat_3 @ X0)
% 4.35/4.53          | (v3_tex_2 @ (sk_C @ (u1_struct_0 @ X0) @ X0) @ X0)
% 4.35/4.53          | ~ (v1_tdlat_3 @ X0)
% 4.35/4.53          | (v2_struct_0 @ X0)
% 4.35/4.53          | ~ (l1_pre_topc @ X0))),
% 4.35/4.53      inference('simplify', [status(thm)], ['33'])).
% 4.35/4.53  thf('35', plain,
% 4.35/4.53      (![X0 : $i]:
% 4.35/4.53         ((v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 4.35/4.53          | ~ (v2_pre_topc @ X0)
% 4.35/4.53          | ~ (v3_tdlat_3 @ X0)
% 4.35/4.53          | ~ (v1_tdlat_3 @ X0)
% 4.35/4.53          | (v2_struct_0 @ X0)
% 4.35/4.53          | ~ (l1_pre_topc @ X0)
% 4.35/4.53          | ~ (l1_pre_topc @ X0)
% 4.35/4.53          | (v2_struct_0 @ X0)
% 4.35/4.53          | ~ (v1_tdlat_3 @ X0)
% 4.35/4.53          | ~ (v3_tdlat_3 @ X0)
% 4.35/4.53          | ~ (v2_pre_topc @ X0))),
% 4.35/4.53      inference('sup+', [status(thm)], ['28', '34'])).
% 4.35/4.53  thf('36', plain,
% 4.35/4.53      (![X0 : $i]:
% 4.35/4.53         (~ (l1_pre_topc @ X0)
% 4.35/4.53          | (v2_struct_0 @ X0)
% 4.35/4.53          | ~ (v1_tdlat_3 @ X0)
% 4.35/4.53          | ~ (v3_tdlat_3 @ X0)
% 4.35/4.53          | ~ (v2_pre_topc @ X0)
% 4.35/4.53          | (v3_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 4.35/4.53      inference('simplify', [status(thm)], ['35'])).
% 4.35/4.53  thf('37', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 4.35/4.53      inference('sup-', [status(thm)], ['3', '4'])).
% 4.35/4.53  thf(t62_tex_2, axiom,
% 4.35/4.53    (![A:$i]:
% 4.35/4.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 4.35/4.53         ( l1_pre_topc @ A ) ) =>
% 4.35/4.53       ( ![B:$i]:
% 4.35/4.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.35/4.53           ( ( v3_tex_2 @ B @ A ) => ( v1_tops_1 @ B @ A ) ) ) ) ))).
% 4.35/4.53  thf('38', plain,
% 4.35/4.53      (![X39 : $i, X40 : $i]:
% 4.35/4.53         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 4.35/4.53          | (v1_tops_1 @ X39 @ X40)
% 4.35/4.53          | ~ (v3_tex_2 @ X39 @ X40)
% 4.35/4.53          | ~ (l1_pre_topc @ X40)
% 4.35/4.53          | ~ (v3_tdlat_3 @ X40)
% 4.35/4.53          | ~ (v2_pre_topc @ X40)
% 4.35/4.53          | (v2_struct_0 @ X40))),
% 4.35/4.53      inference('cnf', [status(esa)], [t62_tex_2])).
% 4.35/4.53  thf('39', plain,
% 4.35/4.53      (![X0 : $i]:
% 4.35/4.53         ((v2_struct_0 @ X0)
% 4.35/4.53          | ~ (v2_pre_topc @ X0)
% 4.35/4.53          | ~ (v3_tdlat_3 @ X0)
% 4.35/4.53          | ~ (l1_pre_topc @ X0)
% 4.35/4.53          | ~ (v3_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 4.35/4.53          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0))),
% 4.35/4.53      inference('sup-', [status(thm)], ['37', '38'])).
% 4.35/4.53  thf('40', plain,
% 4.35/4.53      (![X0 : $i]:
% 4.35/4.53         (~ (v2_pre_topc @ X0)
% 4.35/4.53          | ~ (v3_tdlat_3 @ X0)
% 4.35/4.53          | ~ (v1_tdlat_3 @ X0)
% 4.35/4.53          | (v2_struct_0 @ X0)
% 4.35/4.53          | ~ (l1_pre_topc @ X0)
% 4.35/4.53          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 4.35/4.53          | ~ (l1_pre_topc @ X0)
% 4.35/4.53          | ~ (v3_tdlat_3 @ X0)
% 4.35/4.53          | ~ (v2_pre_topc @ X0)
% 4.35/4.53          | (v2_struct_0 @ X0))),
% 4.35/4.53      inference('sup-', [status(thm)], ['36', '39'])).
% 4.35/4.53  thf('41', plain,
% 4.35/4.53      (![X0 : $i]:
% 4.35/4.53         ((v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 4.35/4.53          | ~ (l1_pre_topc @ X0)
% 4.35/4.53          | (v2_struct_0 @ X0)
% 4.35/4.53          | ~ (v1_tdlat_3 @ X0)
% 4.35/4.53          | ~ (v3_tdlat_3 @ X0)
% 4.35/4.53          | ~ (v2_pre_topc @ X0))),
% 4.35/4.53      inference('simplify', [status(thm)], ['40'])).
% 4.35/4.53  thf('42', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 4.35/4.53      inference('sup-', [status(thm)], ['3', '4'])).
% 4.35/4.53  thf(d2_tops_3, axiom,
% 4.35/4.53    (![A:$i]:
% 4.35/4.53     ( ( l1_pre_topc @ A ) =>
% 4.35/4.53       ( ![B:$i]:
% 4.35/4.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.35/4.53           ( ( v1_tops_1 @ B @ A ) <=>
% 4.35/4.53             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 4.35/4.53  thf('43', plain,
% 4.35/4.53      (![X34 : $i, X35 : $i]:
% 4.35/4.53         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 4.35/4.53          | ~ (v1_tops_1 @ X34 @ X35)
% 4.35/4.53          | ((k2_pre_topc @ X35 @ X34) = (u1_struct_0 @ X35))
% 4.35/4.53          | ~ (l1_pre_topc @ X35))),
% 4.35/4.53      inference('cnf', [status(esa)], [d2_tops_3])).
% 4.35/4.53  thf('44', plain,
% 4.35/4.53      (![X0 : $i]:
% 4.35/4.53         (~ (l1_pre_topc @ X0)
% 4.35/4.53          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 4.35/4.53          | ~ (v1_tops_1 @ (u1_struct_0 @ X0) @ X0))),
% 4.35/4.53      inference('sup-', [status(thm)], ['42', '43'])).
% 4.35/4.53  thf('45', plain,
% 4.35/4.53      (![X0 : $i]:
% 4.35/4.53         (~ (v2_pre_topc @ X0)
% 4.35/4.53          | ~ (v3_tdlat_3 @ X0)
% 4.35/4.53          | ~ (v1_tdlat_3 @ X0)
% 4.35/4.53          | (v2_struct_0 @ X0)
% 4.35/4.53          | ~ (l1_pre_topc @ X0)
% 4.35/4.53          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 4.35/4.53          | ~ (l1_pre_topc @ X0))),
% 4.35/4.53      inference('sup-', [status(thm)], ['41', '44'])).
% 4.35/4.53  thf('46', plain,
% 4.35/4.53      (![X0 : $i]:
% 4.35/4.53         (((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 4.35/4.53          | ~ (l1_pre_topc @ X0)
% 4.35/4.53          | (v2_struct_0 @ X0)
% 4.35/4.53          | ~ (v1_tdlat_3 @ X0)
% 4.35/4.53          | ~ (v3_tdlat_3 @ X0)
% 4.35/4.53          | ~ (v2_pre_topc @ X0))),
% 4.35/4.53      inference('simplify', [status(thm)], ['45'])).
% 4.35/4.53  thf('47', plain,
% 4.35/4.53      (![X0 : $i]:
% 4.35/4.53         ((v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 4.35/4.53          | ~ (l1_pre_topc @ X0)
% 4.35/4.53          | (v2_struct_0 @ X0)
% 4.35/4.53          | ~ (v1_tdlat_3 @ X0)
% 4.35/4.53          | ~ (v3_tdlat_3 @ X0)
% 4.35/4.53          | ~ (v2_pre_topc @ X0))),
% 4.35/4.53      inference('simplify', [status(thm)], ['40'])).
% 4.35/4.53  thf('48', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 4.35/4.53      inference('sup-', [status(thm)], ['3', '4'])).
% 4.35/4.53  thf(d3_tops_1, axiom,
% 4.35/4.53    (![A:$i]:
% 4.35/4.53     ( ( l1_pre_topc @ A ) =>
% 4.35/4.53       ( ![B:$i]:
% 4.35/4.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.35/4.53           ( ( v1_tops_1 @ B @ A ) <=>
% 4.35/4.53             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 4.35/4.53  thf('49', plain,
% 4.35/4.53      (![X25 : $i, X26 : $i]:
% 4.35/4.53         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 4.35/4.53          | ~ (v1_tops_1 @ X25 @ X26)
% 4.35/4.53          | ((k2_pre_topc @ X26 @ X25) = (k2_struct_0 @ X26))
% 4.35/4.53          | ~ (l1_pre_topc @ X26))),
% 4.35/4.53      inference('cnf', [status(esa)], [d3_tops_1])).
% 4.35/4.53  thf('50', plain,
% 4.35/4.53      (![X0 : $i]:
% 4.35/4.53         (~ (l1_pre_topc @ X0)
% 4.35/4.53          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 4.35/4.53          | ~ (v1_tops_1 @ (u1_struct_0 @ X0) @ X0))),
% 4.35/4.53      inference('sup-', [status(thm)], ['48', '49'])).
% 4.35/4.53  thf('51', plain,
% 4.35/4.53      (![X0 : $i]:
% 4.35/4.53         (~ (v2_pre_topc @ X0)
% 4.35/4.53          | ~ (v3_tdlat_3 @ X0)
% 4.35/4.53          | ~ (v1_tdlat_3 @ X0)
% 4.35/4.53          | (v2_struct_0 @ X0)
% 4.35/4.53          | ~ (l1_pre_topc @ X0)
% 4.35/4.53          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 4.35/4.53          | ~ (l1_pre_topc @ X0))),
% 4.35/4.53      inference('sup-', [status(thm)], ['47', '50'])).
% 4.35/4.53  thf('52', plain,
% 4.35/4.53      (![X0 : $i]:
% 4.35/4.53         (((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 4.35/4.53          | ~ (l1_pre_topc @ X0)
% 4.35/4.53          | (v2_struct_0 @ X0)
% 4.35/4.53          | ~ (v1_tdlat_3 @ X0)
% 4.35/4.53          | ~ (v3_tdlat_3 @ X0)
% 4.35/4.53          | ~ (v2_pre_topc @ X0))),
% 4.35/4.53      inference('simplify', [status(thm)], ['51'])).
% 4.35/4.53  thf('53', plain,
% 4.35/4.53      (![X0 : $i]:
% 4.35/4.53         (((u1_struct_0 @ X0) = (k2_struct_0 @ X0))
% 4.35/4.53          | ~ (v2_pre_topc @ X0)
% 4.35/4.53          | ~ (v3_tdlat_3 @ X0)
% 4.35/4.53          | ~ (v1_tdlat_3 @ X0)
% 4.35/4.53          | (v2_struct_0 @ X0)
% 4.35/4.53          | ~ (l1_pre_topc @ X0)
% 4.35/4.53          | ~ (v2_pre_topc @ X0)
% 4.35/4.53          | ~ (v3_tdlat_3 @ X0)
% 4.35/4.53          | ~ (v1_tdlat_3 @ X0)
% 4.35/4.53          | (v2_struct_0 @ X0)
% 4.35/4.53          | ~ (l1_pre_topc @ X0))),
% 4.35/4.53      inference('sup+', [status(thm)], ['46', '52'])).
% 4.35/4.53  thf('54', plain,
% 4.35/4.53      (![X0 : $i]:
% 4.35/4.53         (~ (l1_pre_topc @ X0)
% 4.35/4.53          | (v2_struct_0 @ X0)
% 4.35/4.53          | ~ (v1_tdlat_3 @ X0)
% 4.35/4.53          | ~ (v3_tdlat_3 @ X0)
% 4.35/4.53          | ~ (v2_pre_topc @ X0)
% 4.35/4.53          | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0)))),
% 4.35/4.53      inference('simplify', [status(thm)], ['53'])).
% 4.35/4.53  thf('55', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_A))),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('56', plain, (((sk_D) = (sk_E))),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('57', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 4.35/4.53      inference('demod', [status(thm)], ['55', '56'])).
% 4.35/4.53  thf(redefinition_k6_domain_1, axiom,
% 4.35/4.53    (![A:$i,B:$i]:
% 4.35/4.53     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 4.35/4.53       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 4.35/4.53  thf('58', plain,
% 4.35/4.53      (![X23 : $i, X24 : $i]:
% 4.35/4.53         ((v1_xboole_0 @ X23)
% 4.35/4.53          | ~ (m1_subset_1 @ X24 @ X23)
% 4.35/4.53          | ((k6_domain_1 @ X23 @ X24) = (k1_tarski @ X24)))),
% 4.35/4.53      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 4.35/4.53  thf('59', plain,
% 4.35/4.53      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D) = (k1_tarski @ sk_D))
% 4.35/4.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 4.35/4.53      inference('sup-', [status(thm)], ['57', '58'])).
% 4.35/4.53  thf('60', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf(t1_tsep_1, axiom,
% 4.35/4.53    (![A:$i]:
% 4.35/4.53     ( ( l1_pre_topc @ A ) =>
% 4.35/4.53       ( ![B:$i]:
% 4.35/4.53         ( ( m1_pre_topc @ B @ A ) =>
% 4.35/4.53           ( m1_subset_1 @
% 4.35/4.53             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 4.35/4.53  thf('61', plain,
% 4.35/4.53      (![X27 : $i, X28 : $i]:
% 4.35/4.53         (~ (m1_pre_topc @ X27 @ X28)
% 4.35/4.53          | (m1_subset_1 @ (u1_struct_0 @ X27) @ 
% 4.35/4.53             (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 4.35/4.53          | ~ (l1_pre_topc @ X28))),
% 4.35/4.53      inference('cnf', [status(esa)], [t1_tsep_1])).
% 4.35/4.53  thf('62', plain,
% 4.35/4.53      ((~ (l1_pre_topc @ sk_A)
% 4.35/4.53        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 4.35/4.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 4.35/4.53      inference('sup-', [status(thm)], ['60', '61'])).
% 4.35/4.53  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('64', plain,
% 4.35/4.53      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 4.35/4.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.35/4.53      inference('demod', [status(thm)], ['62', '63'])).
% 4.35/4.53  thf('65', plain,
% 4.35/4.53      (![X41 : $i, X42 : $i]:
% 4.35/4.53         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 4.35/4.53          | ~ (v2_tex_2 @ X41 @ X42)
% 4.35/4.53          | (m1_subset_1 @ (sk_C @ X41 @ X42) @ 
% 4.35/4.53             (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 4.35/4.53          | ~ (l1_pre_topc @ X42)
% 4.35/4.53          | ~ (v3_tdlat_3 @ X42)
% 4.35/4.53          | ~ (v2_pre_topc @ X42)
% 4.35/4.53          | (v2_struct_0 @ X42))),
% 4.35/4.53      inference('cnf', [status(esa)], [t65_tex_2])).
% 4.35/4.53  thf('66', plain,
% 4.35/4.53      (((v2_struct_0 @ sk_A)
% 4.35/4.53        | ~ (v2_pre_topc @ sk_A)
% 4.35/4.53        | ~ (v3_tdlat_3 @ sk_A)
% 4.35/4.53        | ~ (l1_pre_topc @ sk_A)
% 4.35/4.53        | (m1_subset_1 @ (sk_C @ (u1_struct_0 @ sk_B) @ sk_A) @ 
% 4.35/4.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.35/4.53        | ~ (v2_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A))),
% 4.35/4.53      inference('sup-', [status(thm)], ['64', '65'])).
% 4.35/4.53  thf('67', plain, ((v2_pre_topc @ sk_A)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('68', plain, ((v3_tdlat_3 @ sk_A)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('70', plain,
% 4.35/4.53      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 4.35/4.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.35/4.53      inference('demod', [status(thm)], ['62', '63'])).
% 4.35/4.53  thf('71', plain,
% 4.35/4.53      (![X36 : $i, X37 : $i]:
% 4.35/4.53         ((v2_struct_0 @ X37)
% 4.35/4.53          | ~ (l1_pre_topc @ X37)
% 4.35/4.53          | ~ (m1_subset_1 @ (u1_struct_0 @ X36) @ 
% 4.35/4.53               (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 4.35/4.53          | (v2_tex_2 @ (u1_struct_0 @ X36) @ X37)
% 4.35/4.53          | ~ (v1_tdlat_3 @ X36)
% 4.35/4.53          | ~ (m1_pre_topc @ X36 @ X37)
% 4.35/4.53          | (v2_struct_0 @ X36))),
% 4.35/4.53      inference('simplify', [status(thm)], ['6'])).
% 4.35/4.53  thf('72', plain,
% 4.35/4.53      (((v2_struct_0 @ sk_B)
% 4.35/4.53        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 4.35/4.53        | ~ (v1_tdlat_3 @ sk_B)
% 4.35/4.53        | (v2_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A)
% 4.35/4.53        | ~ (l1_pre_topc @ sk_A)
% 4.35/4.53        | (v2_struct_0 @ sk_A))),
% 4.35/4.53      inference('sup-', [status(thm)], ['70', '71'])).
% 4.35/4.53  thf('73', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('74', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf(cc35_tex_2, axiom,
% 4.35/4.53    (![A:$i]:
% 4.35/4.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 4.35/4.53       ( ![B:$i]:
% 4.35/4.53         ( ( m1_pre_topc @ B @ A ) =>
% 4.35/4.53           ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) ) =>
% 4.35/4.53             ( ( ~( v2_struct_0 @ B ) ) & ( v1_tdlat_3 @ B ) ) ) ) ) ))).
% 4.35/4.53  thf('75', plain,
% 4.35/4.53      (![X32 : $i, X33 : $i]:
% 4.35/4.53         (~ (m1_pre_topc @ X32 @ X33)
% 4.35/4.53          | (v1_tdlat_3 @ X32)
% 4.35/4.53          | ~ (v4_tex_2 @ X32 @ X33)
% 4.35/4.53          | (v2_struct_0 @ X32)
% 4.35/4.53          | ~ (l1_pre_topc @ X33)
% 4.35/4.53          | (v2_struct_0 @ X33))),
% 4.35/4.53      inference('cnf', [status(esa)], [cc35_tex_2])).
% 4.35/4.53  thf('76', plain,
% 4.35/4.53      (((v2_struct_0 @ sk_A)
% 4.35/4.53        | ~ (l1_pre_topc @ sk_A)
% 4.35/4.53        | (v2_struct_0 @ sk_B)
% 4.35/4.53        | ~ (v4_tex_2 @ sk_B @ sk_A)
% 4.35/4.53        | (v1_tdlat_3 @ sk_B))),
% 4.35/4.53      inference('sup-', [status(thm)], ['74', '75'])).
% 4.35/4.53  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('78', plain, ((v4_tex_2 @ sk_B @ sk_A)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('79', plain,
% 4.35/4.53      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B) | (v1_tdlat_3 @ sk_B))),
% 4.35/4.53      inference('demod', [status(thm)], ['76', '77', '78'])).
% 4.35/4.53  thf('80', plain, (~ (v2_struct_0 @ sk_A)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('81', plain, (((v1_tdlat_3 @ sk_B) | (v2_struct_0 @ sk_B))),
% 4.35/4.53      inference('clc', [status(thm)], ['79', '80'])).
% 4.35/4.53  thf('82', plain, (~ (v2_struct_0 @ sk_B)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('83', plain, ((v1_tdlat_3 @ sk_B)),
% 4.35/4.53      inference('clc', [status(thm)], ['81', '82'])).
% 4.35/4.53  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('85', plain,
% 4.35/4.53      (((v2_struct_0 @ sk_B)
% 4.35/4.53        | (v2_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A)
% 4.35/4.53        | (v2_struct_0 @ sk_A))),
% 4.35/4.53      inference('demod', [status(thm)], ['72', '73', '83', '84'])).
% 4.35/4.53  thf('86', plain, (~ (v2_struct_0 @ sk_B)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('87', plain,
% 4.35/4.53      (((v2_struct_0 @ sk_A) | (v2_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A))),
% 4.35/4.53      inference('clc', [status(thm)], ['85', '86'])).
% 4.35/4.53  thf('88', plain, (~ (v2_struct_0 @ sk_A)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('89', plain, ((v2_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A)),
% 4.35/4.53      inference('clc', [status(thm)], ['87', '88'])).
% 4.35/4.53  thf('90', plain,
% 4.35/4.53      (((v2_struct_0 @ sk_A)
% 4.35/4.53        | (m1_subset_1 @ (sk_C @ (u1_struct_0 @ sk_B) @ sk_A) @ 
% 4.35/4.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 4.35/4.53      inference('demod', [status(thm)], ['66', '67', '68', '69', '89'])).
% 4.35/4.53  thf('91', plain, (~ (v2_struct_0 @ sk_A)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('92', plain,
% 4.35/4.53      ((m1_subset_1 @ (sk_C @ (u1_struct_0 @ sk_B) @ sk_A) @ 
% 4.35/4.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.35/4.53      inference('clc', [status(thm)], ['90', '91'])).
% 4.35/4.53  thf('93', plain,
% 4.35/4.53      (![X25 : $i, X26 : $i]:
% 4.35/4.53         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 4.35/4.53          | ~ (v1_tops_1 @ X25 @ X26)
% 4.35/4.53          | ((k2_pre_topc @ X26 @ X25) = (k2_struct_0 @ X26))
% 4.35/4.53          | ~ (l1_pre_topc @ X26))),
% 4.35/4.53      inference('cnf', [status(esa)], [d3_tops_1])).
% 4.35/4.53  thf('94', plain,
% 4.35/4.53      ((~ (l1_pre_topc @ sk_A)
% 4.35/4.53        | ((k2_pre_topc @ sk_A @ (sk_C @ (u1_struct_0 @ sk_B) @ sk_A))
% 4.35/4.53            = (k2_struct_0 @ sk_A))
% 4.35/4.53        | ~ (v1_tops_1 @ (sk_C @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))),
% 4.35/4.53      inference('sup-', [status(thm)], ['92', '93'])).
% 4.35/4.53  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('96', plain,
% 4.35/4.53      ((((k2_pre_topc @ sk_A @ (sk_C @ (u1_struct_0 @ sk_B) @ sk_A))
% 4.35/4.53          = (k2_struct_0 @ sk_A))
% 4.35/4.53        | ~ (v1_tops_1 @ (sk_C @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))),
% 4.35/4.53      inference('demod', [status(thm)], ['94', '95'])).
% 4.35/4.53  thf('97', plain,
% 4.35/4.53      ((m1_subset_1 @ (sk_C @ (u1_struct_0 @ sk_B) @ sk_A) @ 
% 4.35/4.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.35/4.53      inference('clc', [status(thm)], ['90', '91'])).
% 4.35/4.53  thf('98', plain,
% 4.35/4.53      (![X34 : $i, X35 : $i]:
% 4.35/4.53         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 4.35/4.53          | ~ (v1_tops_1 @ X34 @ X35)
% 4.35/4.53          | ((k2_pre_topc @ X35 @ X34) = (u1_struct_0 @ X35))
% 4.35/4.53          | ~ (l1_pre_topc @ X35))),
% 4.35/4.53      inference('cnf', [status(esa)], [d2_tops_3])).
% 4.35/4.53  thf('99', plain,
% 4.35/4.53      ((~ (l1_pre_topc @ sk_A)
% 4.35/4.53        | ((k2_pre_topc @ sk_A @ (sk_C @ (u1_struct_0 @ sk_B) @ sk_A))
% 4.35/4.53            = (u1_struct_0 @ sk_A))
% 4.35/4.53        | ~ (v1_tops_1 @ (sk_C @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))),
% 4.35/4.53      inference('sup-', [status(thm)], ['97', '98'])).
% 4.35/4.53  thf('100', plain, ((l1_pre_topc @ sk_A)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('101', plain,
% 4.35/4.53      ((((k2_pre_topc @ sk_A @ (sk_C @ (u1_struct_0 @ sk_B) @ sk_A))
% 4.35/4.53          = (u1_struct_0 @ sk_A))
% 4.35/4.53        | ~ (v1_tops_1 @ (sk_C @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))),
% 4.35/4.53      inference('demod', [status(thm)], ['99', '100'])).
% 4.35/4.53  thf('102', plain,
% 4.35/4.53      ((m1_subset_1 @ (sk_C @ (u1_struct_0 @ sk_B) @ sk_A) @ 
% 4.35/4.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.35/4.53      inference('clc', [status(thm)], ['90', '91'])).
% 4.35/4.53  thf('103', plain,
% 4.35/4.53      (![X39 : $i, X40 : $i]:
% 4.35/4.53         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 4.35/4.53          | (v1_tops_1 @ X39 @ X40)
% 4.35/4.53          | ~ (v3_tex_2 @ X39 @ X40)
% 4.35/4.53          | ~ (l1_pre_topc @ X40)
% 4.35/4.53          | ~ (v3_tdlat_3 @ X40)
% 4.35/4.53          | ~ (v2_pre_topc @ X40)
% 4.35/4.53          | (v2_struct_0 @ X40))),
% 4.35/4.53      inference('cnf', [status(esa)], [t62_tex_2])).
% 4.35/4.53  thf('104', plain,
% 4.35/4.53      (((v2_struct_0 @ sk_A)
% 4.35/4.53        | ~ (v2_pre_topc @ sk_A)
% 4.35/4.53        | ~ (v3_tdlat_3 @ sk_A)
% 4.35/4.53        | ~ (l1_pre_topc @ sk_A)
% 4.35/4.53        | ~ (v3_tex_2 @ (sk_C @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A)
% 4.35/4.53        | (v1_tops_1 @ (sk_C @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))),
% 4.35/4.53      inference('sup-', [status(thm)], ['102', '103'])).
% 4.35/4.53  thf('105', plain, ((v2_pre_topc @ sk_A)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('106', plain, ((v3_tdlat_3 @ sk_A)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('107', plain, ((l1_pre_topc @ sk_A)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('108', plain,
% 4.35/4.53      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 4.35/4.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.35/4.53      inference('demod', [status(thm)], ['62', '63'])).
% 4.35/4.53  thf('109', plain,
% 4.35/4.53      (![X41 : $i, X42 : $i]:
% 4.35/4.53         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 4.35/4.53          | ~ (v2_tex_2 @ X41 @ X42)
% 4.35/4.53          | (v3_tex_2 @ (sk_C @ X41 @ X42) @ X42)
% 4.35/4.53          | ~ (l1_pre_topc @ X42)
% 4.35/4.53          | ~ (v3_tdlat_3 @ X42)
% 4.35/4.53          | ~ (v2_pre_topc @ X42)
% 4.35/4.53          | (v2_struct_0 @ X42))),
% 4.35/4.53      inference('cnf', [status(esa)], [t65_tex_2])).
% 4.35/4.53  thf('110', plain,
% 4.35/4.53      (((v2_struct_0 @ sk_A)
% 4.35/4.53        | ~ (v2_pre_topc @ sk_A)
% 4.35/4.53        | ~ (v3_tdlat_3 @ sk_A)
% 4.35/4.53        | ~ (l1_pre_topc @ sk_A)
% 4.35/4.53        | (v3_tex_2 @ (sk_C @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A)
% 4.35/4.53        | ~ (v2_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A))),
% 4.35/4.53      inference('sup-', [status(thm)], ['108', '109'])).
% 4.35/4.53  thf('111', plain, ((v2_pre_topc @ sk_A)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('112', plain, ((v3_tdlat_3 @ sk_A)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('113', plain, ((l1_pre_topc @ sk_A)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('114', plain, ((v2_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A)),
% 4.35/4.53      inference('clc', [status(thm)], ['87', '88'])).
% 4.35/4.53  thf('115', plain,
% 4.35/4.53      (((v2_struct_0 @ sk_A)
% 4.35/4.53        | (v3_tex_2 @ (sk_C @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))),
% 4.35/4.53      inference('demod', [status(thm)], ['110', '111', '112', '113', '114'])).
% 4.35/4.53  thf('116', plain, (~ (v2_struct_0 @ sk_A)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('117', plain, ((v3_tex_2 @ (sk_C @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A)),
% 4.35/4.53      inference('clc', [status(thm)], ['115', '116'])).
% 4.35/4.53  thf('118', plain,
% 4.35/4.53      (((v2_struct_0 @ sk_A)
% 4.35/4.53        | (v1_tops_1 @ (sk_C @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A))),
% 4.35/4.53      inference('demod', [status(thm)], ['104', '105', '106', '107', '117'])).
% 4.35/4.53  thf('119', plain, (~ (v2_struct_0 @ sk_A)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('120', plain,
% 4.35/4.53      ((v1_tops_1 @ (sk_C @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A)),
% 4.35/4.53      inference('clc', [status(thm)], ['118', '119'])).
% 4.35/4.53  thf('121', plain,
% 4.35/4.53      (((k2_pre_topc @ sk_A @ (sk_C @ (u1_struct_0 @ sk_B) @ sk_A))
% 4.35/4.53         = (u1_struct_0 @ sk_A))),
% 4.35/4.53      inference('demod', [status(thm)], ['101', '120'])).
% 4.35/4.53  thf('122', plain,
% 4.35/4.53      ((v1_tops_1 @ (sk_C @ (u1_struct_0 @ sk_B) @ sk_A) @ sk_A)),
% 4.35/4.53      inference('clc', [status(thm)], ['118', '119'])).
% 4.35/4.53  thf('123', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 4.35/4.53      inference('demod', [status(thm)], ['96', '121', '122'])).
% 4.35/4.53  thf('124', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 4.35/4.53      inference('demod', [status(thm)], ['96', '121', '122'])).
% 4.35/4.53  thf('125', plain,
% 4.35/4.53      ((((k6_domain_1 @ (k2_struct_0 @ sk_A) @ sk_D) = (k1_tarski @ sk_D))
% 4.35/4.53        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 4.35/4.53      inference('demod', [status(thm)], ['59', '123', '124'])).
% 4.35/4.53  thf('126', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('127', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('128', plain,
% 4.35/4.53      (![X23 : $i, X24 : $i]:
% 4.35/4.53         ((v1_xboole_0 @ X23)
% 4.35/4.53          | ~ (m1_subset_1 @ X24 @ X23)
% 4.35/4.53          | ((k6_domain_1 @ X23 @ X24) = (k1_tarski @ X24)))),
% 4.35/4.53      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 4.35/4.53  thf('129', plain,
% 4.35/4.53      ((((k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) = (k1_tarski @ sk_D))
% 4.35/4.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 4.35/4.53      inference('sup-', [status(thm)], ['127', '128'])).
% 4.35/4.53  thf('130', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf(dt_k6_domain_1, axiom,
% 4.35/4.53    (![A:$i,B:$i]:
% 4.35/4.53     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 4.35/4.53       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 4.35/4.53  thf('131', plain,
% 4.35/4.53      (![X21 : $i, X22 : $i]:
% 4.35/4.53         ((v1_xboole_0 @ X21)
% 4.35/4.53          | ~ (m1_subset_1 @ X22 @ X21)
% 4.35/4.53          | (m1_subset_1 @ (k6_domain_1 @ X21 @ X22) @ (k1_zfmisc_1 @ X21)))),
% 4.35/4.53      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 4.35/4.53  thf('132', plain,
% 4.35/4.53      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) @ 
% 4.35/4.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 4.35/4.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 4.35/4.53      inference('sup-', [status(thm)], ['130', '131'])).
% 4.35/4.53  thf('133', plain,
% 4.35/4.53      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 4.35/4.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 4.35/4.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 4.35/4.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 4.35/4.53      inference('sup+', [status(thm)], ['129', '132'])).
% 4.35/4.53  thf('134', plain,
% 4.35/4.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 4.35/4.53        | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 4.35/4.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 4.35/4.53      inference('simplify', [status(thm)], ['133'])).
% 4.35/4.53  thf(t39_pre_topc, axiom,
% 4.35/4.53    (![A:$i]:
% 4.35/4.53     ( ( l1_pre_topc @ A ) =>
% 4.35/4.53       ( ![B:$i]:
% 4.35/4.53         ( ( m1_pre_topc @ B @ A ) =>
% 4.35/4.53           ( ![C:$i]:
% 4.35/4.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 4.35/4.53               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 4.35/4.53  thf('135', plain,
% 4.35/4.53      (![X18 : $i, X19 : $i, X20 : $i]:
% 4.35/4.53         (~ (m1_pre_topc @ X18 @ X19)
% 4.35/4.53          | (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 4.35/4.53          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 4.35/4.53          | ~ (l1_pre_topc @ X19))),
% 4.35/4.53      inference('cnf', [status(esa)], [t39_pre_topc])).
% 4.35/4.53  thf('136', plain,
% 4.35/4.53      (![X0 : $i]:
% 4.35/4.53         ((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 4.35/4.53          | ~ (l1_pre_topc @ X0)
% 4.35/4.53          | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 4.35/4.53             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 4.35/4.53          | ~ (m1_pre_topc @ sk_B @ X0))),
% 4.35/4.53      inference('sup-', [status(thm)], ['134', '135'])).
% 4.35/4.53  thf('137', plain,
% 4.35/4.53      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 4.35/4.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.35/4.53        | ~ (l1_pre_topc @ sk_A)
% 4.35/4.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 4.35/4.53      inference('sup-', [status(thm)], ['126', '136'])).
% 4.35/4.53  thf('138', plain, ((l1_pre_topc @ sk_A)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('139', plain,
% 4.35/4.53      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 4.35/4.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.35/4.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 4.35/4.53      inference('demod', [status(thm)], ['137', '138'])).
% 4.35/4.53  thf('140', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 4.35/4.53      inference('demod', [status(thm)], ['96', '121', '122'])).
% 4.35/4.53  thf('141', plain,
% 4.35/4.53      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 4.35/4.53         (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 4.35/4.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 4.35/4.53      inference('demod', [status(thm)], ['139', '140'])).
% 4.35/4.53  thf('142', plain,
% 4.35/4.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 4.35/4.53        | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 4.35/4.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 4.35/4.53      inference('simplify', [status(thm)], ['133'])).
% 4.35/4.53  thf('143', plain,
% 4.35/4.53      ((m1_subset_1 @ sk_C_1 @ 
% 4.35/4.53        (k1_zfmisc_1 @ 
% 4.35/4.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf(t76_tex_2, axiom,
% 4.35/4.53    (![A:$i]:
% 4.35/4.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 4.35/4.53         ( l1_pre_topc @ A ) ) =>
% 4.35/4.53       ( ![B:$i]:
% 4.35/4.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 4.35/4.53             ( m1_pre_topc @ B @ A ) ) =>
% 4.35/4.53           ( ![C:$i]:
% 4.35/4.53             ( ( ( v1_funct_1 @ C ) & 
% 4.35/4.53                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 4.35/4.53                 ( v5_pre_topc @ C @ A @ B ) & 
% 4.35/4.53                 ( m1_subset_1 @
% 4.35/4.53                   C @ 
% 4.35/4.53                   ( k1_zfmisc_1 @
% 4.35/4.53                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 4.35/4.53               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 4.35/4.53                 ( ![D:$i]:
% 4.35/4.53                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 4.35/4.53                     ( ![E:$i]:
% 4.35/4.53                       ( ( m1_subset_1 @
% 4.35/4.53                           E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.35/4.53                         ( ( ( D ) = ( E ) ) =>
% 4.35/4.53                           ( ( k8_relset_1 @
% 4.35/4.53                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 4.35/4.53                               D ) =
% 4.35/4.53                             ( k2_pre_topc @ A @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 4.35/4.53  thf('144', plain,
% 4.35/4.53      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 4.35/4.53         ((v2_struct_0 @ X43)
% 4.35/4.53          | ~ (v4_tex_2 @ X43 @ X44)
% 4.35/4.53          | ~ (m1_pre_topc @ X43 @ X44)
% 4.35/4.53          | ~ (v3_borsuk_1 @ X45 @ X44 @ X43)
% 4.35/4.53          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 4.35/4.53          | ((X46) != (X47))
% 4.35/4.53          | ((k8_relset_1 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X43) @ X45 @ 
% 4.35/4.53              X46) = (k2_pre_topc @ X44 @ X47))
% 4.35/4.53          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 4.35/4.53          | ~ (m1_subset_1 @ X45 @ 
% 4.35/4.53               (k1_zfmisc_1 @ 
% 4.35/4.53                (k2_zfmisc_1 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X43))))
% 4.35/4.53          | ~ (v5_pre_topc @ X45 @ X44 @ X43)
% 4.35/4.53          | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X43))
% 4.35/4.53          | ~ (v1_funct_1 @ X45)
% 4.35/4.53          | ~ (l1_pre_topc @ X44)
% 4.35/4.53          | ~ (v3_tdlat_3 @ X44)
% 4.35/4.53          | ~ (v2_pre_topc @ X44)
% 4.35/4.53          | (v2_struct_0 @ X44))),
% 4.35/4.53      inference('cnf', [status(esa)], [t76_tex_2])).
% 4.35/4.53  thf('145', plain,
% 4.35/4.53      (![X43 : $i, X44 : $i, X45 : $i, X47 : $i]:
% 4.35/4.53         ((v2_struct_0 @ X44)
% 4.35/4.53          | ~ (v2_pre_topc @ X44)
% 4.35/4.53          | ~ (v3_tdlat_3 @ X44)
% 4.35/4.53          | ~ (l1_pre_topc @ X44)
% 4.35/4.53          | ~ (v1_funct_1 @ X45)
% 4.35/4.53          | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X43))
% 4.35/4.53          | ~ (v5_pre_topc @ X45 @ X44 @ X43)
% 4.35/4.53          | ~ (m1_subset_1 @ X45 @ 
% 4.35/4.53               (k1_zfmisc_1 @ 
% 4.35/4.53                (k2_zfmisc_1 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X43))))
% 4.35/4.53          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 4.35/4.53          | ((k8_relset_1 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X43) @ X45 @ 
% 4.35/4.53              X47) = (k2_pre_topc @ X44 @ X47))
% 4.35/4.53          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 4.35/4.53          | ~ (v3_borsuk_1 @ X45 @ X44 @ X43)
% 4.35/4.53          | ~ (m1_pre_topc @ X43 @ X44)
% 4.35/4.53          | ~ (v4_tex_2 @ X43 @ X44)
% 4.35/4.53          | (v2_struct_0 @ X43))),
% 4.35/4.53      inference('simplify', [status(thm)], ['144'])).
% 4.35/4.53  thf('146', plain,
% 4.35/4.53      (![X0 : $i]:
% 4.35/4.53         ((v2_struct_0 @ sk_B)
% 4.35/4.53          | ~ (v4_tex_2 @ sk_B @ sk_A)
% 4.35/4.53          | ~ (m1_pre_topc @ sk_B @ sk_A)
% 4.35/4.53          | ~ (v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B)
% 4.35/4.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 4.35/4.53          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 4.35/4.53              sk_C_1 @ X0) = (k2_pre_topc @ sk_A @ X0))
% 4.35/4.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.35/4.53          | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B)
% 4.35/4.53          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 4.35/4.53               (u1_struct_0 @ sk_B))
% 4.35/4.53          | ~ (v1_funct_1 @ sk_C_1)
% 4.35/4.53          | ~ (l1_pre_topc @ sk_A)
% 4.35/4.53          | ~ (v3_tdlat_3 @ sk_A)
% 4.35/4.53          | ~ (v2_pre_topc @ sk_A)
% 4.35/4.53          | (v2_struct_0 @ sk_A))),
% 4.35/4.53      inference('sup-', [status(thm)], ['143', '145'])).
% 4.35/4.53  thf('147', plain, ((v4_tex_2 @ sk_B @ sk_A)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('148', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('149', plain, ((v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('150', plain, ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('151', plain,
% 4.35/4.53      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('152', plain, ((v1_funct_1 @ sk_C_1)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('153', plain, ((l1_pre_topc @ sk_A)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('154', plain, ((v3_tdlat_3 @ sk_A)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('155', plain, ((v2_pre_topc @ sk_A)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('156', plain,
% 4.35/4.53      (![X0 : $i]:
% 4.35/4.53         ((v2_struct_0 @ sk_B)
% 4.35/4.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 4.35/4.53          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 4.35/4.53              sk_C_1 @ X0) = (k2_pre_topc @ sk_A @ X0))
% 4.35/4.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.35/4.53          | (v2_struct_0 @ sk_A))),
% 4.35/4.53      inference('demod', [status(thm)],
% 4.35/4.53                ['146', '147', '148', '149', '150', '151', '152', '153', 
% 4.35/4.53                 '154', '155'])).
% 4.35/4.53  thf('157', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 4.35/4.53      inference('demod', [status(thm)], ['96', '121', '122'])).
% 4.35/4.53  thf('158', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 4.35/4.53      inference('demod', [status(thm)], ['96', '121', '122'])).
% 4.35/4.53  thf('159', plain,
% 4.35/4.53      (![X0 : $i]:
% 4.35/4.53         ((v2_struct_0 @ sk_B)
% 4.35/4.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 4.35/4.53          | ((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 4.35/4.53              sk_C_1 @ X0) = (k2_pre_topc @ sk_A @ X0))
% 4.35/4.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 4.35/4.53          | (v2_struct_0 @ sk_A))),
% 4.35/4.53      inference('demod', [status(thm)], ['156', '157', '158'])).
% 4.35/4.53  thf('160', plain,
% 4.35/4.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 4.35/4.53        | (v2_struct_0 @ sk_A)
% 4.35/4.53        | ~ (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 4.35/4.53             (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 4.35/4.53        | ((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 4.35/4.53            sk_C_1 @ (k1_tarski @ sk_D))
% 4.35/4.53            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 4.35/4.53        | (v2_struct_0 @ sk_B))),
% 4.35/4.53      inference('sup-', [status(thm)], ['142', '159'])).
% 4.35/4.53  thf('161', plain,
% 4.35/4.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 4.35/4.53        | (v2_struct_0 @ sk_B)
% 4.35/4.53        | ((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 4.35/4.53            sk_C_1 @ (k1_tarski @ sk_D))
% 4.35/4.53            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 4.35/4.53        | (v2_struct_0 @ sk_A)
% 4.35/4.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 4.35/4.53      inference('sup-', [status(thm)], ['141', '160'])).
% 4.35/4.53  thf('162', plain,
% 4.35/4.53      (((v2_struct_0 @ sk_A)
% 4.35/4.53        | ((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 4.35/4.53            sk_C_1 @ (k1_tarski @ sk_D))
% 4.35/4.53            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 4.35/4.53        | (v2_struct_0 @ sk_B)
% 4.35/4.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 4.35/4.53      inference('simplify', [status(thm)], ['161'])).
% 4.35/4.53  thf('163', plain,
% 4.35/4.53      ((((k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) = (k1_tarski @ sk_D))
% 4.35/4.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 4.35/4.53      inference('sup-', [status(thm)], ['127', '128'])).
% 4.35/4.53  thf('164', plain,
% 4.35/4.53      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1 @ 
% 4.35/4.53         (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 4.35/4.53         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_E)))),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('165', plain, (((sk_D) = (sk_E))),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('166', plain,
% 4.35/4.53      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1 @ 
% 4.35/4.53         (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 4.35/4.53         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 4.35/4.53      inference('demod', [status(thm)], ['164', '165'])).
% 4.35/4.53  thf('167', plain,
% 4.35/4.53      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1 @ 
% 4.35/4.53          (k1_tarski @ sk_D))
% 4.35/4.53          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 4.35/4.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 4.35/4.53      inference('sup-', [status(thm)], ['163', '166'])).
% 4.35/4.53  thf('168', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 4.35/4.53      inference('demod', [status(thm)], ['96', '121', '122'])).
% 4.35/4.53  thf('169', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 4.35/4.53      inference('demod', [status(thm)], ['96', '121', '122'])).
% 4.35/4.53  thf('170', plain,
% 4.35/4.53      ((((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1 @ 
% 4.35/4.53          (k1_tarski @ sk_D))
% 4.35/4.53          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (k2_struct_0 @ sk_A) @ sk_D)))
% 4.35/4.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 4.35/4.53      inference('demod', [status(thm)], ['167', '168', '169'])).
% 4.35/4.53  thf('171', plain,
% 4.35/4.53      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 4.35/4.53          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (k2_struct_0 @ sk_A) @ sk_D)))
% 4.35/4.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 4.35/4.53        | (v2_struct_0 @ sk_B)
% 4.35/4.53        | (v2_struct_0 @ sk_A)
% 4.35/4.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 4.35/4.53      inference('sup-', [status(thm)], ['162', '170'])).
% 4.35/4.53  thf('172', plain,
% 4.35/4.53      (((v2_struct_0 @ sk_A)
% 4.35/4.53        | (v2_struct_0 @ sk_B)
% 4.35/4.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 4.35/4.53        | ((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 4.35/4.53            != (k2_pre_topc @ sk_A @ 
% 4.35/4.53                (k6_domain_1 @ (k2_struct_0 @ sk_A) @ sk_D))))),
% 4.35/4.53      inference('simplify', [status(thm)], ['171'])).
% 4.35/4.53  thf('173', plain,
% 4.35/4.53      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 4.35/4.53          != (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 4.35/4.53        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 4.35/4.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 4.35/4.53        | (v2_struct_0 @ sk_B)
% 4.35/4.53        | (v2_struct_0 @ sk_A))),
% 4.35/4.53      inference('sup-', [status(thm)], ['125', '172'])).
% 4.35/4.53  thf('174', plain,
% 4.35/4.53      (((v2_struct_0 @ sk_A)
% 4.35/4.53        | (v2_struct_0 @ sk_B)
% 4.35/4.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 4.35/4.53        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 4.35/4.53      inference('simplify', [status(thm)], ['173'])).
% 4.35/4.53  thf('175', plain,
% 4.35/4.53      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 4.35/4.53        | ~ (v2_pre_topc @ sk_B)
% 4.35/4.53        | ~ (v3_tdlat_3 @ sk_B)
% 4.35/4.53        | ~ (v1_tdlat_3 @ sk_B)
% 4.35/4.53        | (v2_struct_0 @ sk_B)
% 4.35/4.53        | ~ (l1_pre_topc @ sk_B)
% 4.35/4.53        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 4.35/4.53        | (v2_struct_0 @ sk_B)
% 4.35/4.53        | (v2_struct_0 @ sk_A))),
% 4.35/4.53      inference('sup+', [status(thm)], ['54', '174'])).
% 4.35/4.53  thf('176', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf(cc1_pre_topc, axiom,
% 4.35/4.53    (![A:$i]:
% 4.35/4.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.35/4.53       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 4.35/4.53  thf('177', plain,
% 4.35/4.53      (![X12 : $i, X13 : $i]:
% 4.35/4.53         (~ (m1_pre_topc @ X12 @ X13)
% 4.35/4.53          | (v2_pre_topc @ X12)
% 4.35/4.53          | ~ (l1_pre_topc @ X13)
% 4.35/4.53          | ~ (v2_pre_topc @ X13))),
% 4.35/4.53      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 4.35/4.53  thf('178', plain,
% 4.35/4.53      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_B))),
% 4.35/4.53      inference('sup-', [status(thm)], ['176', '177'])).
% 4.35/4.53  thf('179', plain, ((v2_pre_topc @ sk_A)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('180', plain, ((l1_pre_topc @ sk_A)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('181', plain, ((v2_pre_topc @ sk_B)),
% 4.35/4.53      inference('demod', [status(thm)], ['178', '179', '180'])).
% 4.35/4.53  thf('182', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf(cc18_tex_2, axiom,
% 4.35/4.53    (![A:$i]:
% 4.35/4.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 4.35/4.53       ( ![B:$i]:
% 4.35/4.53         ( ( m1_pre_topc @ B @ A ) =>
% 4.35/4.53           ( ( v1_tdlat_3 @ B ) => ( v3_tdlat_3 @ B ) ) ) ) ))).
% 4.35/4.53  thf('183', plain,
% 4.35/4.53      (![X30 : $i, X31 : $i]:
% 4.35/4.53         (~ (m1_pre_topc @ X30 @ X31)
% 4.35/4.53          | (v3_tdlat_3 @ X30)
% 4.35/4.53          | ~ (v1_tdlat_3 @ X30)
% 4.35/4.53          | ~ (l1_pre_topc @ X31)
% 4.35/4.53          | (v2_struct_0 @ X31))),
% 4.35/4.53      inference('cnf', [status(esa)], [cc18_tex_2])).
% 4.35/4.53  thf('184', plain,
% 4.35/4.53      (((v2_struct_0 @ sk_A)
% 4.35/4.53        | ~ (l1_pre_topc @ sk_A)
% 4.35/4.53        | ~ (v1_tdlat_3 @ sk_B)
% 4.35/4.53        | (v3_tdlat_3 @ sk_B))),
% 4.35/4.53      inference('sup-', [status(thm)], ['182', '183'])).
% 4.35/4.53  thf('185', plain, ((l1_pre_topc @ sk_A)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('186', plain,
% 4.35/4.53      (((v2_struct_0 @ sk_A) | ~ (v1_tdlat_3 @ sk_B) | (v3_tdlat_3 @ sk_B))),
% 4.35/4.53      inference('demod', [status(thm)], ['184', '185'])).
% 4.35/4.53  thf('187', plain, (~ (v2_struct_0 @ sk_A)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('188', plain, (((v3_tdlat_3 @ sk_B) | ~ (v1_tdlat_3 @ sk_B))),
% 4.35/4.53      inference('clc', [status(thm)], ['186', '187'])).
% 4.35/4.53  thf('189', plain, ((v1_tdlat_3 @ sk_B)),
% 4.35/4.53      inference('clc', [status(thm)], ['81', '82'])).
% 4.35/4.53  thf('190', plain, ((v3_tdlat_3 @ sk_B)),
% 4.35/4.53      inference('demod', [status(thm)], ['188', '189'])).
% 4.35/4.53  thf('191', plain, ((v1_tdlat_3 @ sk_B)),
% 4.35/4.53      inference('clc', [status(thm)], ['81', '82'])).
% 4.35/4.53  thf('192', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf(dt_m1_pre_topc, axiom,
% 4.35/4.53    (![A:$i]:
% 4.35/4.53     ( ( l1_pre_topc @ A ) =>
% 4.35/4.53       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 4.35/4.53  thf('193', plain,
% 4.35/4.53      (![X15 : $i, X16 : $i]:
% 4.35/4.53         (~ (m1_pre_topc @ X15 @ X16)
% 4.35/4.53          | (l1_pre_topc @ X15)
% 4.35/4.53          | ~ (l1_pre_topc @ X16))),
% 4.35/4.53      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 4.35/4.53  thf('194', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 4.35/4.53      inference('sup-', [status(thm)], ['192', '193'])).
% 4.35/4.53  thf('195', plain, ((l1_pre_topc @ sk_A)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('196', plain, ((l1_pre_topc @ sk_B)),
% 4.35/4.53      inference('demod', [status(thm)], ['194', '195'])).
% 4.35/4.53  thf('197', plain,
% 4.35/4.53      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 4.35/4.53        | (v2_struct_0 @ sk_B)
% 4.35/4.53        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 4.35/4.53        | (v2_struct_0 @ sk_B)
% 4.35/4.53        | (v2_struct_0 @ sk_A))),
% 4.35/4.53      inference('demod', [status(thm)], ['175', '181', '190', '191', '196'])).
% 4.35/4.53  thf('198', plain,
% 4.35/4.53      (((v2_struct_0 @ sk_A)
% 4.35/4.53        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 4.35/4.53        | (v2_struct_0 @ sk_B)
% 4.35/4.53        | (v1_xboole_0 @ (k2_struct_0 @ sk_B)))),
% 4.35/4.53      inference('simplify', [status(thm)], ['197'])).
% 4.35/4.53  thf(fc5_struct_0, axiom,
% 4.35/4.53    (![A:$i]:
% 4.35/4.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 4.35/4.53       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 4.35/4.53  thf('199', plain,
% 4.35/4.53      (![X17 : $i]:
% 4.35/4.53         (~ (v1_xboole_0 @ (k2_struct_0 @ X17))
% 4.35/4.53          | ~ (l1_struct_0 @ X17)
% 4.35/4.53          | (v2_struct_0 @ X17))),
% 4.35/4.53      inference('cnf', [status(esa)], [fc5_struct_0])).
% 4.35/4.53  thf('200', plain,
% 4.35/4.53      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 4.35/4.53        | (v2_struct_0 @ sk_B)
% 4.35/4.53        | (v2_struct_0 @ sk_A)
% 4.35/4.53        | (v2_struct_0 @ sk_A)
% 4.35/4.53        | ~ (l1_struct_0 @ sk_A))),
% 4.35/4.53      inference('sup-', [status(thm)], ['198', '199'])).
% 4.35/4.53  thf('201', plain, ((l1_pre_topc @ sk_A)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf(dt_l1_pre_topc, axiom,
% 4.35/4.53    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 4.35/4.53  thf('202', plain,
% 4.35/4.53      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_pre_topc @ X14))),
% 4.35/4.53      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 4.35/4.53  thf('203', plain, ((l1_struct_0 @ sk_A)),
% 4.35/4.53      inference('sup-', [status(thm)], ['201', '202'])).
% 4.35/4.53  thf('204', plain,
% 4.35/4.53      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 4.35/4.53        | (v2_struct_0 @ sk_B)
% 4.35/4.53        | (v2_struct_0 @ sk_A)
% 4.35/4.53        | (v2_struct_0 @ sk_A))),
% 4.35/4.53      inference('demod', [status(thm)], ['200', '203'])).
% 4.35/4.53  thf('205', plain,
% 4.35/4.53      (((v2_struct_0 @ sk_A)
% 4.35/4.53        | (v2_struct_0 @ sk_B)
% 4.35/4.53        | (v1_xboole_0 @ (k2_struct_0 @ sk_B)))),
% 4.35/4.53      inference('simplify', [status(thm)], ['204'])).
% 4.35/4.53  thf('206', plain, (~ (v2_struct_0 @ sk_A)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('207', plain,
% 4.35/4.53      (((v1_xboole_0 @ (k2_struct_0 @ sk_B)) | (v2_struct_0 @ sk_B))),
% 4.35/4.53      inference('clc', [status(thm)], ['205', '206'])).
% 4.35/4.53  thf('208', plain, (~ (v2_struct_0 @ sk_B)),
% 4.35/4.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.53  thf('209', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_B))),
% 4.35/4.53      inference('clc', [status(thm)], ['207', '208'])).
% 4.35/4.53  thf('210', plain,
% 4.35/4.53      (![X17 : $i]:
% 4.35/4.53         (~ (v1_xboole_0 @ (k2_struct_0 @ X17))
% 4.35/4.53          | ~ (l1_struct_0 @ X17)
% 4.35/4.53          | (v2_struct_0 @ X17))),
% 4.35/4.53      inference('cnf', [status(esa)], [fc5_struct_0])).
% 4.35/4.53  thf('211', plain, (((v2_struct_0 @ sk_B) | ~ (l1_struct_0 @ sk_B))),
% 4.35/4.53      inference('sup-', [status(thm)], ['209', '210'])).
% 4.35/4.53  thf('212', plain, ((l1_pre_topc @ sk_B)),
% 4.35/4.53      inference('demod', [status(thm)], ['194', '195'])).
% 4.35/4.53  thf('213', plain,
% 4.35/4.53      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_pre_topc @ X14))),
% 4.35/4.53      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 4.35/4.53  thf('214', plain, ((l1_struct_0 @ sk_B)),
% 4.35/4.53      inference('sup-', [status(thm)], ['212', '213'])).
% 4.35/4.53  thf('215', plain, ((v2_struct_0 @ sk_B)),
% 4.35/4.53      inference('demod', [status(thm)], ['211', '214'])).
% 4.35/4.53  thf('216', plain, ($false), inference('demod', [status(thm)], ['0', '215'])).
% 4.35/4.53  
% 4.35/4.53  % SZS output end Refutation
% 4.35/4.53  
% 4.35/4.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
