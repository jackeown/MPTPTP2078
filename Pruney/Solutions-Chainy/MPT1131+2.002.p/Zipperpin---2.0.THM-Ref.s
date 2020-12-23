%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cNc6vfzL9P

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:26 EST 2020

% Result     : Theorem 5.48s
% Output     : Refutation 5.48s
% Verified   : 
% Statistics : Number of formulae       :  278 (1981 expanded)
%              Number of leaves         :   55 ( 592 expanded)
%              Depth                    :   41
%              Number of atoms          : 3291 (48173 expanded)
%              Number of equality atoms :   21 ( 685 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X43: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X43 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) ) )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(dt_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) )
        & ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X41: $i,X42: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ X41 @ X42 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t62_pre_topc,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ ( u1_struct_0 @ B ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ ( u1_struct_0 @ B ) ) ) ) )
                 => ( ( C = D )
                   => ( ( v5_pre_topc @ C @ A @ B )
                    <=> ( v5_pre_topc @ D @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ B ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ( v2_pre_topc @ B )
              & ( l1_pre_topc @ B ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ! [D: $i] :
                    ( ( ( v1_funct_1 @ D )
                      & ( v1_funct_2 @ D @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ ( u1_struct_0 @ B ) )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ ( u1_struct_0 @ B ) ) ) ) )
                   => ( ( C = D )
                     => ( ( v5_pre_topc @ C @ A @ B )
                      <=> ( v5_pre_topc @ D @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_pre_topc])).

thf('4',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_C_1 = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(d12_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( v5_pre_topc @ C @ A @ B )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                   => ( ( v4_pre_topc @ D @ B )
                     => ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ A ) ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ( m1_subset_1 @ ( sk_D @ X11 @ X10 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v5_pre_topc @ X11 @ X12 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( v1_funct_2 @ X11 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('8',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_2 ) )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 )
    | ( m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) )
    | ~ ( l1_pre_topc @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    sk_C_1 = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 )
    | ( m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['8','9','12','13'])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['3','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 )
    | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 )
   <= ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,(
    sk_C_1 = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 )
   <= ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 )
    | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    sk_C_1 = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 )
    | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 )
   <= ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 )
   <= ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('27',plain,
    ( ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 )
    | ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 )
    | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    sk_C_1 = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 )
    | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 )
    | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference(split,[status(esa)],['30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ( m1_subset_1 @ ( sk_D @ X11 @ X10 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v5_pre_topc @ X11 @ X12 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( v1_funct_2 @ X11 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('34',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) )
    | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 )
    | ( m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) )
    | ~ ( l1_pre_topc @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 )
    | ( m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36','37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('41',plain,
    ( ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 )
    | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,(
    sk_C_1 = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('46',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( v5_pre_topc @ X11 @ X12 @ X10 )
      | ~ ( v4_pre_topc @ X13 @ X10 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) @ X11 @ X13 ) @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( v1_funct_2 @ X11 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C_1 @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v4_pre_topc @ X0 @ sk_B_2 )
      | ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 )
      | ~ ( l1_pre_topc @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('50',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C_1 @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v4_pre_topc @ X0 @ sk_B_2 )
      | ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf(fc6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
        & ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('52',plain,(
    ! [X44: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X44 ) @ ( u1_pre_topc @ X44 ) ) )
      | ~ ( l1_pre_topc @ X44 )
      | ~ ( v2_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_pre_topc @ A )
      <=> ( ! [B: $i] :
              ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) )
                      & ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) )
                   => ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ) )
          & ! [B: $i] :
              ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) )
               => ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) )
          & ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_5 @ B @ A )
    <=> ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
       => ( zip_tseitin_4 @ B @ A ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_4 @ B @ A )
    <=> ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) )
       => ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_5,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_3 @ B @ A )
    <=> ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
       => ! [C: $i] :
            ( zip_tseitin_2 @ C @ B @ A ) ) ) )).

thf(zf_stmt_7,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
    <=> ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
       => ( zip_tseitin_1 @ C @ B @ A ) ) ) )).

thf(zf_stmt_9,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_10,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
    <=> ( ( zip_tseitin_0 @ C @ B @ A )
       => ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_11,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_12,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
    <=> ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) )
        & ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_13,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_pre_topc @ A )
      <=> ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
          & ! [B: $i] :
              ( zip_tseitin_5 @ B @ A )
          & ! [B: $i] :
              ( zip_tseitin_3 @ B @ A ) ) ) ) )).

thf('54',plain,(
    ! [X36: $i] :
      ( ~ ( v2_pre_topc @ X36 )
      | ( r2_hidden @ ( u1_struct_0 @ X36 ) @ ( u1_pre_topc @ X36 ) )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('56',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['55'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('57',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('58',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('59',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( r2_hidden @ X39 @ ( u1_pre_topc @ X40 ) )
      | ( v3_pre_topc @ X39 @ X40 )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(t60_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v3_pre_topc @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
        <=> ( ( v3_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) )).

thf('64',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( v3_pre_topc @ X45 @ ( g1_pre_topc @ ( u1_struct_0 @ X46 ) @ ( u1_pre_topc @ X46 ) ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X46 ) @ ( u1_pre_topc @ X46 ) ) ) ) )
      | ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v2_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[t60_pre_topc])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( m1_subset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['53','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( m1_subset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['52','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X36: $i,X38: $i] :
      ( ~ ( v2_pre_topc @ X36 )
      | ( zip_tseitin_5 @ X38 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_5 @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( zip_tseitin_5 @ X0 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X43: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X43 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) ) )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('79',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) ) )
      | ( zip_tseitin_4 @ X33 @ X34 )
      | ~ ( zip_tseitin_5 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( zip_tseitin_5 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ( zip_tseitin_4 @ ( u1_pre_topc @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( zip_tseitin_4 @ ( u1_pre_topc @ sk_A ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    zip_tseitin_4 @ ( u1_pre_topc @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('85',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ X30 @ ( u1_pre_topc @ X31 ) )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X31 ) @ X30 ) @ ( u1_pre_topc @ X31 ) )
      | ~ ( zip_tseitin_4 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_4 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( u1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    ! [X36: $i] :
      ( ~ ( v2_pre_topc @ X36 )
      | ( r2_hidden @ ( u1_struct_0 @ X36 ) @ ( u1_pre_topc @ X36 ) )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('89',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X16 @ X14 @ X17 )
      | ~ ( r2_hidden @ X16 @ ( u1_pre_topc @ X17 ) )
      | ~ ( r2_hidden @ X14 @ ( u1_pre_topc @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) )
      | ( zip_tseitin_0 @ ( u1_struct_0 @ X0 ) @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['87','90'])).

thf('92',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X16 @ ( u1_pre_topc @ X15 ) )
      | ~ ( zip_tseitin_0 @ X16 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('96',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('98',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('102',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( v3_pre_topc @ X47 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X46 ) @ ( u1_pre_topc @ X46 ) ) ) ) )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v2_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[t60_pre_topc])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['100','103'])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('109',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('111',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','111'])).

thf('113',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C_1 @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v4_pre_topc @ X0 @ sk_B_2 )
      | ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['51','115'])).

thf('117',plain,
    ( ! [X0: $i] :
        ( ~ ( v4_pre_topc @ X0 @ sk_B_2 )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C_1 @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) )
        | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['44','116'])).

thf('118',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C_1 @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( v4_pre_topc @ X0 @ sk_B_2 ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['40','117'])).

thf('119',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C_1 @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( v4_pre_topc @ X0 @ sk_B_2 ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( ( ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 )
      | ~ ( v4_pre_topc @ ( sk_D @ sk_C_1 @ sk_B_2 @ sk_A ) @ sk_B_2 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C_1 @ ( sk_D @ sk_C_1 @ sk_B_2 @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['39','120'])).

thf('122',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ( v4_pre_topc @ ( sk_D @ X11 @ X10 @ X12 ) @ X10 )
      | ( v5_pre_topc @ X11 @ X12 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( v1_funct_2 @ X11 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('124',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) )
    | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 )
    | ( v4_pre_topc @ ( sk_D @ sk_C_1 @ sk_B_2 @ sk_A ) @ sk_B_2 )
    | ~ ( l1_pre_topc @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 )
    | ( v4_pre_topc @ ( sk_D @ sk_C_1 @ sk_B_2 @ sk_A ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['124','125','126','127','128'])).

thf('130',plain,
    ( ( ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C_1 @ ( sk_D @ sk_C_1 @ sk_B_2 @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 ) ),
    inference(clc,[status(thm)],['121','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) )
      | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['131','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf(t61_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v4_pre_topc @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
        <=> ( ( v4_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) )).

thf('142',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v4_pre_topc @ X48 @ ( g1_pre_topc @ ( u1_struct_0 @ X49 ) @ ( u1_pre_topc @ X49 ) ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X49 ) @ ( u1_pre_topc @ X49 ) ) ) ) )
      | ( v4_pre_topc @ X48 @ X49 )
      | ~ ( l1_pre_topc @ X49 )
      | ~ ( v2_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t61_pre_topc])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ X1 @ X0 )
      | ~ ( v4_pre_topc @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_pre_topc @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( v4_pre_topc @ X1 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,
    ( ( ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 )
      | ~ ( m1_subset_1 @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C_1 @ ( sk_D @ sk_C_1 @ sk_B_2 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C_1 @ ( sk_D @ sk_C_1 @ sk_B_2 @ sk_A ) ) @ sk_A ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['130','144'])).

thf('146',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('147',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ( m1_subset_1 @ ( k8_relset_1 @ X7 @ X8 @ X6 @ X9 ) @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relset_1])).

thf('148',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C_1 @ ( sk_D @ sk_C_1 @ sk_B_2 @ sk_A ) ) @ sk_A ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['145','148','149','150'])).

thf('152',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) @ X11 @ ( sk_D @ X11 @ X10 @ X12 ) ) @ X12 )
      | ( v5_pre_topc @ X11 @ X12 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( v1_funct_2 @ X11 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('153',plain,
    ( ( ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 )
      | ~ ( l1_pre_topc @ sk_B_2 ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 )
      | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['153','154','155','156','157','158'])).

thf('160',plain,
    ( ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,
    ( ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 )
   <= ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference(split,[status(esa)],['18'])).

thf('162',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 )
    | ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,
    ( ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('164',plain,
    ( ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 )
   <= ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 ) ),
    inference(split,[status(esa)],['30'])).

thf('165',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 ) ),
    inference('sat_resolution*',[status(thm)],['27','31','162','165'])).

thf('167',plain,(
    ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 ) ),
    inference(simpl_trail,[status(thm)],['21','166'])).

thf('168',plain,(
    m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['17','167'])).

thf('169',plain,
    ( ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 )
   <= ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference(split,[status(esa)],['41'])).

thf('170',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( v5_pre_topc @ X11 @ X12 @ X10 )
      | ~ ( v4_pre_topc @ X13 @ X10 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) @ X11 @ X13 ) @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( v1_funct_2 @ X11 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('172',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C_1 @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_B_2 )
      | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 )
      | ~ ( l1_pre_topc @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C_1 @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_B_2 )
      | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['172','173','174','175','176'])).

thf('178',plain,
    ( ! [X0: $i] :
        ( ~ ( v4_pre_topc @ X0 @ sk_B_2 )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C_1 @ X0 ) @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) ) )
   <= ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['169','177'])).

thf('179',plain,
    ( ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 ) ),
    inference(split,[status(esa)],['24'])).

thf('180',plain,(
    v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 ),
    inference('sat_resolution*',[status(thm)],['27','31','162','179'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ X0 @ sk_B_2 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C_1 @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['178','180'])).

thf('182',plain,
    ( ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C_1 @ ( sk_D @ sk_C_1 @ sk_B_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( sk_D @ sk_C_1 @ sk_B_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['168','181'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('184',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('185',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ( v4_pre_topc @ ( sk_D @ X11 @ X10 @ X12 ) @ X10 )
      | ( v5_pre_topc @ X11 @ X12 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( v1_funct_2 @ X11 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('186',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_2 ) )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 )
    | ( v4_pre_topc @ ( sk_D @ sk_C_1 @ sk_B_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B_2 )
    | ~ ( l1_pre_topc @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('189',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 )
    | ( v4_pre_topc @ ( sk_D @ sk_C_1 @ sk_B_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['186','187','188','189'])).

thf('191',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( sk_D @ sk_C_1 @ sk_B_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B_2 )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['183','190'])).

thf('192',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( v4_pre_topc @ ( sk_D @ sk_C_1 @ sk_B_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B_2 )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['191','192'])).

thf('194',plain,(
    ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 ) ),
    inference(simpl_trail,[status(thm)],['21','166'])).

thf('195',plain,(
    v4_pre_topc @ ( sk_D @ sk_C_1 @ sk_B_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B_2 ),
    inference(clc,[status(thm)],['193','194'])).

thf('196',plain,(
    v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C_1 @ ( sk_D @ sk_C_1 @ sk_B_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) @ sk_A ),
    inference(demod,[status(thm)],['182','195'])).

thf('197',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('198',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( v4_pre_topc @ X50 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ( v4_pre_topc @ X50 @ ( g1_pre_topc @ ( u1_struct_0 @ X49 ) @ ( u1_pre_topc @ X49 ) ) )
      | ~ ( l1_pre_topc @ X49 )
      | ~ ( v2_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t61_pre_topc])).

thf('199',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C_1 @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C_1 @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C_1 @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C_1 @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['199','200','201'])).

thf('203',plain,(
    v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C_1 @ ( sk_D @ sk_C_1 @ sk_B_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['196','202'])).

thf('204',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('205',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) @ X11 @ ( sk_D @ X11 @ X10 @ X12 ) ) @ X12 )
      | ( v5_pre_topc @ X11 @ X12 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( v1_funct_2 @ X11 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('206',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) @ X2 @ ( sk_D @ X2 @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ( v5_pre_topc @ X2 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,
    ( ~ ( l1_pre_topc @ sk_B_2 )
    | ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_2 ) ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_2 ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['203','206'])).

thf('208',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,
    ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('210',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,
    ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('212',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,
    ( ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['207','208','209','210','211','212','213','214','215'])).

thf('217',plain,(
    ~ ( v5_pre_topc @ sk_C_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_2 ) ),
    inference(simpl_trail,[status(thm)],['21','166'])).

thf('218',plain,(
    ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['216','217'])).

thf('219',plain,(
    ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['2','218'])).

thf('220',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    $false ),
    inference(demod,[status(thm)],['219','220'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cNc6vfzL9P
% 0.15/0.37  % Computer   : n008.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 11:43:30 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.22/0.37  % Number of cores: 8
% 0.22/0.37  % Python version: Python 3.6.8
% 0.22/0.38  % Running in FO mode
% 5.48/5.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.48/5.68  % Solved by: fo/fo7.sh
% 5.48/5.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.48/5.68  % done 4165 iterations in 5.186s
% 5.48/5.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.48/5.68  % SZS output start Refutation
% 5.48/5.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.48/5.68  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 5.48/5.68  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 5.48/5.68  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 5.48/5.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.48/5.68  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 5.48/5.68  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 5.48/5.68  thf(sk_D_1_type, type, sk_D_1: $i).
% 5.48/5.68  thf(sk_C_1_type, type, sk_C_1: $i).
% 5.48/5.68  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 5.48/5.68  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 5.48/5.68  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 5.48/5.68  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 5.48/5.68  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 5.48/5.68  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 5.48/5.68  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 5.48/5.68  thf(sk_A_type, type, sk_A: $i).
% 5.48/5.68  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 5.48/5.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.48/5.68  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 5.48/5.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.48/5.68  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 5.48/5.68  thf(sk_B_2_type, type, sk_B_2: $i).
% 5.48/5.68  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 5.48/5.68  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 5.48/5.68  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 5.48/5.68  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 5.48/5.68  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 5.48/5.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.48/5.68  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 5.48/5.68  thf(dt_u1_pre_topc, axiom,
% 5.48/5.68    (![A:$i]:
% 5.48/5.68     ( ( l1_pre_topc @ A ) =>
% 5.48/5.68       ( m1_subset_1 @
% 5.48/5.68         ( u1_pre_topc @ A ) @ 
% 5.48/5.68         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 5.48/5.68  thf('0', plain,
% 5.48/5.68      (![X43 : $i]:
% 5.48/5.68         ((m1_subset_1 @ (u1_pre_topc @ X43) @ 
% 5.48/5.68           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43))))
% 5.48/5.68          | ~ (l1_pre_topc @ X43))),
% 5.48/5.68      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 5.48/5.68  thf(dt_g1_pre_topc, axiom,
% 5.48/5.68    (![A:$i,B:$i]:
% 5.48/5.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 5.48/5.68       ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) ) & 
% 5.48/5.68         ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ))).
% 5.48/5.68  thf('1', plain,
% 5.48/5.68      (![X41 : $i, X42 : $i]:
% 5.48/5.68         ((l1_pre_topc @ (g1_pre_topc @ X41 @ X42))
% 5.48/5.68          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X41))))),
% 5.48/5.68      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 5.48/5.68  thf('2', plain,
% 5.48/5.68      (![X0 : $i]:
% 5.48/5.68         (~ (l1_pre_topc @ X0)
% 5.48/5.68          | (l1_pre_topc @ 
% 5.48/5.68             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 5.48/5.68      inference('sup-', [status(thm)], ['0', '1'])).
% 5.48/5.68  thf('3', plain,
% 5.48/5.68      (![X0 : $i]:
% 5.48/5.68         (~ (l1_pre_topc @ X0)
% 5.48/5.68          | (l1_pre_topc @ 
% 5.48/5.68             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 5.48/5.68      inference('sup-', [status(thm)], ['0', '1'])).
% 5.48/5.68  thf(t62_pre_topc, conjecture,
% 5.48/5.68    (![A:$i]:
% 5.48/5.68     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.48/5.68       ( ![B:$i]:
% 5.48/5.68         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 5.48/5.68           ( ![C:$i]:
% 5.48/5.68             ( ( ( v1_funct_1 @ C ) & 
% 5.48/5.68                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 5.48/5.68                 ( m1_subset_1 @
% 5.48/5.68                   C @ 
% 5.48/5.68                   ( k1_zfmisc_1 @
% 5.48/5.68                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 5.48/5.68               ( ![D:$i]:
% 5.48/5.68                 ( ( ( v1_funct_1 @ D ) & 
% 5.48/5.68                     ( v1_funct_2 @
% 5.48/5.68                       D @ 
% 5.48/5.68                       ( u1_struct_0 @
% 5.48/5.68                         ( g1_pre_topc @
% 5.48/5.68                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 5.48/5.68                       ( u1_struct_0 @ B ) ) & 
% 5.48/5.68                     ( m1_subset_1 @
% 5.48/5.68                       D @ 
% 5.48/5.68                       ( k1_zfmisc_1 @
% 5.48/5.68                         ( k2_zfmisc_1 @
% 5.48/5.68                           ( u1_struct_0 @
% 5.48/5.68                             ( g1_pre_topc @
% 5.48/5.68                               ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 5.48/5.68                           ( u1_struct_0 @ B ) ) ) ) ) =>
% 5.48/5.68                   ( ( ( C ) = ( D ) ) =>
% 5.48/5.68                     ( ( v5_pre_topc @ C @ A @ B ) <=>
% 5.48/5.68                       ( v5_pre_topc @
% 5.48/5.68                         D @ 
% 5.48/5.68                         ( g1_pre_topc @
% 5.48/5.68                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ 
% 5.48/5.68                         B ) ) ) ) ) ) ) ) ) ))).
% 5.48/5.68  thf(zf_stmt_0, negated_conjecture,
% 5.48/5.68    (~( ![A:$i]:
% 5.48/5.68        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.48/5.68          ( ![B:$i]:
% 5.48/5.68            ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 5.48/5.68              ( ![C:$i]:
% 5.48/5.68                ( ( ( v1_funct_1 @ C ) & 
% 5.48/5.68                    ( v1_funct_2 @
% 5.48/5.68                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 5.48/5.68                    ( m1_subset_1 @
% 5.48/5.68                      C @ 
% 5.48/5.68                      ( k1_zfmisc_1 @
% 5.48/5.68                        ( k2_zfmisc_1 @
% 5.48/5.68                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 5.48/5.68                  ( ![D:$i]:
% 5.48/5.68                    ( ( ( v1_funct_1 @ D ) & 
% 5.48/5.68                        ( v1_funct_2 @
% 5.48/5.68                          D @ 
% 5.48/5.68                          ( u1_struct_0 @
% 5.48/5.68                            ( g1_pre_topc @
% 5.48/5.68                              ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 5.48/5.68                          ( u1_struct_0 @ B ) ) & 
% 5.48/5.68                        ( m1_subset_1 @
% 5.48/5.68                          D @ 
% 5.48/5.68                          ( k1_zfmisc_1 @
% 5.48/5.68                            ( k2_zfmisc_1 @
% 5.48/5.68                              ( u1_struct_0 @
% 5.48/5.68                                ( g1_pre_topc @
% 5.48/5.68                                  ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 5.48/5.68                              ( u1_struct_0 @ B ) ) ) ) ) =>
% 5.48/5.68                      ( ( ( C ) = ( D ) ) =>
% 5.48/5.68                        ( ( v5_pre_topc @ C @ A @ B ) <=>
% 5.48/5.68                          ( v5_pre_topc @
% 5.48/5.68                            D @ 
% 5.48/5.68                            ( g1_pre_topc @
% 5.48/5.68                              ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ 
% 5.48/5.68                            B ) ) ) ) ) ) ) ) ) ) )),
% 5.48/5.68    inference('cnf.neg', [status(esa)], [t62_pre_topc])).
% 5.48/5.68  thf('4', plain,
% 5.48/5.68      ((m1_subset_1 @ sk_D_1 @ 
% 5.48/5.68        (k1_zfmisc_1 @ 
% 5.48/5.68         (k2_zfmisc_1 @ 
% 5.48/5.68          (u1_struct_0 @ 
% 5.48/5.68           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 5.48/5.68          (u1_struct_0 @ sk_B_2))))),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('5', plain, (((sk_C_1) = (sk_D_1))),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('6', plain,
% 5.48/5.68      ((m1_subset_1 @ sk_C_1 @ 
% 5.48/5.68        (k1_zfmisc_1 @ 
% 5.48/5.68         (k2_zfmisc_1 @ 
% 5.48/5.68          (u1_struct_0 @ 
% 5.48/5.68           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 5.48/5.68          (u1_struct_0 @ sk_B_2))))),
% 5.48/5.68      inference('demod', [status(thm)], ['4', '5'])).
% 5.48/5.68  thf(d12_pre_topc, axiom,
% 5.48/5.68    (![A:$i]:
% 5.48/5.68     ( ( l1_pre_topc @ A ) =>
% 5.48/5.68       ( ![B:$i]:
% 5.48/5.68         ( ( l1_pre_topc @ B ) =>
% 5.48/5.68           ( ![C:$i]:
% 5.48/5.68             ( ( ( v1_funct_1 @ C ) & 
% 5.48/5.68                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 5.48/5.68                 ( m1_subset_1 @
% 5.48/5.68                   C @ 
% 5.48/5.68                   ( k1_zfmisc_1 @
% 5.48/5.68                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 5.48/5.68               ( ( v5_pre_topc @ C @ A @ B ) <=>
% 5.48/5.68                 ( ![D:$i]:
% 5.48/5.68                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 5.48/5.68                     ( ( v4_pre_topc @ D @ B ) =>
% 5.48/5.68                       ( v4_pre_topc @
% 5.48/5.68                         ( k8_relset_1 @
% 5.48/5.68                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 5.48/5.68                         A ) ) ) ) ) ) ) ) ) ))).
% 5.48/5.68  thf('7', plain,
% 5.48/5.68      (![X10 : $i, X11 : $i, X12 : $i]:
% 5.48/5.68         (~ (l1_pre_topc @ X10)
% 5.48/5.68          | (m1_subset_1 @ (sk_D @ X11 @ X10 @ X12) @ 
% 5.48/5.68             (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 5.48/5.68          | (v5_pre_topc @ X11 @ X12 @ X10)
% 5.48/5.68          | ~ (m1_subset_1 @ X11 @ 
% 5.48/5.68               (k1_zfmisc_1 @ 
% 5.48/5.68                (k2_zfmisc_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10))))
% 5.48/5.68          | ~ (v1_funct_2 @ X11 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10))
% 5.48/5.68          | ~ (v1_funct_1 @ X11)
% 5.48/5.68          | ~ (l1_pre_topc @ X12))),
% 5.48/5.68      inference('cnf', [status(esa)], [d12_pre_topc])).
% 5.48/5.68  thf('8', plain,
% 5.48/5.68      ((~ (l1_pre_topc @ 
% 5.48/5.68           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 5.48/5.68        | ~ (v1_funct_1 @ sk_C_1)
% 5.48/5.68        | ~ (v1_funct_2 @ sk_C_1 @ 
% 5.48/5.68             (u1_struct_0 @ 
% 5.48/5.68              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 5.48/5.68             (u1_struct_0 @ sk_B_2))
% 5.48/5.68        | (v5_pre_topc @ sk_C_1 @ 
% 5.48/5.68           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_2)
% 5.48/5.68        | (m1_subset_1 @ 
% 5.48/5.68           (sk_D @ sk_C_1 @ sk_B_2 @ 
% 5.48/5.68            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 5.48/5.68           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2)))
% 5.48/5.68        | ~ (l1_pre_topc @ sk_B_2))),
% 5.48/5.68      inference('sup-', [status(thm)], ['6', '7'])).
% 5.48/5.68  thf('9', plain, ((v1_funct_1 @ sk_C_1)),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('10', plain,
% 5.48/5.68      ((v1_funct_2 @ sk_D_1 @ 
% 5.48/5.68        (u1_struct_0 @ 
% 5.48/5.68         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 5.48/5.68        (u1_struct_0 @ sk_B_2))),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('11', plain, (((sk_C_1) = (sk_D_1))),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('12', plain,
% 5.48/5.68      ((v1_funct_2 @ sk_C_1 @ 
% 5.48/5.68        (u1_struct_0 @ 
% 5.48/5.68         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 5.48/5.68        (u1_struct_0 @ sk_B_2))),
% 5.48/5.68      inference('demod', [status(thm)], ['10', '11'])).
% 5.48/5.68  thf('13', plain, ((l1_pre_topc @ sk_B_2)),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('14', plain,
% 5.48/5.68      ((~ (l1_pre_topc @ 
% 5.48/5.68           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 5.48/5.68        | (v5_pre_topc @ sk_C_1 @ 
% 5.48/5.68           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_2)
% 5.48/5.68        | (m1_subset_1 @ 
% 5.48/5.68           (sk_D @ sk_C_1 @ sk_B_2 @ 
% 5.48/5.68            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 5.48/5.68           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2))))),
% 5.48/5.68      inference('demod', [status(thm)], ['8', '9', '12', '13'])).
% 5.48/5.68  thf('15', plain,
% 5.48/5.68      ((~ (l1_pre_topc @ sk_A)
% 5.48/5.68        | (m1_subset_1 @ 
% 5.48/5.68           (sk_D @ sk_C_1 @ sk_B_2 @ 
% 5.48/5.68            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 5.48/5.68           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2)))
% 5.48/5.68        | (v5_pre_topc @ sk_C_1 @ 
% 5.48/5.68           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_2))),
% 5.48/5.68      inference('sup-', [status(thm)], ['3', '14'])).
% 5.48/5.68  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('17', plain,
% 5.48/5.68      (((m1_subset_1 @ 
% 5.48/5.68         (sk_D @ sk_C_1 @ sk_B_2 @ 
% 5.48/5.68          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 5.48/5.68         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2)))
% 5.48/5.68        | (v5_pre_topc @ sk_C_1 @ 
% 5.48/5.68           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_2))),
% 5.48/5.68      inference('demod', [status(thm)], ['15', '16'])).
% 5.48/5.68  thf('18', plain,
% 5.48/5.68      ((~ (v5_pre_topc @ sk_D_1 @ 
% 5.48/5.68           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_2)
% 5.48/5.68        | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2))),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('19', plain,
% 5.48/5.68      ((~ (v5_pre_topc @ sk_D_1 @ 
% 5.48/5.68           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_2))
% 5.48/5.68         <= (~
% 5.48/5.68             ((v5_pre_topc @ sk_D_1 @ 
% 5.48/5.68               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 5.48/5.68               sk_B_2)))),
% 5.48/5.68      inference('split', [status(esa)], ['18'])).
% 5.48/5.68  thf('20', plain, (((sk_C_1) = (sk_D_1))),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('21', plain,
% 5.48/5.68      ((~ (v5_pre_topc @ sk_C_1 @ 
% 5.48/5.68           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_2))
% 5.48/5.68         <= (~
% 5.48/5.68             ((v5_pre_topc @ sk_D_1 @ 
% 5.48/5.68               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 5.48/5.68               sk_B_2)))),
% 5.48/5.68      inference('demod', [status(thm)], ['19', '20'])).
% 5.48/5.68  thf('22', plain,
% 5.48/5.68      (((v5_pre_topc @ sk_D_1 @ 
% 5.48/5.68         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_2)
% 5.48/5.68        | (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2))),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('23', plain, (((sk_C_1) = (sk_D_1))),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('24', plain,
% 5.48/5.68      (((v5_pre_topc @ sk_C_1 @ 
% 5.48/5.68         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_2)
% 5.48/5.68        | (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2))),
% 5.48/5.68      inference('demod', [status(thm)], ['22', '23'])).
% 5.48/5.68  thf('25', plain,
% 5.48/5.68      (((v5_pre_topc @ sk_C_1 @ 
% 5.48/5.68         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_2))
% 5.48/5.68         <= (((v5_pre_topc @ sk_C_1 @ 
% 5.48/5.68               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 5.48/5.68               sk_B_2)))),
% 5.48/5.68      inference('split', [status(esa)], ['24'])).
% 5.48/5.68  thf('26', plain,
% 5.48/5.68      ((~ (v5_pre_topc @ sk_C_1 @ 
% 5.48/5.68           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_2))
% 5.48/5.68         <= (~
% 5.48/5.68             ((v5_pre_topc @ sk_D_1 @ 
% 5.48/5.68               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 5.48/5.68               sk_B_2)))),
% 5.48/5.68      inference('demod', [status(thm)], ['19', '20'])).
% 5.48/5.68  thf('27', plain,
% 5.48/5.68      (~
% 5.48/5.68       ((v5_pre_topc @ sk_C_1 @ 
% 5.48/5.68         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_2)) | 
% 5.48/5.68       ((v5_pre_topc @ sk_D_1 @ 
% 5.48/5.68         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_2))),
% 5.48/5.68      inference('sup-', [status(thm)], ['25', '26'])).
% 5.48/5.68  thf('28', plain,
% 5.48/5.68      ((~ (v5_pre_topc @ sk_D_1 @ 
% 5.48/5.68           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_2)
% 5.48/5.68        | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2))),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('29', plain, (((sk_C_1) = (sk_D_1))),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('30', plain,
% 5.48/5.68      ((~ (v5_pre_topc @ sk_C_1 @ 
% 5.48/5.68           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_2)
% 5.48/5.68        | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2))),
% 5.48/5.68      inference('demod', [status(thm)], ['28', '29'])).
% 5.48/5.68  thf('31', plain,
% 5.48/5.68      (~
% 5.48/5.68       ((v5_pre_topc @ sk_C_1 @ 
% 5.48/5.68         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_2)) | 
% 5.48/5.68       ~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2))),
% 5.48/5.68      inference('split', [status(esa)], ['30'])).
% 5.48/5.68  thf('32', plain,
% 5.48/5.68      ((m1_subset_1 @ sk_C_1 @ 
% 5.48/5.68        (k1_zfmisc_1 @ 
% 5.48/5.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('33', plain,
% 5.48/5.68      (![X10 : $i, X11 : $i, X12 : $i]:
% 5.48/5.68         (~ (l1_pre_topc @ X10)
% 5.48/5.68          | (m1_subset_1 @ (sk_D @ X11 @ X10 @ X12) @ 
% 5.48/5.68             (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 5.48/5.68          | (v5_pre_topc @ X11 @ X12 @ X10)
% 5.48/5.68          | ~ (m1_subset_1 @ X11 @ 
% 5.48/5.68               (k1_zfmisc_1 @ 
% 5.48/5.68                (k2_zfmisc_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10))))
% 5.48/5.68          | ~ (v1_funct_2 @ X11 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10))
% 5.48/5.68          | ~ (v1_funct_1 @ X11)
% 5.48/5.68          | ~ (l1_pre_topc @ X12))),
% 5.48/5.68      inference('cnf', [status(esa)], [d12_pre_topc])).
% 5.48/5.68  thf('34', plain,
% 5.48/5.68      ((~ (l1_pre_topc @ sk_A)
% 5.48/5.68        | ~ (v1_funct_1 @ sk_C_1)
% 5.48/5.68        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 5.48/5.68             (u1_struct_0 @ sk_B_2))
% 5.48/5.68        | (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2)
% 5.48/5.68        | (m1_subset_1 @ (sk_D @ sk_C_1 @ sk_B_2 @ sk_A) @ 
% 5.48/5.68           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2)))
% 5.48/5.68        | ~ (l1_pre_topc @ sk_B_2))),
% 5.48/5.68      inference('sup-', [status(thm)], ['32', '33'])).
% 5.48/5.68  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('36', plain, ((v1_funct_1 @ sk_C_1)),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('37', plain,
% 5.48/5.68      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('38', plain, ((l1_pre_topc @ sk_B_2)),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('39', plain,
% 5.48/5.68      (((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2)
% 5.48/5.68        | (m1_subset_1 @ (sk_D @ sk_C_1 @ sk_B_2 @ sk_A) @ 
% 5.48/5.68           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2))))),
% 5.48/5.68      inference('demod', [status(thm)], ['34', '35', '36', '37', '38'])).
% 5.48/5.68  thf('40', plain,
% 5.48/5.68      (![X0 : $i]:
% 5.48/5.68         (~ (l1_pre_topc @ X0)
% 5.48/5.68          | (l1_pre_topc @ 
% 5.48/5.68             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 5.48/5.68      inference('sup-', [status(thm)], ['0', '1'])).
% 5.48/5.68  thf('41', plain,
% 5.48/5.68      (((v5_pre_topc @ sk_D_1 @ 
% 5.48/5.68         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_2)
% 5.48/5.68        | (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2))),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('42', plain,
% 5.48/5.68      (((v5_pre_topc @ sk_D_1 @ 
% 5.48/5.68         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_2))
% 5.48/5.68         <= (((v5_pre_topc @ sk_D_1 @ 
% 5.48/5.68               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 5.48/5.68               sk_B_2)))),
% 5.48/5.68      inference('split', [status(esa)], ['41'])).
% 5.48/5.68  thf('43', plain, (((sk_C_1) = (sk_D_1))),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('44', plain,
% 5.48/5.68      (((v5_pre_topc @ sk_C_1 @ 
% 5.48/5.68         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_2))
% 5.48/5.68         <= (((v5_pre_topc @ sk_D_1 @ 
% 5.48/5.68               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 5.48/5.68               sk_B_2)))),
% 5.48/5.68      inference('demod', [status(thm)], ['42', '43'])).
% 5.48/5.68  thf('45', plain,
% 5.48/5.68      ((m1_subset_1 @ sk_C_1 @ 
% 5.48/5.68        (k1_zfmisc_1 @ 
% 5.48/5.68         (k2_zfmisc_1 @ 
% 5.48/5.68          (u1_struct_0 @ 
% 5.48/5.68           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 5.48/5.68          (u1_struct_0 @ sk_B_2))))),
% 5.48/5.68      inference('demod', [status(thm)], ['4', '5'])).
% 5.48/5.68  thf('46', plain,
% 5.48/5.68      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 5.48/5.68         (~ (l1_pre_topc @ X10)
% 5.48/5.68          | ~ (v5_pre_topc @ X11 @ X12 @ X10)
% 5.48/5.68          | ~ (v4_pre_topc @ X13 @ X10)
% 5.48/5.68          | (v4_pre_topc @ 
% 5.48/5.68             (k8_relset_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10) @ X11 @ 
% 5.48/5.68              X13) @ 
% 5.48/5.68             X12)
% 5.48/5.68          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 5.48/5.68          | ~ (m1_subset_1 @ X11 @ 
% 5.48/5.68               (k1_zfmisc_1 @ 
% 5.48/5.68                (k2_zfmisc_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10))))
% 5.48/5.68          | ~ (v1_funct_2 @ X11 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10))
% 5.48/5.68          | ~ (v1_funct_1 @ X11)
% 5.48/5.68          | ~ (l1_pre_topc @ X12))),
% 5.48/5.68      inference('cnf', [status(esa)], [d12_pre_topc])).
% 5.48/5.68  thf('47', plain,
% 5.48/5.68      (![X0 : $i]:
% 5.48/5.68         (~ (l1_pre_topc @ 
% 5.48/5.68             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 5.48/5.68          | ~ (v1_funct_1 @ sk_C_1)
% 5.48/5.68          | ~ (v1_funct_2 @ sk_C_1 @ 
% 5.48/5.68               (u1_struct_0 @ 
% 5.48/5.68                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 5.48/5.68               (u1_struct_0 @ sk_B_2))
% 5.48/5.68          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2)))
% 5.48/5.68          | (v4_pre_topc @ 
% 5.48/5.68             (k8_relset_1 @ 
% 5.48/5.68              (u1_struct_0 @ 
% 5.48/5.68               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 5.48/5.68              (u1_struct_0 @ sk_B_2) @ sk_C_1 @ X0) @ 
% 5.48/5.68             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 5.48/5.68          | ~ (v4_pre_topc @ X0 @ sk_B_2)
% 5.48/5.68          | ~ (v5_pre_topc @ sk_C_1 @ 
% 5.48/5.68               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 5.48/5.68               sk_B_2)
% 5.48/5.68          | ~ (l1_pre_topc @ sk_B_2))),
% 5.48/5.68      inference('sup-', [status(thm)], ['45', '46'])).
% 5.48/5.68  thf('48', plain, ((v1_funct_1 @ sk_C_1)),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('49', plain,
% 5.48/5.68      ((v1_funct_2 @ sk_C_1 @ 
% 5.48/5.68        (u1_struct_0 @ 
% 5.48/5.68         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 5.48/5.68        (u1_struct_0 @ sk_B_2))),
% 5.48/5.68      inference('demod', [status(thm)], ['10', '11'])).
% 5.48/5.68  thf('50', plain, ((l1_pre_topc @ sk_B_2)),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('51', plain,
% 5.48/5.68      (![X0 : $i]:
% 5.48/5.68         (~ (l1_pre_topc @ 
% 5.48/5.68             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 5.48/5.68          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2)))
% 5.48/5.68          | (v4_pre_topc @ 
% 5.48/5.68             (k8_relset_1 @ 
% 5.48/5.68              (u1_struct_0 @ 
% 5.48/5.68               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 5.48/5.68              (u1_struct_0 @ sk_B_2) @ sk_C_1 @ X0) @ 
% 5.48/5.68             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 5.48/5.68          | ~ (v4_pre_topc @ X0 @ sk_B_2)
% 5.48/5.68          | ~ (v5_pre_topc @ sk_C_1 @ 
% 5.48/5.68               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 5.48/5.68               sk_B_2))),
% 5.48/5.68      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 5.48/5.68  thf(fc6_pre_topc, axiom,
% 5.48/5.68    (![A:$i]:
% 5.48/5.68     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.48/5.68       ( ( v1_pre_topc @
% 5.48/5.68           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 5.48/5.68         ( v2_pre_topc @
% 5.48/5.68           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 5.48/5.68  thf('52', plain,
% 5.48/5.68      (![X44 : $i]:
% 5.48/5.68         ((v2_pre_topc @ 
% 5.48/5.68           (g1_pre_topc @ (u1_struct_0 @ X44) @ (u1_pre_topc @ X44)))
% 5.48/5.68          | ~ (l1_pre_topc @ X44)
% 5.48/5.68          | ~ (v2_pre_topc @ X44))),
% 5.48/5.68      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 5.48/5.68  thf('53', plain,
% 5.48/5.68      (![X0 : $i]:
% 5.48/5.68         (~ (l1_pre_topc @ X0)
% 5.48/5.68          | (l1_pre_topc @ 
% 5.48/5.68             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 5.48/5.68      inference('sup-', [status(thm)], ['0', '1'])).
% 5.48/5.68  thf(d1_pre_topc, axiom,
% 5.48/5.68    (![A:$i]:
% 5.48/5.68     ( ( l1_pre_topc @ A ) =>
% 5.48/5.68       ( ( v2_pre_topc @ A ) <=>
% 5.48/5.68         ( ( ![B:$i]:
% 5.48/5.68             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.48/5.68               ( ![C:$i]:
% 5.48/5.68                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.48/5.68                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 5.48/5.68                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 5.48/5.68                     ( r2_hidden @
% 5.48/5.68                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 5.48/5.68                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 5.48/5.68           ( ![B:$i]:
% 5.48/5.68             ( ( m1_subset_1 @
% 5.48/5.68                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 5.48/5.68               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 5.48/5.68                 ( r2_hidden @
% 5.48/5.68                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 5.48/5.68                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 5.48/5.68           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 5.48/5.68  thf(zf_stmt_1, type, zip_tseitin_5 : $i > $i > $o).
% 5.48/5.68  thf(zf_stmt_2, axiom,
% 5.48/5.68    (![B:$i,A:$i]:
% 5.48/5.68     ( ( zip_tseitin_5 @ B @ A ) <=>
% 5.48/5.68       ( ( m1_subset_1 @
% 5.48/5.68           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 5.48/5.68         ( zip_tseitin_4 @ B @ A ) ) ))).
% 5.48/5.68  thf(zf_stmt_3, type, zip_tseitin_4 : $i > $i > $o).
% 5.48/5.68  thf(zf_stmt_4, axiom,
% 5.48/5.68    (![B:$i,A:$i]:
% 5.48/5.68     ( ( zip_tseitin_4 @ B @ A ) <=>
% 5.48/5.68       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 5.48/5.68         ( r2_hidden @
% 5.48/5.68           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 5.48/5.68  thf(zf_stmt_5, type, zip_tseitin_3 : $i > $i > $o).
% 5.48/5.68  thf(zf_stmt_6, axiom,
% 5.48/5.68    (![B:$i,A:$i]:
% 5.48/5.68     ( ( zip_tseitin_3 @ B @ A ) <=>
% 5.48/5.68       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.48/5.68         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 5.48/5.68  thf(zf_stmt_7, type, zip_tseitin_2 : $i > $i > $i > $o).
% 5.48/5.68  thf(zf_stmt_8, axiom,
% 5.48/5.68    (![C:$i,B:$i,A:$i]:
% 5.48/5.68     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 5.48/5.68       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.48/5.68         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 5.48/5.68  thf(zf_stmt_9, type, zip_tseitin_1 : $i > $i > $i > $o).
% 5.48/5.68  thf(zf_stmt_10, axiom,
% 5.48/5.68    (![C:$i,B:$i,A:$i]:
% 5.48/5.68     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 5.48/5.68       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 5.48/5.68         ( r2_hidden @
% 5.48/5.68           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 5.48/5.68  thf(zf_stmt_11, type, zip_tseitin_0 : $i > $i > $i > $o).
% 5.48/5.68  thf(zf_stmt_12, axiom,
% 5.48/5.68    (![C:$i,B:$i,A:$i]:
% 5.48/5.68     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 5.48/5.68       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 5.48/5.68         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 5.48/5.68  thf(zf_stmt_13, axiom,
% 5.48/5.68    (![A:$i]:
% 5.48/5.68     ( ( l1_pre_topc @ A ) =>
% 5.48/5.68       ( ( v2_pre_topc @ A ) <=>
% 5.48/5.68         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 5.48/5.68           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 5.48/5.68           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 5.48/5.68  thf('54', plain,
% 5.48/5.68      (![X36 : $i]:
% 5.48/5.68         (~ (v2_pre_topc @ X36)
% 5.48/5.68          | (r2_hidden @ (u1_struct_0 @ X36) @ (u1_pre_topc @ X36))
% 5.48/5.68          | ~ (l1_pre_topc @ X36))),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_13])).
% 5.48/5.68  thf(d10_xboole_0, axiom,
% 5.48/5.68    (![A:$i,B:$i]:
% 5.48/5.68     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.48/5.68  thf('55', plain,
% 5.48/5.68      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 5.48/5.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.48/5.68  thf('56', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 5.48/5.68      inference('simplify', [status(thm)], ['55'])).
% 5.48/5.68  thf(t3_subset, axiom,
% 5.48/5.68    (![A:$i,B:$i]:
% 5.48/5.68     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 5.48/5.68  thf('57', plain,
% 5.48/5.68      (![X3 : $i, X5 : $i]:
% 5.48/5.68         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 5.48/5.68      inference('cnf', [status(esa)], [t3_subset])).
% 5.48/5.68  thf('58', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 5.48/5.68      inference('sup-', [status(thm)], ['56', '57'])).
% 5.48/5.68  thf(d5_pre_topc, axiom,
% 5.48/5.68    (![A:$i]:
% 5.48/5.68     ( ( l1_pre_topc @ A ) =>
% 5.48/5.68       ( ![B:$i]:
% 5.48/5.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.48/5.68           ( ( v3_pre_topc @ B @ A ) <=>
% 5.48/5.68             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 5.48/5.68  thf('59', plain,
% 5.48/5.68      (![X39 : $i, X40 : $i]:
% 5.48/5.68         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 5.48/5.68          | ~ (r2_hidden @ X39 @ (u1_pre_topc @ X40))
% 5.48/5.68          | (v3_pre_topc @ X39 @ X40)
% 5.48/5.68          | ~ (l1_pre_topc @ X40))),
% 5.48/5.68      inference('cnf', [status(esa)], [d5_pre_topc])).
% 5.48/5.68  thf('60', plain,
% 5.48/5.68      (![X0 : $i]:
% 5.48/5.68         (~ (l1_pre_topc @ X0)
% 5.48/5.68          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 5.48/5.68          | ~ (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))),
% 5.48/5.68      inference('sup-', [status(thm)], ['58', '59'])).
% 5.48/5.68  thf('61', plain,
% 5.48/5.68      (![X0 : $i]:
% 5.48/5.68         (~ (l1_pre_topc @ X0)
% 5.48/5.68          | ~ (v2_pre_topc @ X0)
% 5.48/5.68          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 5.48/5.68          | ~ (l1_pre_topc @ X0))),
% 5.48/5.68      inference('sup-', [status(thm)], ['54', '60'])).
% 5.48/5.68  thf('62', plain,
% 5.48/5.68      (![X0 : $i]:
% 5.48/5.68         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 5.48/5.68          | ~ (v2_pre_topc @ X0)
% 5.48/5.68          | ~ (l1_pre_topc @ X0))),
% 5.48/5.68      inference('simplify', [status(thm)], ['61'])).
% 5.48/5.68  thf('63', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 5.48/5.68      inference('sup-', [status(thm)], ['56', '57'])).
% 5.48/5.68  thf(t60_pre_topc, axiom,
% 5.48/5.68    (![A:$i]:
% 5.48/5.68     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.48/5.68       ( ![B:$i]:
% 5.48/5.68         ( ( ( v3_pre_topc @ B @ A ) & 
% 5.48/5.68             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) <=>
% 5.48/5.68           ( ( v3_pre_topc @
% 5.48/5.68               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 5.48/5.68             ( m1_subset_1 @
% 5.48/5.68               B @ 
% 5.48/5.68               ( k1_zfmisc_1 @
% 5.48/5.68                 ( u1_struct_0 @
% 5.48/5.68                   ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ))).
% 5.48/5.68  thf('64', plain,
% 5.48/5.68      (![X45 : $i, X46 : $i]:
% 5.48/5.68         (~ (v3_pre_topc @ X45 @ 
% 5.48/5.68             (g1_pre_topc @ (u1_struct_0 @ X46) @ (u1_pre_topc @ X46)))
% 5.48/5.68          | ~ (m1_subset_1 @ X45 @ 
% 5.48/5.68               (k1_zfmisc_1 @ 
% 5.48/5.68                (u1_struct_0 @ 
% 5.48/5.68                 (g1_pre_topc @ (u1_struct_0 @ X46) @ (u1_pre_topc @ X46)))))
% 5.48/5.68          | (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 5.48/5.68          | ~ (l1_pre_topc @ X46)
% 5.48/5.68          | ~ (v2_pre_topc @ X46))),
% 5.48/5.68      inference('cnf', [status(esa)], [t60_pre_topc])).
% 5.48/5.68  thf('65', plain,
% 5.48/5.68      (![X0 : $i]:
% 5.48/5.68         (~ (v2_pre_topc @ X0)
% 5.48/5.68          | ~ (l1_pre_topc @ X0)
% 5.48/5.68          | (m1_subset_1 @ 
% 5.48/5.68             (u1_struct_0 @ 
% 5.48/5.68              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 5.48/5.68             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 5.48/5.68          | ~ (v3_pre_topc @ 
% 5.48/5.68               (u1_struct_0 @ 
% 5.48/5.68                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 5.48/5.68               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 5.48/5.68      inference('sup-', [status(thm)], ['63', '64'])).
% 5.48/5.68  thf('66', plain,
% 5.48/5.68      (![X0 : $i]:
% 5.48/5.68         (~ (l1_pre_topc @ 
% 5.48/5.68             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 5.48/5.68          | ~ (v2_pre_topc @ 
% 5.48/5.68               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 5.48/5.68          | (m1_subset_1 @ 
% 5.48/5.68             (u1_struct_0 @ 
% 5.48/5.68              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 5.48/5.68             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 5.48/5.68          | ~ (l1_pre_topc @ X0)
% 5.48/5.68          | ~ (v2_pre_topc @ X0))),
% 5.48/5.68      inference('sup-', [status(thm)], ['62', '65'])).
% 5.48/5.68  thf('67', plain,
% 5.48/5.68      (![X0 : $i]:
% 5.48/5.68         (~ (l1_pre_topc @ X0)
% 5.48/5.68          | ~ (v2_pre_topc @ X0)
% 5.48/5.68          | ~ (l1_pre_topc @ X0)
% 5.48/5.68          | (m1_subset_1 @ 
% 5.48/5.68             (u1_struct_0 @ 
% 5.48/5.68              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 5.48/5.68             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 5.48/5.68          | ~ (v2_pre_topc @ 
% 5.48/5.68               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 5.48/5.68      inference('sup-', [status(thm)], ['53', '66'])).
% 5.48/5.68  thf('68', plain,
% 5.48/5.68      (![X0 : $i]:
% 5.48/5.68         (~ (v2_pre_topc @ 
% 5.48/5.68             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 5.48/5.68          | (m1_subset_1 @ 
% 5.48/5.68             (u1_struct_0 @ 
% 5.48/5.68              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 5.48/5.68             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 5.48/5.68          | ~ (v2_pre_topc @ X0)
% 5.48/5.68          | ~ (l1_pre_topc @ X0))),
% 5.48/5.68      inference('simplify', [status(thm)], ['67'])).
% 5.48/5.68  thf('69', plain,
% 5.48/5.68      (![X0 : $i]:
% 5.48/5.68         (~ (v2_pre_topc @ X0)
% 5.48/5.68          | ~ (l1_pre_topc @ X0)
% 5.48/5.68          | ~ (l1_pre_topc @ X0)
% 5.48/5.68          | ~ (v2_pre_topc @ X0)
% 5.48/5.68          | (m1_subset_1 @ 
% 5.48/5.68             (u1_struct_0 @ 
% 5.48/5.68              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 5.48/5.68             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 5.48/5.68      inference('sup-', [status(thm)], ['52', '68'])).
% 5.48/5.68  thf('70', plain,
% 5.48/5.68      (![X0 : $i]:
% 5.48/5.68         ((m1_subset_1 @ 
% 5.48/5.68           (u1_struct_0 @ 
% 5.48/5.68            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 5.48/5.68           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 5.48/5.68          | ~ (l1_pre_topc @ X0)
% 5.48/5.68          | ~ (v2_pre_topc @ X0))),
% 5.48/5.68      inference('simplify', [status(thm)], ['69'])).
% 5.48/5.68  thf('71', plain,
% 5.48/5.68      (![X3 : $i, X4 : $i]:
% 5.48/5.68         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 5.48/5.68      inference('cnf', [status(esa)], [t3_subset])).
% 5.48/5.68  thf('72', plain,
% 5.48/5.68      (![X0 : $i]:
% 5.48/5.68         (~ (v2_pre_topc @ X0)
% 5.48/5.68          | ~ (l1_pre_topc @ X0)
% 5.48/5.68          | (r1_tarski @ 
% 5.48/5.68             (u1_struct_0 @ 
% 5.48/5.68              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 5.48/5.68             (u1_struct_0 @ X0)))),
% 5.48/5.68      inference('sup-', [status(thm)], ['70', '71'])).
% 5.48/5.68  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('74', plain,
% 5.48/5.68      (![X36 : $i, X38 : $i]:
% 5.48/5.68         (~ (v2_pre_topc @ X36)
% 5.48/5.68          | (zip_tseitin_5 @ X38 @ X36)
% 5.48/5.68          | ~ (l1_pre_topc @ X36))),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_13])).
% 5.48/5.68  thf('75', plain,
% 5.48/5.68      (![X0 : $i]: ((zip_tseitin_5 @ X0 @ sk_A) | ~ (v2_pre_topc @ sk_A))),
% 5.48/5.68      inference('sup-', [status(thm)], ['73', '74'])).
% 5.48/5.68  thf('76', plain, ((v2_pre_topc @ sk_A)),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('77', plain, (![X0 : $i]: (zip_tseitin_5 @ X0 @ sk_A)),
% 5.48/5.68      inference('demod', [status(thm)], ['75', '76'])).
% 5.48/5.68  thf('78', plain,
% 5.48/5.68      (![X43 : $i]:
% 5.48/5.68         ((m1_subset_1 @ (u1_pre_topc @ X43) @ 
% 5.48/5.68           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43))))
% 5.48/5.68          | ~ (l1_pre_topc @ X43))),
% 5.48/5.68      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 5.48/5.68  thf('79', plain,
% 5.48/5.68      (![X33 : $i, X34 : $i]:
% 5.48/5.68         (~ (m1_subset_1 @ X33 @ 
% 5.48/5.68             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34))))
% 5.48/5.68          | (zip_tseitin_4 @ X33 @ X34)
% 5.48/5.68          | ~ (zip_tseitin_5 @ X33 @ X34))),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.48/5.68  thf('80', plain,
% 5.48/5.68      (![X0 : $i]:
% 5.48/5.68         (~ (l1_pre_topc @ X0)
% 5.48/5.68          | ~ (zip_tseitin_5 @ (u1_pre_topc @ X0) @ X0)
% 5.48/5.68          | (zip_tseitin_4 @ (u1_pre_topc @ X0) @ X0))),
% 5.48/5.68      inference('sup-', [status(thm)], ['78', '79'])).
% 5.48/5.68  thf('81', plain,
% 5.48/5.68      (((zip_tseitin_4 @ (u1_pre_topc @ sk_A) @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 5.48/5.68      inference('sup-', [status(thm)], ['77', '80'])).
% 5.48/5.68  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('83', plain, ((zip_tseitin_4 @ (u1_pre_topc @ sk_A) @ sk_A)),
% 5.48/5.68      inference('demod', [status(thm)], ['81', '82'])).
% 5.48/5.68  thf('84', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 5.48/5.68      inference('simplify', [status(thm)], ['55'])).
% 5.48/5.68  thf('85', plain,
% 5.48/5.68      (![X30 : $i, X31 : $i]:
% 5.48/5.68         (~ (r1_tarski @ X30 @ (u1_pre_topc @ X31))
% 5.48/5.68          | (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ X31) @ X30) @ 
% 5.48/5.68             (u1_pre_topc @ X31))
% 5.48/5.68          | ~ (zip_tseitin_4 @ X30 @ X31))),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_4])).
% 5.48/5.68  thf('86', plain,
% 5.48/5.68      (![X0 : $i]:
% 5.48/5.68         (~ (zip_tseitin_4 @ (u1_pre_topc @ X0) @ X0)
% 5.48/5.68          | (r2_hidden @ 
% 5.48/5.68             (k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ 
% 5.48/5.68             (u1_pre_topc @ X0)))),
% 5.48/5.68      inference('sup-', [status(thm)], ['84', '85'])).
% 5.48/5.68  thf('87', plain,
% 5.48/5.68      ((r2_hidden @ 
% 5.48/5.68        (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 5.48/5.68        (u1_pre_topc @ sk_A))),
% 5.48/5.68      inference('sup-', [status(thm)], ['83', '86'])).
% 5.48/5.68  thf('88', plain,
% 5.48/5.68      (![X36 : $i]:
% 5.48/5.68         (~ (v2_pre_topc @ X36)
% 5.48/5.68          | (r2_hidden @ (u1_struct_0 @ X36) @ (u1_pre_topc @ X36))
% 5.48/5.68          | ~ (l1_pre_topc @ X36))),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_13])).
% 5.48/5.68  thf('89', plain,
% 5.48/5.68      (![X14 : $i, X16 : $i, X17 : $i]:
% 5.48/5.68         ((zip_tseitin_0 @ X16 @ X14 @ X17)
% 5.48/5.68          | ~ (r2_hidden @ X16 @ (u1_pre_topc @ X17))
% 5.48/5.68          | ~ (r2_hidden @ X14 @ (u1_pre_topc @ X17)))),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_12])).
% 5.48/5.68  thf('90', plain,
% 5.48/5.68      (![X0 : $i, X1 : $i]:
% 5.48/5.68         (~ (l1_pre_topc @ X0)
% 5.48/5.68          | ~ (v2_pre_topc @ X0)
% 5.48/5.68          | ~ (r2_hidden @ X1 @ (u1_pre_topc @ X0))
% 5.48/5.68          | (zip_tseitin_0 @ (u1_struct_0 @ X0) @ X1 @ X0))),
% 5.48/5.68      inference('sup-', [status(thm)], ['88', '89'])).
% 5.48/5.68  thf('91', plain,
% 5.48/5.68      (((zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ 
% 5.48/5.68         (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_A)
% 5.48/5.68        | ~ (v2_pre_topc @ sk_A)
% 5.48/5.68        | ~ (l1_pre_topc @ sk_A))),
% 5.48/5.68      inference('sup-', [status(thm)], ['87', '90'])).
% 5.48/5.68  thf('92', plain, ((v2_pre_topc @ sk_A)),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('94', plain,
% 5.48/5.68      ((zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ 
% 5.48/5.68        (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_A)),
% 5.48/5.68      inference('demod', [status(thm)], ['91', '92', '93'])).
% 5.48/5.68  thf('95', plain,
% 5.48/5.68      (![X14 : $i, X15 : $i, X16 : $i]:
% 5.48/5.68         ((r2_hidden @ X16 @ (u1_pre_topc @ X15))
% 5.48/5.68          | ~ (zip_tseitin_0 @ X16 @ X14 @ X15))),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_12])).
% 5.48/5.68  thf('96', plain, ((r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))),
% 5.48/5.68      inference('sup-', [status(thm)], ['94', '95'])).
% 5.48/5.68  thf('97', plain,
% 5.48/5.68      (![X0 : $i]:
% 5.48/5.68         (~ (l1_pre_topc @ X0)
% 5.48/5.68          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 5.48/5.68          | ~ (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))),
% 5.48/5.68      inference('sup-', [status(thm)], ['58', '59'])).
% 5.48/5.68  thf('98', plain,
% 5.48/5.68      (((v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 5.48/5.68      inference('sup-', [status(thm)], ['96', '97'])).
% 5.48/5.68  thf('99', plain, ((l1_pre_topc @ sk_A)),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('100', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)),
% 5.48/5.68      inference('demod', [status(thm)], ['98', '99'])).
% 5.48/5.68  thf('101', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 5.48/5.68      inference('sup-', [status(thm)], ['56', '57'])).
% 5.48/5.68  thf('102', plain,
% 5.48/5.68      (![X46 : $i, X47 : $i]:
% 5.48/5.68         (~ (v3_pre_topc @ X47 @ X46)
% 5.48/5.68          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 5.48/5.68          | (m1_subset_1 @ X47 @ 
% 5.48/5.68             (k1_zfmisc_1 @ 
% 5.48/5.68              (u1_struct_0 @ 
% 5.48/5.68               (g1_pre_topc @ (u1_struct_0 @ X46) @ (u1_pre_topc @ X46)))))
% 5.48/5.68          | ~ (l1_pre_topc @ X46)
% 5.48/5.68          | ~ (v2_pre_topc @ X46))),
% 5.48/5.68      inference('cnf', [status(esa)], [t60_pre_topc])).
% 5.48/5.68  thf('103', plain,
% 5.48/5.68      (![X0 : $i]:
% 5.48/5.68         (~ (v2_pre_topc @ X0)
% 5.48/5.68          | ~ (l1_pre_topc @ X0)
% 5.48/5.68          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 5.48/5.68             (k1_zfmisc_1 @ 
% 5.48/5.68              (u1_struct_0 @ 
% 5.48/5.68               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 5.48/5.68          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 5.48/5.68      inference('sup-', [status(thm)], ['101', '102'])).
% 5.48/5.68  thf('104', plain,
% 5.48/5.68      (((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.48/5.68         (k1_zfmisc_1 @ 
% 5.48/5.68          (u1_struct_0 @ 
% 5.48/5.68           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 5.48/5.68        | ~ (l1_pre_topc @ sk_A)
% 5.48/5.68        | ~ (v2_pre_topc @ sk_A))),
% 5.48/5.68      inference('sup-', [status(thm)], ['100', '103'])).
% 5.48/5.68  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('106', plain, ((v2_pre_topc @ sk_A)),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('107', plain,
% 5.48/5.68      ((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.48/5.68        (k1_zfmisc_1 @ 
% 5.48/5.68         (u1_struct_0 @ 
% 5.48/5.68          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 5.48/5.68      inference('demod', [status(thm)], ['104', '105', '106'])).
% 5.48/5.68  thf('108', plain,
% 5.48/5.68      (![X3 : $i, X4 : $i]:
% 5.48/5.68         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 5.48/5.68      inference('cnf', [status(esa)], [t3_subset])).
% 5.48/5.68  thf('109', plain,
% 5.48/5.68      ((r1_tarski @ (u1_struct_0 @ sk_A) @ 
% 5.48/5.68        (u1_struct_0 @ 
% 5.48/5.68         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 5.48/5.68      inference('sup-', [status(thm)], ['107', '108'])).
% 5.48/5.68  thf('110', plain,
% 5.48/5.68      (![X0 : $i, X2 : $i]:
% 5.48/5.68         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 5.48/5.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.48/5.68  thf('111', plain,
% 5.48/5.68      ((~ (r1_tarski @ 
% 5.48/5.68           (u1_struct_0 @ 
% 5.48/5.68            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 5.48/5.68           (u1_struct_0 @ sk_A))
% 5.48/5.68        | ((u1_struct_0 @ 
% 5.48/5.68            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 5.48/5.68            = (u1_struct_0 @ sk_A)))),
% 5.48/5.68      inference('sup-', [status(thm)], ['109', '110'])).
% 5.48/5.68  thf('112', plain,
% 5.48/5.68      ((~ (l1_pre_topc @ sk_A)
% 5.48/5.68        | ~ (v2_pre_topc @ sk_A)
% 5.48/5.68        | ((u1_struct_0 @ 
% 5.48/5.68            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 5.48/5.68            = (u1_struct_0 @ sk_A)))),
% 5.48/5.68      inference('sup-', [status(thm)], ['72', '111'])).
% 5.48/5.68  thf('113', plain, ((l1_pre_topc @ sk_A)),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('114', plain, ((v2_pre_topc @ sk_A)),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('115', plain,
% 5.48/5.68      (((u1_struct_0 @ 
% 5.48/5.68         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 5.48/5.68         = (u1_struct_0 @ sk_A))),
% 5.48/5.68      inference('demod', [status(thm)], ['112', '113', '114'])).
% 5.48/5.68  thf('116', plain,
% 5.48/5.68      (![X0 : $i]:
% 5.48/5.68         (~ (l1_pre_topc @ 
% 5.48/5.68             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 5.48/5.68          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2)))
% 5.48/5.68          | (v4_pre_topc @ 
% 5.48/5.68             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 5.48/5.68              sk_C_1 @ X0) @ 
% 5.48/5.68             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 5.48/5.68          | ~ (v4_pre_topc @ X0 @ sk_B_2)
% 5.48/5.68          | ~ (v5_pre_topc @ sk_C_1 @ 
% 5.48/5.68               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 5.48/5.68               sk_B_2))),
% 5.48/5.68      inference('demod', [status(thm)], ['51', '115'])).
% 5.48/5.68  thf('117', plain,
% 5.48/5.68      ((![X0 : $i]:
% 5.48/5.68          (~ (v4_pre_topc @ X0 @ sk_B_2)
% 5.48/5.68           | (v4_pre_topc @ 
% 5.48/5.68              (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 5.48/5.68               sk_C_1 @ X0) @ 
% 5.48/5.68              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 5.48/5.68           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2)))
% 5.48/5.68           | ~ (l1_pre_topc @ 
% 5.48/5.68                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 5.48/5.68         <= (((v5_pre_topc @ sk_D_1 @ 
% 5.48/5.68               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 5.48/5.68               sk_B_2)))),
% 5.48/5.68      inference('sup-', [status(thm)], ['44', '116'])).
% 5.48/5.68  thf('118', plain,
% 5.48/5.68      ((![X0 : $i]:
% 5.48/5.68          (~ (l1_pre_topc @ sk_A)
% 5.48/5.68           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2)))
% 5.48/5.68           | (v4_pre_topc @ 
% 5.48/5.68              (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 5.48/5.68               sk_C_1 @ X0) @ 
% 5.48/5.68              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 5.48/5.68           | ~ (v4_pre_topc @ X0 @ sk_B_2)))
% 5.48/5.68         <= (((v5_pre_topc @ sk_D_1 @ 
% 5.48/5.68               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 5.48/5.68               sk_B_2)))),
% 5.48/5.68      inference('sup-', [status(thm)], ['40', '117'])).
% 5.48/5.68  thf('119', plain, ((l1_pre_topc @ sk_A)),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('120', plain,
% 5.48/5.68      ((![X0 : $i]:
% 5.48/5.68          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2)))
% 5.48/5.68           | (v4_pre_topc @ 
% 5.48/5.68              (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 5.48/5.68               sk_C_1 @ X0) @ 
% 5.48/5.68              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 5.48/5.68           | ~ (v4_pre_topc @ X0 @ sk_B_2)))
% 5.48/5.68         <= (((v5_pre_topc @ sk_D_1 @ 
% 5.48/5.68               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 5.48/5.68               sk_B_2)))),
% 5.48/5.68      inference('demod', [status(thm)], ['118', '119'])).
% 5.48/5.68  thf('121', plain,
% 5.48/5.68      ((((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2)
% 5.48/5.68         | ~ (v4_pre_topc @ (sk_D @ sk_C_1 @ sk_B_2 @ sk_A) @ sk_B_2)
% 5.48/5.68         | (v4_pre_topc @ 
% 5.48/5.68            (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 5.48/5.68             sk_C_1 @ (sk_D @ sk_C_1 @ sk_B_2 @ sk_A)) @ 
% 5.48/5.68            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 5.48/5.68         <= (((v5_pre_topc @ sk_D_1 @ 
% 5.48/5.68               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 5.48/5.68               sk_B_2)))),
% 5.48/5.68      inference('sup-', [status(thm)], ['39', '120'])).
% 5.48/5.68  thf('122', plain,
% 5.48/5.68      ((m1_subset_1 @ sk_C_1 @ 
% 5.48/5.68        (k1_zfmisc_1 @ 
% 5.48/5.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('123', plain,
% 5.48/5.68      (![X10 : $i, X11 : $i, X12 : $i]:
% 5.48/5.68         (~ (l1_pre_topc @ X10)
% 5.48/5.68          | (v4_pre_topc @ (sk_D @ X11 @ X10 @ X12) @ X10)
% 5.48/5.68          | (v5_pre_topc @ X11 @ X12 @ X10)
% 5.48/5.68          | ~ (m1_subset_1 @ X11 @ 
% 5.48/5.68               (k1_zfmisc_1 @ 
% 5.48/5.68                (k2_zfmisc_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10))))
% 5.48/5.68          | ~ (v1_funct_2 @ X11 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10))
% 5.48/5.68          | ~ (v1_funct_1 @ X11)
% 5.48/5.68          | ~ (l1_pre_topc @ X12))),
% 5.48/5.68      inference('cnf', [status(esa)], [d12_pre_topc])).
% 5.48/5.68  thf('124', plain,
% 5.48/5.68      ((~ (l1_pre_topc @ sk_A)
% 5.48/5.68        | ~ (v1_funct_1 @ sk_C_1)
% 5.48/5.68        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 5.48/5.68             (u1_struct_0 @ sk_B_2))
% 5.48/5.68        | (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2)
% 5.48/5.68        | (v4_pre_topc @ (sk_D @ sk_C_1 @ sk_B_2 @ sk_A) @ sk_B_2)
% 5.48/5.68        | ~ (l1_pre_topc @ sk_B_2))),
% 5.48/5.68      inference('sup-', [status(thm)], ['122', '123'])).
% 5.48/5.68  thf('125', plain, ((l1_pre_topc @ sk_A)),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('126', plain, ((v1_funct_1 @ sk_C_1)),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('127', plain,
% 5.48/5.68      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('128', plain, ((l1_pre_topc @ sk_B_2)),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('129', plain,
% 5.48/5.68      (((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2)
% 5.48/5.68        | (v4_pre_topc @ (sk_D @ sk_C_1 @ sk_B_2 @ sk_A) @ sk_B_2))),
% 5.48/5.68      inference('demod', [status(thm)], ['124', '125', '126', '127', '128'])).
% 5.48/5.68  thf('130', plain,
% 5.48/5.68      ((((v4_pre_topc @ 
% 5.48/5.68          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 5.48/5.68           sk_C_1 @ (sk_D @ sk_C_1 @ sk_B_2 @ sk_A)) @ 
% 5.48/5.68          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 5.48/5.68         | (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2)))
% 5.48/5.68         <= (((v5_pre_topc @ sk_D_1 @ 
% 5.48/5.68               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 5.48/5.68               sk_B_2)))),
% 5.48/5.68      inference('clc', [status(thm)], ['121', '129'])).
% 5.48/5.68  thf('131', plain,
% 5.48/5.68      (![X0 : $i]:
% 5.48/5.68         (~ (v2_pre_topc @ X0)
% 5.48/5.68          | ~ (l1_pre_topc @ X0)
% 5.48/5.68          | (r1_tarski @ 
% 5.48/5.68             (u1_struct_0 @ 
% 5.48/5.68              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 5.48/5.68             (u1_struct_0 @ X0)))),
% 5.48/5.68      inference('sup-', [status(thm)], ['70', '71'])).
% 5.48/5.68  thf('132', plain,
% 5.48/5.68      (![X0 : $i]:
% 5.48/5.68         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 5.48/5.68          | ~ (v2_pre_topc @ X0)
% 5.48/5.68          | ~ (l1_pre_topc @ X0))),
% 5.48/5.68      inference('simplify', [status(thm)], ['61'])).
% 5.48/5.68  thf('133', plain,
% 5.48/5.68      (![X0 : $i]:
% 5.48/5.68         (~ (v2_pre_topc @ X0)
% 5.48/5.68          | ~ (l1_pre_topc @ X0)
% 5.48/5.68          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 5.48/5.68             (k1_zfmisc_1 @ 
% 5.48/5.68              (u1_struct_0 @ 
% 5.48/5.68               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 5.48/5.68          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 5.48/5.68      inference('sup-', [status(thm)], ['101', '102'])).
% 5.48/5.68  thf('134', plain,
% 5.48/5.68      (![X0 : $i]:
% 5.48/5.68         (~ (l1_pre_topc @ X0)
% 5.48/5.68          | ~ (v2_pre_topc @ X0)
% 5.48/5.68          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 5.48/5.68             (k1_zfmisc_1 @ 
% 5.48/5.68              (u1_struct_0 @ 
% 5.48/5.68               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 5.48/5.68          | ~ (l1_pre_topc @ X0)
% 5.48/5.68          | ~ (v2_pre_topc @ X0))),
% 5.48/5.68      inference('sup-', [status(thm)], ['132', '133'])).
% 5.48/5.68  thf('135', plain,
% 5.48/5.68      (![X0 : $i]:
% 5.48/5.68         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 5.48/5.68           (k1_zfmisc_1 @ 
% 5.48/5.68            (u1_struct_0 @ 
% 5.48/5.68             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 5.48/5.68          | ~ (v2_pre_topc @ X0)
% 5.48/5.68          | ~ (l1_pre_topc @ X0))),
% 5.48/5.68      inference('simplify', [status(thm)], ['134'])).
% 5.48/5.68  thf('136', plain,
% 5.48/5.68      (![X3 : $i, X4 : $i]:
% 5.48/5.68         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 5.48/5.68      inference('cnf', [status(esa)], [t3_subset])).
% 5.48/5.68  thf('137', plain,
% 5.48/5.68      (![X0 : $i]:
% 5.48/5.68         (~ (l1_pre_topc @ X0)
% 5.48/5.68          | ~ (v2_pre_topc @ X0)
% 5.48/5.68          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 5.48/5.68             (u1_struct_0 @ 
% 5.48/5.68              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))),
% 5.48/5.68      inference('sup-', [status(thm)], ['135', '136'])).
% 5.48/5.68  thf('138', plain,
% 5.48/5.68      (![X0 : $i, X2 : $i]:
% 5.48/5.68         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 5.48/5.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.48/5.68  thf('139', plain,
% 5.48/5.68      (![X0 : $i]:
% 5.48/5.68         (~ (v2_pre_topc @ X0)
% 5.48/5.68          | ~ (l1_pre_topc @ X0)
% 5.48/5.68          | ~ (r1_tarski @ 
% 5.48/5.68               (u1_struct_0 @ 
% 5.48/5.68                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 5.48/5.68               (u1_struct_0 @ X0))
% 5.48/5.68          | ((u1_struct_0 @ 
% 5.48/5.68              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 5.48/5.68              = (u1_struct_0 @ X0)))),
% 5.48/5.68      inference('sup-', [status(thm)], ['137', '138'])).
% 5.48/5.68  thf('140', plain,
% 5.48/5.68      (![X0 : $i]:
% 5.48/5.68         (~ (l1_pre_topc @ X0)
% 5.48/5.68          | ~ (v2_pre_topc @ X0)
% 5.48/5.68          | ((u1_struct_0 @ 
% 5.48/5.68              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 5.48/5.68              = (u1_struct_0 @ X0))
% 5.48/5.68          | ~ (l1_pre_topc @ X0)
% 5.48/5.68          | ~ (v2_pre_topc @ X0))),
% 5.48/5.68      inference('sup-', [status(thm)], ['131', '139'])).
% 5.48/5.68  thf('141', plain,
% 5.48/5.68      (![X0 : $i]:
% 5.48/5.68         (((u1_struct_0 @ 
% 5.48/5.68            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 5.48/5.68            = (u1_struct_0 @ X0))
% 5.48/5.68          | ~ (v2_pre_topc @ X0)
% 5.48/5.68          | ~ (l1_pre_topc @ X0))),
% 5.48/5.68      inference('simplify', [status(thm)], ['140'])).
% 5.48/5.68  thf(t61_pre_topc, axiom,
% 5.48/5.68    (![A:$i]:
% 5.48/5.68     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.48/5.68       ( ![B:$i]:
% 5.48/5.68         ( ( ( v4_pre_topc @ B @ A ) & 
% 5.48/5.68             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) <=>
% 5.48/5.68           ( ( v4_pre_topc @
% 5.48/5.68               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 5.48/5.68             ( m1_subset_1 @
% 5.48/5.68               B @ 
% 5.48/5.68               ( k1_zfmisc_1 @
% 5.48/5.68                 ( u1_struct_0 @
% 5.48/5.68                   ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ))).
% 5.48/5.68  thf('142', plain,
% 5.48/5.68      (![X48 : $i, X49 : $i]:
% 5.48/5.68         (~ (v4_pre_topc @ X48 @ 
% 5.48/5.68             (g1_pre_topc @ (u1_struct_0 @ X49) @ (u1_pre_topc @ X49)))
% 5.48/5.68          | ~ (m1_subset_1 @ X48 @ 
% 5.48/5.68               (k1_zfmisc_1 @ 
% 5.48/5.68                (u1_struct_0 @ 
% 5.48/5.68                 (g1_pre_topc @ (u1_struct_0 @ X49) @ (u1_pre_topc @ X49)))))
% 5.48/5.68          | (v4_pre_topc @ X48 @ X49)
% 5.48/5.68          | ~ (l1_pre_topc @ X49)
% 5.48/5.68          | ~ (v2_pre_topc @ X49))),
% 5.48/5.68      inference('cnf', [status(esa)], [t61_pre_topc])).
% 5.48/5.68  thf('143', plain,
% 5.48/5.68      (![X0 : $i, X1 : $i]:
% 5.48/5.68         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 5.48/5.68          | ~ (l1_pre_topc @ X0)
% 5.48/5.68          | ~ (v2_pre_topc @ X0)
% 5.48/5.68          | ~ (v2_pre_topc @ X0)
% 5.48/5.68          | ~ (l1_pre_topc @ X0)
% 5.48/5.68          | (v4_pre_topc @ X1 @ X0)
% 5.48/5.68          | ~ (v4_pre_topc @ X1 @ 
% 5.48/5.68               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 5.48/5.68      inference('sup-', [status(thm)], ['141', '142'])).
% 5.48/5.68  thf('144', plain,
% 5.48/5.68      (![X0 : $i, X1 : $i]:
% 5.48/5.68         (~ (v4_pre_topc @ X1 @ 
% 5.48/5.68             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 5.48/5.68          | (v4_pre_topc @ X1 @ X0)
% 5.48/5.68          | ~ (v2_pre_topc @ X0)
% 5.48/5.68          | ~ (l1_pre_topc @ X0)
% 5.48/5.68          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 5.48/5.68      inference('simplify', [status(thm)], ['143'])).
% 5.48/5.68  thf('145', plain,
% 5.48/5.68      ((((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2)
% 5.48/5.68         | ~ (m1_subset_1 @ 
% 5.48/5.68              (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 5.48/5.68               sk_C_1 @ (sk_D @ sk_C_1 @ sk_B_2 @ sk_A)) @ 
% 5.48/5.68              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.48/5.68         | ~ (l1_pre_topc @ sk_A)
% 5.48/5.68         | ~ (v2_pre_topc @ sk_A)
% 5.48/5.68         | (v4_pre_topc @ 
% 5.48/5.68            (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 5.48/5.68             sk_C_1 @ (sk_D @ sk_C_1 @ sk_B_2 @ sk_A)) @ 
% 5.48/5.68            sk_A)))
% 5.48/5.68         <= (((v5_pre_topc @ sk_D_1 @ 
% 5.48/5.68               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 5.48/5.68               sk_B_2)))),
% 5.48/5.68      inference('sup-', [status(thm)], ['130', '144'])).
% 5.48/5.68  thf('146', plain,
% 5.48/5.68      ((m1_subset_1 @ sk_C_1 @ 
% 5.48/5.68        (k1_zfmisc_1 @ 
% 5.48/5.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf(dt_k8_relset_1, axiom,
% 5.48/5.68    (![A:$i,B:$i,C:$i,D:$i]:
% 5.48/5.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.48/5.68       ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 5.48/5.68  thf('147', plain,
% 5.48/5.68      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 5.48/5.68         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 5.48/5.68          | (m1_subset_1 @ (k8_relset_1 @ X7 @ X8 @ X6 @ X9) @ 
% 5.48/5.68             (k1_zfmisc_1 @ X7)))),
% 5.48/5.68      inference('cnf', [status(esa)], [dt_k8_relset_1])).
% 5.48/5.68  thf('148', plain,
% 5.48/5.68      (![X0 : $i]:
% 5.48/5.68         (m1_subset_1 @ 
% 5.48/5.68          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 5.48/5.68           sk_C_1 @ X0) @ 
% 5.48/5.68          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.48/5.68      inference('sup-', [status(thm)], ['146', '147'])).
% 5.48/5.68  thf('149', plain, ((l1_pre_topc @ sk_A)),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('150', plain, ((v2_pre_topc @ sk_A)),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('151', plain,
% 5.48/5.68      ((((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2)
% 5.48/5.68         | (v4_pre_topc @ 
% 5.48/5.68            (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 5.48/5.68             sk_C_1 @ (sk_D @ sk_C_1 @ sk_B_2 @ sk_A)) @ 
% 5.48/5.68            sk_A)))
% 5.48/5.68         <= (((v5_pre_topc @ sk_D_1 @ 
% 5.48/5.68               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 5.48/5.68               sk_B_2)))),
% 5.48/5.68      inference('demod', [status(thm)], ['145', '148', '149', '150'])).
% 5.48/5.68  thf('152', plain,
% 5.48/5.68      (![X10 : $i, X11 : $i, X12 : $i]:
% 5.48/5.68         (~ (l1_pre_topc @ X10)
% 5.48/5.68          | ~ (v4_pre_topc @ 
% 5.48/5.68               (k8_relset_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10) @ 
% 5.48/5.68                X11 @ (sk_D @ X11 @ X10 @ X12)) @ 
% 5.48/5.68               X12)
% 5.48/5.68          | (v5_pre_topc @ X11 @ X12 @ X10)
% 5.48/5.68          | ~ (m1_subset_1 @ X11 @ 
% 5.48/5.68               (k1_zfmisc_1 @ 
% 5.48/5.68                (k2_zfmisc_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10))))
% 5.48/5.68          | ~ (v1_funct_2 @ X11 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10))
% 5.48/5.68          | ~ (v1_funct_1 @ X11)
% 5.48/5.68          | ~ (l1_pre_topc @ X12))),
% 5.48/5.68      inference('cnf', [status(esa)], [d12_pre_topc])).
% 5.48/5.68  thf('153', plain,
% 5.48/5.68      ((((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2)
% 5.48/5.68         | ~ (l1_pre_topc @ sk_A)
% 5.48/5.68         | ~ (v1_funct_1 @ sk_C_1)
% 5.48/5.68         | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 5.48/5.68              (u1_struct_0 @ sk_B_2))
% 5.48/5.68         | ~ (m1_subset_1 @ sk_C_1 @ 
% 5.48/5.68              (k1_zfmisc_1 @ 
% 5.48/5.68               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))
% 5.48/5.68         | (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2)
% 5.48/5.68         | ~ (l1_pre_topc @ sk_B_2)))
% 5.48/5.68         <= (((v5_pre_topc @ sk_D_1 @ 
% 5.48/5.68               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 5.48/5.68               sk_B_2)))),
% 5.48/5.68      inference('sup-', [status(thm)], ['151', '152'])).
% 5.48/5.68  thf('154', plain, ((l1_pre_topc @ sk_A)),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('155', plain, ((v1_funct_1 @ sk_C_1)),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('156', plain,
% 5.48/5.68      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('157', plain,
% 5.48/5.68      ((m1_subset_1 @ sk_C_1 @ 
% 5.48/5.68        (k1_zfmisc_1 @ 
% 5.48/5.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('158', plain, ((l1_pre_topc @ sk_B_2)),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('159', plain,
% 5.48/5.68      ((((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2)
% 5.48/5.68         | (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2)))
% 5.48/5.68         <= (((v5_pre_topc @ sk_D_1 @ 
% 5.48/5.68               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 5.48/5.68               sk_B_2)))),
% 5.48/5.68      inference('demod', [status(thm)],
% 5.48/5.68                ['153', '154', '155', '156', '157', '158'])).
% 5.48/5.68  thf('160', plain,
% 5.48/5.68      (((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2))
% 5.48/5.68         <= (((v5_pre_topc @ sk_D_1 @ 
% 5.48/5.68               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 5.48/5.68               sk_B_2)))),
% 5.48/5.68      inference('simplify', [status(thm)], ['159'])).
% 5.48/5.68  thf('161', plain,
% 5.48/5.68      ((~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2))
% 5.48/5.68         <= (~ ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2)))),
% 5.48/5.68      inference('split', [status(esa)], ['18'])).
% 5.48/5.68  thf('162', plain,
% 5.48/5.68      (~
% 5.48/5.68       ((v5_pre_topc @ sk_D_1 @ 
% 5.48/5.68         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_2)) | 
% 5.48/5.68       ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2))),
% 5.48/5.68      inference('sup-', [status(thm)], ['160', '161'])).
% 5.48/5.68  thf('163', plain,
% 5.48/5.68      (((v5_pre_topc @ sk_C_1 @ 
% 5.48/5.68         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_2))
% 5.48/5.68         <= (((v5_pre_topc @ sk_D_1 @ 
% 5.48/5.68               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 5.48/5.68               sk_B_2)))),
% 5.48/5.68      inference('demod', [status(thm)], ['42', '43'])).
% 5.48/5.68  thf('164', plain,
% 5.48/5.68      ((~ (v5_pre_topc @ sk_C_1 @ 
% 5.48/5.68           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_2))
% 5.48/5.68         <= (~
% 5.48/5.68             ((v5_pre_topc @ sk_C_1 @ 
% 5.48/5.68               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 5.48/5.68               sk_B_2)))),
% 5.48/5.68      inference('split', [status(esa)], ['30'])).
% 5.48/5.68  thf('165', plain,
% 5.48/5.68      (~
% 5.48/5.68       ((v5_pre_topc @ sk_D_1 @ 
% 5.48/5.68         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_2)) | 
% 5.48/5.68       ((v5_pre_topc @ sk_C_1 @ 
% 5.48/5.68         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_2))),
% 5.48/5.68      inference('sup-', [status(thm)], ['163', '164'])).
% 5.48/5.68  thf('166', plain,
% 5.48/5.68      (~
% 5.48/5.68       ((v5_pre_topc @ sk_D_1 @ 
% 5.48/5.68         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_2))),
% 5.48/5.68      inference('sat_resolution*', [status(thm)], ['27', '31', '162', '165'])).
% 5.48/5.68  thf('167', plain,
% 5.48/5.68      (~ (v5_pre_topc @ sk_C_1 @ 
% 5.48/5.68          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_2)),
% 5.48/5.68      inference('simpl_trail', [status(thm)], ['21', '166'])).
% 5.48/5.68  thf('168', plain,
% 5.48/5.68      ((m1_subset_1 @ 
% 5.48/5.68        (sk_D @ sk_C_1 @ sk_B_2 @ 
% 5.48/5.68         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 5.48/5.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2)))),
% 5.48/5.68      inference('clc', [status(thm)], ['17', '167'])).
% 5.48/5.68  thf('169', plain,
% 5.48/5.68      (((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2))
% 5.48/5.68         <= (((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2)))),
% 5.48/5.68      inference('split', [status(esa)], ['41'])).
% 5.48/5.68  thf('170', plain,
% 5.48/5.68      ((m1_subset_1 @ sk_C_1 @ 
% 5.48/5.68        (k1_zfmisc_1 @ 
% 5.48/5.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('171', plain,
% 5.48/5.68      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 5.48/5.68         (~ (l1_pre_topc @ X10)
% 5.48/5.68          | ~ (v5_pre_topc @ X11 @ X12 @ X10)
% 5.48/5.68          | ~ (v4_pre_topc @ X13 @ X10)
% 5.48/5.68          | (v4_pre_topc @ 
% 5.48/5.68             (k8_relset_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10) @ X11 @ 
% 5.48/5.68              X13) @ 
% 5.48/5.68             X12)
% 5.48/5.68          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 5.48/5.68          | ~ (m1_subset_1 @ X11 @ 
% 5.48/5.68               (k1_zfmisc_1 @ 
% 5.48/5.68                (k2_zfmisc_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10))))
% 5.48/5.68          | ~ (v1_funct_2 @ X11 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10))
% 5.48/5.68          | ~ (v1_funct_1 @ X11)
% 5.48/5.68          | ~ (l1_pre_topc @ X12))),
% 5.48/5.68      inference('cnf', [status(esa)], [d12_pre_topc])).
% 5.48/5.68  thf('172', plain,
% 5.48/5.68      (![X0 : $i]:
% 5.48/5.68         (~ (l1_pre_topc @ sk_A)
% 5.48/5.68          | ~ (v1_funct_1 @ sk_C_1)
% 5.48/5.68          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 5.48/5.68               (u1_struct_0 @ sk_B_2))
% 5.48/5.68          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2)))
% 5.48/5.68          | (v4_pre_topc @ 
% 5.48/5.68             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 5.48/5.68              sk_C_1 @ X0) @ 
% 5.48/5.68             sk_A)
% 5.48/5.68          | ~ (v4_pre_topc @ X0 @ sk_B_2)
% 5.48/5.68          | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2)
% 5.48/5.68          | ~ (l1_pre_topc @ sk_B_2))),
% 5.48/5.68      inference('sup-', [status(thm)], ['170', '171'])).
% 5.48/5.68  thf('173', plain, ((l1_pre_topc @ sk_A)),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('174', plain, ((v1_funct_1 @ sk_C_1)),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('175', plain,
% 5.48/5.68      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('176', plain, ((l1_pre_topc @ sk_B_2)),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('177', plain,
% 5.48/5.68      (![X0 : $i]:
% 5.48/5.68         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2)))
% 5.48/5.68          | (v4_pre_topc @ 
% 5.48/5.68             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 5.48/5.68              sk_C_1 @ X0) @ 
% 5.48/5.68             sk_A)
% 5.48/5.68          | ~ (v4_pre_topc @ X0 @ sk_B_2)
% 5.48/5.68          | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2))),
% 5.48/5.68      inference('demod', [status(thm)], ['172', '173', '174', '175', '176'])).
% 5.48/5.68  thf('178', plain,
% 5.48/5.68      ((![X0 : $i]:
% 5.48/5.68          (~ (v4_pre_topc @ X0 @ sk_B_2)
% 5.48/5.68           | (v4_pre_topc @ 
% 5.48/5.68              (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 5.48/5.68               sk_C_1 @ X0) @ 
% 5.48/5.68              sk_A)
% 5.48/5.68           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2)))))
% 5.48/5.68         <= (((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2)))),
% 5.48/5.68      inference('sup-', [status(thm)], ['169', '177'])).
% 5.48/5.68  thf('179', plain,
% 5.48/5.68      (((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2)) | 
% 5.48/5.68       ((v5_pre_topc @ sk_C_1 @ 
% 5.48/5.68         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_2))),
% 5.48/5.68      inference('split', [status(esa)], ['24'])).
% 5.48/5.68  thf('180', plain, (((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2))),
% 5.48/5.68      inference('sat_resolution*', [status(thm)], ['27', '31', '162', '179'])).
% 5.48/5.68  thf('181', plain,
% 5.48/5.68      (![X0 : $i]:
% 5.48/5.68         (~ (v4_pre_topc @ X0 @ sk_B_2)
% 5.48/5.68          | (v4_pre_topc @ 
% 5.48/5.68             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 5.48/5.68              sk_C_1 @ X0) @ 
% 5.48/5.68             sk_A)
% 5.48/5.68          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2))))),
% 5.48/5.68      inference('simpl_trail', [status(thm)], ['178', '180'])).
% 5.48/5.68  thf('182', plain,
% 5.48/5.68      (((v4_pre_topc @ 
% 5.48/5.68         (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 5.48/5.68          sk_C_1 @ 
% 5.48/5.68          (sk_D @ sk_C_1 @ sk_B_2 @ 
% 5.48/5.68           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) @ 
% 5.48/5.68         sk_A)
% 5.48/5.68        | ~ (v4_pre_topc @ 
% 5.48/5.68             (sk_D @ sk_C_1 @ sk_B_2 @ 
% 5.48/5.68              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 5.48/5.68             sk_B_2))),
% 5.48/5.68      inference('sup-', [status(thm)], ['168', '181'])).
% 5.48/5.68  thf('183', plain,
% 5.48/5.68      (![X0 : $i]:
% 5.48/5.68         (~ (l1_pre_topc @ X0)
% 5.48/5.68          | (l1_pre_topc @ 
% 5.48/5.68             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 5.48/5.68      inference('sup-', [status(thm)], ['0', '1'])).
% 5.48/5.68  thf('184', plain,
% 5.48/5.68      ((m1_subset_1 @ sk_C_1 @ 
% 5.48/5.68        (k1_zfmisc_1 @ 
% 5.48/5.68         (k2_zfmisc_1 @ 
% 5.48/5.68          (u1_struct_0 @ 
% 5.48/5.68           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 5.48/5.68          (u1_struct_0 @ sk_B_2))))),
% 5.48/5.68      inference('demod', [status(thm)], ['4', '5'])).
% 5.48/5.68  thf('185', plain,
% 5.48/5.68      (![X10 : $i, X11 : $i, X12 : $i]:
% 5.48/5.68         (~ (l1_pre_topc @ X10)
% 5.48/5.68          | (v4_pre_topc @ (sk_D @ X11 @ X10 @ X12) @ X10)
% 5.48/5.68          | (v5_pre_topc @ X11 @ X12 @ X10)
% 5.48/5.68          | ~ (m1_subset_1 @ X11 @ 
% 5.48/5.68               (k1_zfmisc_1 @ 
% 5.48/5.68                (k2_zfmisc_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10))))
% 5.48/5.68          | ~ (v1_funct_2 @ X11 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10))
% 5.48/5.68          | ~ (v1_funct_1 @ X11)
% 5.48/5.68          | ~ (l1_pre_topc @ X12))),
% 5.48/5.68      inference('cnf', [status(esa)], [d12_pre_topc])).
% 5.48/5.68  thf('186', plain,
% 5.48/5.68      ((~ (l1_pre_topc @ 
% 5.48/5.68           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 5.48/5.68        | ~ (v1_funct_1 @ sk_C_1)
% 5.48/5.68        | ~ (v1_funct_2 @ sk_C_1 @ 
% 5.48/5.68             (u1_struct_0 @ 
% 5.48/5.68              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 5.48/5.68             (u1_struct_0 @ sk_B_2))
% 5.48/5.68        | (v5_pre_topc @ sk_C_1 @ 
% 5.48/5.68           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_2)
% 5.48/5.68        | (v4_pre_topc @ 
% 5.48/5.68           (sk_D @ sk_C_1 @ sk_B_2 @ 
% 5.48/5.68            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 5.48/5.68           sk_B_2)
% 5.48/5.68        | ~ (l1_pre_topc @ sk_B_2))),
% 5.48/5.68      inference('sup-', [status(thm)], ['184', '185'])).
% 5.48/5.68  thf('187', plain, ((v1_funct_1 @ sk_C_1)),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('188', plain,
% 5.48/5.68      ((v1_funct_2 @ sk_C_1 @ 
% 5.48/5.68        (u1_struct_0 @ 
% 5.48/5.68         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 5.48/5.68        (u1_struct_0 @ sk_B_2))),
% 5.48/5.68      inference('demod', [status(thm)], ['10', '11'])).
% 5.48/5.68  thf('189', plain, ((l1_pre_topc @ sk_B_2)),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('190', plain,
% 5.48/5.68      ((~ (l1_pre_topc @ 
% 5.48/5.68           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 5.48/5.68        | (v5_pre_topc @ sk_C_1 @ 
% 5.48/5.68           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_2)
% 5.48/5.68        | (v4_pre_topc @ 
% 5.48/5.68           (sk_D @ sk_C_1 @ sk_B_2 @ 
% 5.48/5.68            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 5.48/5.68           sk_B_2))),
% 5.48/5.68      inference('demod', [status(thm)], ['186', '187', '188', '189'])).
% 5.48/5.68  thf('191', plain,
% 5.48/5.68      ((~ (l1_pre_topc @ sk_A)
% 5.48/5.68        | (v4_pre_topc @ 
% 5.48/5.68           (sk_D @ sk_C_1 @ sk_B_2 @ 
% 5.48/5.68            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 5.48/5.68           sk_B_2)
% 5.48/5.68        | (v5_pre_topc @ sk_C_1 @ 
% 5.48/5.68           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_2))),
% 5.48/5.68      inference('sup-', [status(thm)], ['183', '190'])).
% 5.48/5.68  thf('192', plain, ((l1_pre_topc @ sk_A)),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('193', plain,
% 5.48/5.68      (((v4_pre_topc @ 
% 5.48/5.68         (sk_D @ sk_C_1 @ sk_B_2 @ 
% 5.48/5.68          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 5.48/5.68         sk_B_2)
% 5.48/5.68        | (v5_pre_topc @ sk_C_1 @ 
% 5.48/5.68           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_2))),
% 5.48/5.68      inference('demod', [status(thm)], ['191', '192'])).
% 5.48/5.68  thf('194', plain,
% 5.48/5.68      (~ (v5_pre_topc @ sk_C_1 @ 
% 5.48/5.68          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_2)),
% 5.48/5.68      inference('simpl_trail', [status(thm)], ['21', '166'])).
% 5.48/5.68  thf('195', plain,
% 5.48/5.68      ((v4_pre_topc @ 
% 5.48/5.68        (sk_D @ sk_C_1 @ sk_B_2 @ 
% 5.48/5.68         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 5.48/5.68        sk_B_2)),
% 5.48/5.68      inference('clc', [status(thm)], ['193', '194'])).
% 5.48/5.68  thf('196', plain,
% 5.48/5.68      ((v4_pre_topc @ 
% 5.48/5.68        (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 5.48/5.68         sk_C_1 @ 
% 5.48/5.68         (sk_D @ sk_C_1 @ sk_B_2 @ 
% 5.48/5.68          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) @ 
% 5.48/5.68        sk_A)),
% 5.48/5.68      inference('demod', [status(thm)], ['182', '195'])).
% 5.48/5.68  thf('197', plain,
% 5.48/5.68      (![X0 : $i]:
% 5.48/5.68         (m1_subset_1 @ 
% 5.48/5.68          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 5.48/5.68           sk_C_1 @ X0) @ 
% 5.48/5.68          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.48/5.68      inference('sup-', [status(thm)], ['146', '147'])).
% 5.48/5.68  thf('198', plain,
% 5.48/5.68      (![X49 : $i, X50 : $i]:
% 5.48/5.68         (~ (v4_pre_topc @ X50 @ X49)
% 5.48/5.68          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 5.48/5.68          | (v4_pre_topc @ X50 @ 
% 5.48/5.68             (g1_pre_topc @ (u1_struct_0 @ X49) @ (u1_pre_topc @ X49)))
% 5.48/5.68          | ~ (l1_pre_topc @ X49)
% 5.48/5.68          | ~ (v2_pre_topc @ X49))),
% 5.48/5.68      inference('cnf', [status(esa)], [t61_pre_topc])).
% 5.48/5.68  thf('199', plain,
% 5.48/5.68      (![X0 : $i]:
% 5.48/5.68         (~ (v2_pre_topc @ sk_A)
% 5.48/5.68          | ~ (l1_pre_topc @ sk_A)
% 5.48/5.68          | (v4_pre_topc @ 
% 5.48/5.68             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 5.48/5.68              sk_C_1 @ X0) @ 
% 5.48/5.68             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 5.48/5.68          | ~ (v4_pre_topc @ 
% 5.48/5.68               (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 5.48/5.68                sk_C_1 @ X0) @ 
% 5.48/5.68               sk_A))),
% 5.48/5.68      inference('sup-', [status(thm)], ['197', '198'])).
% 5.48/5.68  thf('200', plain, ((v2_pre_topc @ sk_A)),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('201', plain, ((l1_pre_topc @ sk_A)),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('202', plain,
% 5.48/5.68      (![X0 : $i]:
% 5.48/5.68         ((v4_pre_topc @ 
% 5.48/5.68           (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 5.48/5.68            sk_C_1 @ X0) @ 
% 5.48/5.68           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 5.48/5.68          | ~ (v4_pre_topc @ 
% 5.48/5.68               (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 5.48/5.68                sk_C_1 @ X0) @ 
% 5.48/5.68               sk_A))),
% 5.48/5.68      inference('demod', [status(thm)], ['199', '200', '201'])).
% 5.48/5.68  thf('203', plain,
% 5.48/5.68      ((v4_pre_topc @ 
% 5.48/5.68        (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 5.48/5.68         sk_C_1 @ 
% 5.48/5.68         (sk_D @ sk_C_1 @ sk_B_2 @ 
% 5.48/5.68          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) @ 
% 5.48/5.68        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 5.48/5.68      inference('sup-', [status(thm)], ['196', '202'])).
% 5.48/5.68  thf('204', plain,
% 5.48/5.68      (![X0 : $i]:
% 5.48/5.68         (((u1_struct_0 @ 
% 5.48/5.68            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 5.48/5.68            = (u1_struct_0 @ X0))
% 5.48/5.68          | ~ (v2_pre_topc @ X0)
% 5.48/5.68          | ~ (l1_pre_topc @ X0))),
% 5.48/5.68      inference('simplify', [status(thm)], ['140'])).
% 5.48/5.68  thf('205', plain,
% 5.48/5.68      (![X10 : $i, X11 : $i, X12 : $i]:
% 5.48/5.68         (~ (l1_pre_topc @ X10)
% 5.48/5.68          | ~ (v4_pre_topc @ 
% 5.48/5.68               (k8_relset_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10) @ 
% 5.48/5.68                X11 @ (sk_D @ X11 @ X10 @ X12)) @ 
% 5.48/5.68               X12)
% 5.48/5.68          | (v5_pre_topc @ X11 @ X12 @ X10)
% 5.48/5.68          | ~ (m1_subset_1 @ X11 @ 
% 5.48/5.68               (k1_zfmisc_1 @ 
% 5.48/5.68                (k2_zfmisc_1 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10))))
% 5.48/5.68          | ~ (v1_funct_2 @ X11 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X10))
% 5.48/5.68          | ~ (v1_funct_1 @ X11)
% 5.48/5.68          | ~ (l1_pre_topc @ X12))),
% 5.48/5.68      inference('cnf', [status(esa)], [d12_pre_topc])).
% 5.48/5.68  thf('206', plain,
% 5.48/5.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.48/5.68         (~ (v4_pre_topc @ 
% 5.48/5.68             (k8_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1) @ X2 @ 
% 5.48/5.68              (sk_D @ X2 @ X1 @ 
% 5.48/5.68               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))) @ 
% 5.48/5.68             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 5.48/5.68          | ~ (l1_pre_topc @ X0)
% 5.48/5.68          | ~ (v2_pre_topc @ X0)
% 5.48/5.68          | ~ (l1_pre_topc @ 
% 5.48/5.68               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 5.48/5.68          | ~ (v1_funct_1 @ X2)
% 5.48/5.68          | ~ (v1_funct_2 @ X2 @ 
% 5.48/5.68               (u1_struct_0 @ 
% 5.48/5.68                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 5.48/5.68               (u1_struct_0 @ X1))
% 5.48/5.68          | ~ (m1_subset_1 @ X2 @ 
% 5.48/5.68               (k1_zfmisc_1 @ 
% 5.48/5.68                (k2_zfmisc_1 @ 
% 5.48/5.68                 (u1_struct_0 @ 
% 5.48/5.68                  (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 5.48/5.68                 (u1_struct_0 @ X1))))
% 5.48/5.68          | (v5_pre_topc @ X2 @ 
% 5.48/5.68             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)
% 5.48/5.68          | ~ (l1_pre_topc @ X1))),
% 5.48/5.68      inference('sup-', [status(thm)], ['204', '205'])).
% 5.48/5.68  thf('207', plain,
% 5.48/5.68      ((~ (l1_pre_topc @ sk_B_2)
% 5.48/5.68        | (v5_pre_topc @ sk_C_1 @ 
% 5.48/5.68           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_2)
% 5.48/5.68        | ~ (m1_subset_1 @ sk_C_1 @ 
% 5.48/5.68             (k1_zfmisc_1 @ 
% 5.48/5.68              (k2_zfmisc_1 @ 
% 5.48/5.68               (u1_struct_0 @ 
% 5.48/5.68                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 5.48/5.68               (u1_struct_0 @ sk_B_2))))
% 5.48/5.68        | ~ (v1_funct_2 @ sk_C_1 @ 
% 5.48/5.68             (u1_struct_0 @ 
% 5.48/5.68              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 5.48/5.68             (u1_struct_0 @ sk_B_2))
% 5.48/5.68        | ~ (v1_funct_1 @ sk_C_1)
% 5.48/5.68        | ~ (l1_pre_topc @ 
% 5.48/5.68             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 5.48/5.68        | ~ (v2_pre_topc @ sk_A)
% 5.48/5.68        | ~ (l1_pre_topc @ sk_A))),
% 5.48/5.68      inference('sup-', [status(thm)], ['203', '206'])).
% 5.48/5.68  thf('208', plain, ((l1_pre_topc @ sk_B_2)),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('209', plain,
% 5.48/5.68      (((u1_struct_0 @ 
% 5.48/5.68         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 5.48/5.68         = (u1_struct_0 @ sk_A))),
% 5.48/5.68      inference('demod', [status(thm)], ['112', '113', '114'])).
% 5.48/5.68  thf('210', plain,
% 5.48/5.68      ((m1_subset_1 @ sk_C_1 @ 
% 5.48/5.68        (k1_zfmisc_1 @ 
% 5.48/5.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('211', plain,
% 5.48/5.68      (((u1_struct_0 @ 
% 5.48/5.68         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 5.48/5.68         = (u1_struct_0 @ sk_A))),
% 5.48/5.68      inference('demod', [status(thm)], ['112', '113', '114'])).
% 5.48/5.68  thf('212', plain,
% 5.48/5.68      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('213', plain, ((v1_funct_1 @ sk_C_1)),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('214', plain, ((v2_pre_topc @ sk_A)),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('215', plain, ((l1_pre_topc @ sk_A)),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('216', plain,
% 5.48/5.68      (((v5_pre_topc @ sk_C_1 @ 
% 5.48/5.68         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_2)
% 5.48/5.68        | ~ (l1_pre_topc @ 
% 5.48/5.68             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 5.48/5.68      inference('demod', [status(thm)],
% 5.48/5.68                ['207', '208', '209', '210', '211', '212', '213', '214', '215'])).
% 5.48/5.68  thf('217', plain,
% 5.48/5.68      (~ (v5_pre_topc @ sk_C_1 @ 
% 5.48/5.68          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_2)),
% 5.48/5.68      inference('simpl_trail', [status(thm)], ['21', '166'])).
% 5.48/5.68  thf('218', plain,
% 5.48/5.68      (~ (l1_pre_topc @ 
% 5.48/5.68          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 5.48/5.68      inference('clc', [status(thm)], ['216', '217'])).
% 5.48/5.68  thf('219', plain, (~ (l1_pre_topc @ sk_A)),
% 5.48/5.68      inference('sup-', [status(thm)], ['2', '218'])).
% 5.48/5.68  thf('220', plain, ((l1_pre_topc @ sk_A)),
% 5.48/5.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.48/5.68  thf('221', plain, ($false), inference('demod', [status(thm)], ['219', '220'])).
% 5.48/5.68  
% 5.48/5.68  % SZS output end Refutation
% 5.48/5.68  
% 5.48/5.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
