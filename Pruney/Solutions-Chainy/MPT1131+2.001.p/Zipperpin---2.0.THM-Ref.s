%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pdfCkZnWQH

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:26 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  190 (1034 expanded)
%              Number of leaves         :   27 ( 302 expanded)
%              Depth                    :   29
%              Number of atoms          : 2603 (33699 expanded)
%              Number of equality atoms :   24 ( 523 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X11: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X11 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(dt_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) )
        & ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) ) ) ),
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
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ( v4_pre_topc @ ( sk_D @ X6 @ X5 @ X7 ) @ X5 )
      | ( v5_pre_topc @ X6 @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('8',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['8','9','12','13'])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('20',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ( m1_subset_1 @ ( sk_D @ X6 @ X5 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( v5_pre_topc @ X6 @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('21',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('24',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['21','22','23','24'])).

thf('26',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( v5_pre_topc @ X6 @ X7 @ X5 )
      | ~ ( v4_pre_topc @ X8 @ X5 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) @ X6 @ X8 ) @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_B )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_B )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34','35','36','37'])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ~ ( v4_pre_topc @ X0 @ sk_B )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['30','38'])).

thf('40',plain,
    ( ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
   <= ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(split,[status(esa)],['42'])).

thf('44',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
   <= ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(split,[status(esa)],['44'])).

thf('46',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
   <= ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['43','47'])).

thf('49',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['51'])).

thf('53',plain,(
    ! [X11: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X11 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('54',plain,(
    ! [X9: $i,X10: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('56',plain,(
    ! [X4: $i] :
      ( ~ ( v1_pre_topc @ X4 )
      | ( X4
        = ( g1_pre_topc @ ( u1_struct_0 @ X4 ) @ ( u1_pre_topc @ X4 ) ) )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('57',plain,(
    ! [X11: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X11 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('58',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( ( g1_pre_topc @ X14 @ X15 )
       != ( g1_pre_topc @ X12 @ X13 ) )
      | ( X14 = X12 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X2 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
        = X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['55','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ( m1_subset_1 @ ( sk_D @ X6 @ X5 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( v5_pre_topc @ X6 @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('67',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['67','68','69','70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('74',plain,
    ( ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(split,[status(esa)],['29'])).

thf('75',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('78',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( v5_pre_topc @ X6 @ X7 @ X5 )
      | ~ ( v4_pre_topc @ X8 @ X5 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) @ X6 @ X8 ) @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v4_pre_topc @ X0 @ sk_B )
      | ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('82',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v4_pre_topc @ X0 @ sk_B )
      | ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('84',plain,
    ( ! [X0: $i] :
        ( ~ ( v4_pre_topc @ X0 @ sk_B )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['76','83'])).

thf('85',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( v4_pre_topc @ X0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['73','84'])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
        | ~ ( v4_pre_topc @ X0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['72','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ( v4_pre_topc @ ( sk_D @ X6 @ X5 @ X7 ) @ X5 )
      | ( v5_pre_topc @ X6 @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('91',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['91','92','93','94','95'])).

thf('97',plain,
    ( ( ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(clc,[status(thm)],['88','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(dt_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ( m1_subset_1 @ ( k8_relset_1 @ X1 @ X2 @ X0 @ X3 ) @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relset_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf(t61_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v4_pre_topc @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
        <=> ( ( v4_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) )).

thf('101',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v4_pre_topc @ X16 @ ( g1_pre_topc @ ( u1_struct_0 @ X17 ) @ ( u1_pre_topc @ X17 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X17 ) @ ( u1_pre_topc @ X17 ) ) ) ) )
      | ( v4_pre_topc @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t61_pre_topc])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ sk_A ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['97','105'])).

thf('107',plain,
    ( ( ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference('sup+',[status(thm)],['64','106'])).

thf('108',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ sk_A )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) @ X6 @ ( sk_D @ X6 @ X5 @ X7 ) ) @ X7 )
      | ( v5_pre_topc @ X6 @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('111',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( l1_pre_topc @ sk_B ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['111','112','113','114','115','116'])).

thf('118',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['44'])).

thf('120',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(split,[status(esa)],['42'])).

thf('122',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['48','52','120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ X0 @ sk_B )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['39','122'])).

thf('124',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['28','123'])).

thf('125',plain,
    ( ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
   <= ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('126',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
   <= ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('127',plain,
    ( ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
   <= ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(split,[status(esa)],['51'])).

thf('128',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ~ ( v5_pre_topc @ sk_D_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['48','52','120','128'])).

thf('130',plain,(
    ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['125','129'])).

thf('131',plain,
    ( ~ ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_B )
    | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) @ sk_A ) ),
    inference(clc,[status(thm)],['124','130'])).

thf('132',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['17','131'])).

thf('133',plain,(
    ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['125','129'])).

thf('134',plain,(
    v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) @ sk_A ),
    inference(clc,[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('137',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup+',[status(thm)],['136','137'])).

thf('139',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v4_pre_topc @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v4_pre_topc @ X18 @ ( g1_pre_topc @ ( u1_struct_0 @ X17 ) @ ( u1_pre_topc @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t61_pre_topc])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['135','145'])).

thf('147',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_A )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,(
    v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['134','148'])).

thf('150',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) @ X6 @ ( sk_D @ X6 @ X5 @ X7 ) ) @ X7 )
      | ( v5_pre_topc @ X6 @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('151',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('154',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('155',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['151','152','153','154','155'])).

thf('157',plain,(
    ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['125','129'])).

thf('158',plain,(
    ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('159',plain,(
    ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['2','158'])).

thf('160',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    $false ),
    inference(demod,[status(thm)],['159','160'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pdfCkZnWQH
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:35:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.47/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.63  % Solved by: fo/fo7.sh
% 0.47/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.63  % done 210 iterations in 0.171s
% 0.47/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.63  % SZS output start Refutation
% 0.47/0.63  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.63  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.47/0.63  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.47/0.63  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.47/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.63  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.47/0.63  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.47/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.63  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.47/0.63  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.47/0.63  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.47/0.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.47/0.63  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.47/0.63  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.47/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.63  thf(dt_u1_pre_topc, axiom,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( l1_pre_topc @ A ) =>
% 0.47/0.63       ( m1_subset_1 @
% 0.47/0.63         ( u1_pre_topc @ A ) @ 
% 0.47/0.63         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.47/0.63  thf('0', plain,
% 0.47/0.63      (![X11 : $i]:
% 0.47/0.63         ((m1_subset_1 @ (u1_pre_topc @ X11) @ 
% 0.47/0.63           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))
% 0.47/0.63          | ~ (l1_pre_topc @ X11))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.47/0.63  thf(dt_g1_pre_topc, axiom,
% 0.47/0.63    (![A:$i,B:$i]:
% 0.47/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.47/0.63       ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) ) & 
% 0.47/0.63         ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ))).
% 0.47/0.63  thf('1', plain,
% 0.47/0.63      (![X9 : $i, X10 : $i]:
% 0.47/0.63         ((l1_pre_topc @ (g1_pre_topc @ X9 @ X10))
% 0.47/0.63          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X9))))),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 0.47/0.63  thf('2', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (l1_pre_topc @ X0)
% 0.47/0.63          | (l1_pre_topc @ 
% 0.47/0.63             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['0', '1'])).
% 0.47/0.63  thf('3', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (l1_pre_topc @ X0)
% 0.47/0.63          | (l1_pre_topc @ 
% 0.47/0.63             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['0', '1'])).
% 0.47/0.63  thf(t62_pre_topc, conjecture,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.63       ( ![B:$i]:
% 0.47/0.63         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.47/0.63           ( ![C:$i]:
% 0.47/0.63             ( ( ( v1_funct_1 @ C ) & 
% 0.47/0.63                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.47/0.63                 ( m1_subset_1 @
% 0.47/0.63                   C @ 
% 0.47/0.63                   ( k1_zfmisc_1 @
% 0.47/0.63                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.47/0.63               ( ![D:$i]:
% 0.47/0.63                 ( ( ( v1_funct_1 @ D ) & 
% 0.47/0.63                     ( v1_funct_2 @
% 0.47/0.63                       D @ 
% 0.47/0.63                       ( u1_struct_0 @
% 0.47/0.63                         ( g1_pre_topc @
% 0.47/0.63                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 0.47/0.63                       ( u1_struct_0 @ B ) ) & 
% 0.47/0.63                     ( m1_subset_1 @
% 0.47/0.63                       D @ 
% 0.47/0.63                       ( k1_zfmisc_1 @
% 0.47/0.63                         ( k2_zfmisc_1 @
% 0.47/0.63                           ( u1_struct_0 @
% 0.47/0.63                             ( g1_pre_topc @
% 0.47/0.63                               ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 0.47/0.63                           ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.47/0.63                   ( ( ( C ) = ( D ) ) =>
% 0.47/0.63                     ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.47/0.63                       ( v5_pre_topc @
% 0.47/0.63                         D @ 
% 0.47/0.63                         ( g1_pre_topc @
% 0.47/0.63                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ 
% 0.47/0.63                         B ) ) ) ) ) ) ) ) ) ))).
% 0.47/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.63    (~( ![A:$i]:
% 0.47/0.63        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.63          ( ![B:$i]:
% 0.47/0.63            ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.47/0.63              ( ![C:$i]:
% 0.47/0.63                ( ( ( v1_funct_1 @ C ) & 
% 0.47/0.63                    ( v1_funct_2 @
% 0.47/0.63                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.47/0.63                    ( m1_subset_1 @
% 0.47/0.63                      C @ 
% 0.47/0.63                      ( k1_zfmisc_1 @
% 0.47/0.63                        ( k2_zfmisc_1 @
% 0.47/0.63                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.47/0.63                  ( ![D:$i]:
% 0.47/0.63                    ( ( ( v1_funct_1 @ D ) & 
% 0.47/0.63                        ( v1_funct_2 @
% 0.47/0.63                          D @ 
% 0.47/0.63                          ( u1_struct_0 @
% 0.47/0.63                            ( g1_pre_topc @
% 0.47/0.63                              ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 0.47/0.63                          ( u1_struct_0 @ B ) ) & 
% 0.47/0.63                        ( m1_subset_1 @
% 0.47/0.63                          D @ 
% 0.47/0.63                          ( k1_zfmisc_1 @
% 0.47/0.63                            ( k2_zfmisc_1 @
% 0.47/0.63                              ( u1_struct_0 @
% 0.47/0.63                                ( g1_pre_topc @
% 0.47/0.64                                  ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 0.47/0.64                              ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.47/0.64                      ( ( ( C ) = ( D ) ) =>
% 0.47/0.64                        ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.47/0.64                          ( v5_pre_topc @
% 0.47/0.64                            D @ 
% 0.47/0.64                            ( g1_pre_topc @
% 0.47/0.64                              ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ 
% 0.47/0.64                            B ) ) ) ) ) ) ) ) ) ) )),
% 0.47/0.64    inference('cnf.neg', [status(esa)], [t62_pre_topc])).
% 0.47/0.64  thf('4', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_D_1 @ 
% 0.47/0.64        (k1_zfmisc_1 @ 
% 0.47/0.64         (k2_zfmisc_1 @ 
% 0.47/0.64          (u1_struct_0 @ 
% 0.47/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64          (u1_struct_0 @ sk_B))))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('5', plain, (((sk_C) = (sk_D_1))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('6', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_C @ 
% 0.47/0.64        (k1_zfmisc_1 @ 
% 0.47/0.64         (k2_zfmisc_1 @ 
% 0.47/0.64          (u1_struct_0 @ 
% 0.47/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64          (u1_struct_0 @ sk_B))))),
% 0.47/0.64      inference('demod', [status(thm)], ['4', '5'])).
% 0.47/0.64  thf(d12_pre_topc, axiom,
% 0.47/0.64    (![A:$i]:
% 0.47/0.64     ( ( l1_pre_topc @ A ) =>
% 0.47/0.64       ( ![B:$i]:
% 0.47/0.64         ( ( l1_pre_topc @ B ) =>
% 0.47/0.64           ( ![C:$i]:
% 0.47/0.64             ( ( ( v1_funct_1 @ C ) & 
% 0.47/0.64                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.47/0.64                 ( m1_subset_1 @
% 0.47/0.64                   C @ 
% 0.47/0.64                   ( k1_zfmisc_1 @
% 0.47/0.64                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.47/0.64               ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.47/0.64                 ( ![D:$i]:
% 0.47/0.64                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.47/0.64                     ( ( v4_pre_topc @ D @ B ) =>
% 0.47/0.64                       ( v4_pre_topc @
% 0.47/0.64                         ( k8_relset_1 @
% 0.47/0.64                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.47/0.64                         A ) ) ) ) ) ) ) ) ) ))).
% 0.47/0.64  thf('7', plain,
% 0.47/0.64      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.47/0.64         (~ (l1_pre_topc @ X5)
% 0.47/0.64          | (v4_pre_topc @ (sk_D @ X6 @ X5 @ X7) @ X5)
% 0.47/0.64          | (v5_pre_topc @ X6 @ X7 @ X5)
% 0.47/0.64          | ~ (m1_subset_1 @ X6 @ 
% 0.47/0.64               (k1_zfmisc_1 @ 
% 0.47/0.64                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))))
% 0.47/0.64          | ~ (v1_funct_2 @ X6 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))
% 0.47/0.64          | ~ (v1_funct_1 @ X6)
% 0.47/0.64          | ~ (l1_pre_topc @ X7))),
% 0.47/0.64      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.47/0.64  thf('8', plain,
% 0.47/0.64      ((~ (l1_pre_topc @ 
% 0.47/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.47/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.47/0.64        | ~ (v1_funct_2 @ sk_C @ 
% 0.47/0.64             (u1_struct_0 @ 
% 0.47/0.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64             (u1_struct_0 @ sk_B))
% 0.47/0.64        | (v5_pre_topc @ sk_C @ 
% 0.47/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)
% 0.47/0.64        | (v4_pre_topc @ 
% 0.47/0.64           (sk_D @ sk_C @ sk_B @ 
% 0.47/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64           sk_B)
% 0.47/0.64        | ~ (l1_pre_topc @ sk_B))),
% 0.47/0.64      inference('sup-', [status(thm)], ['6', '7'])).
% 0.47/0.64  thf('9', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('10', plain,
% 0.47/0.64      ((v1_funct_2 @ sk_D_1 @ 
% 0.47/0.64        (u1_struct_0 @ 
% 0.47/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64        (u1_struct_0 @ sk_B))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('11', plain, (((sk_C) = (sk_D_1))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('12', plain,
% 0.47/0.64      ((v1_funct_2 @ sk_C @ 
% 0.47/0.64        (u1_struct_0 @ 
% 0.47/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64        (u1_struct_0 @ sk_B))),
% 0.47/0.64      inference('demod', [status(thm)], ['10', '11'])).
% 0.47/0.64  thf('13', plain, ((l1_pre_topc @ sk_B)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('14', plain,
% 0.47/0.64      ((~ (l1_pre_topc @ 
% 0.47/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.47/0.64        | (v5_pre_topc @ sk_C @ 
% 0.47/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)
% 0.47/0.64        | (v4_pre_topc @ 
% 0.47/0.64           (sk_D @ sk_C @ sk_B @ 
% 0.47/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64           sk_B))),
% 0.47/0.64      inference('demod', [status(thm)], ['8', '9', '12', '13'])).
% 0.47/0.64  thf('15', plain,
% 0.47/0.64      ((~ (l1_pre_topc @ sk_A)
% 0.47/0.64        | (v4_pre_topc @ 
% 0.47/0.64           (sk_D @ sk_C @ sk_B @ 
% 0.47/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64           sk_B)
% 0.47/0.64        | (v5_pre_topc @ sk_C @ 
% 0.47/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))),
% 0.47/0.64      inference('sup-', [status(thm)], ['3', '14'])).
% 0.47/0.64  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('17', plain,
% 0.47/0.64      (((v4_pre_topc @ 
% 0.47/0.64         (sk_D @ sk_C @ sk_B @ 
% 0.47/0.64          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64         sk_B)
% 0.47/0.64        | (v5_pre_topc @ sk_C @ 
% 0.47/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))),
% 0.47/0.64      inference('demod', [status(thm)], ['15', '16'])).
% 0.47/0.64  thf('18', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (l1_pre_topc @ X0)
% 0.47/0.64          | (l1_pre_topc @ 
% 0.47/0.64             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['0', '1'])).
% 0.47/0.64  thf('19', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_C @ 
% 0.47/0.64        (k1_zfmisc_1 @ 
% 0.47/0.64         (k2_zfmisc_1 @ 
% 0.47/0.64          (u1_struct_0 @ 
% 0.47/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64          (u1_struct_0 @ sk_B))))),
% 0.47/0.64      inference('demod', [status(thm)], ['4', '5'])).
% 0.47/0.64  thf('20', plain,
% 0.47/0.64      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.47/0.64         (~ (l1_pre_topc @ X5)
% 0.47/0.64          | (m1_subset_1 @ (sk_D @ X6 @ X5 @ X7) @ 
% 0.47/0.64             (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.47/0.64          | (v5_pre_topc @ X6 @ X7 @ X5)
% 0.47/0.64          | ~ (m1_subset_1 @ X6 @ 
% 0.47/0.64               (k1_zfmisc_1 @ 
% 0.47/0.64                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))))
% 0.47/0.64          | ~ (v1_funct_2 @ X6 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))
% 0.47/0.64          | ~ (v1_funct_1 @ X6)
% 0.47/0.64          | ~ (l1_pre_topc @ X7))),
% 0.47/0.64      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.47/0.64  thf('21', plain,
% 0.47/0.64      ((~ (l1_pre_topc @ 
% 0.47/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.47/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.47/0.64        | ~ (v1_funct_2 @ sk_C @ 
% 0.47/0.64             (u1_struct_0 @ 
% 0.47/0.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64             (u1_struct_0 @ sk_B))
% 0.47/0.64        | (v5_pre_topc @ sk_C @ 
% 0.47/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)
% 0.47/0.64        | (m1_subset_1 @ 
% 0.47/0.64           (sk_D @ sk_C @ sk_B @ 
% 0.47/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.47/0.64        | ~ (l1_pre_topc @ sk_B))),
% 0.47/0.64      inference('sup-', [status(thm)], ['19', '20'])).
% 0.47/0.64  thf('22', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('23', plain,
% 0.47/0.64      ((v1_funct_2 @ sk_C @ 
% 0.47/0.64        (u1_struct_0 @ 
% 0.47/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64        (u1_struct_0 @ sk_B))),
% 0.47/0.64      inference('demod', [status(thm)], ['10', '11'])).
% 0.47/0.64  thf('24', plain, ((l1_pre_topc @ sk_B)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('25', plain,
% 0.47/0.64      ((~ (l1_pre_topc @ 
% 0.47/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.47/0.64        | (v5_pre_topc @ sk_C @ 
% 0.47/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)
% 0.47/0.64        | (m1_subset_1 @ 
% 0.47/0.64           (sk_D @ sk_C @ sk_B @ 
% 0.47/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.47/0.64      inference('demod', [status(thm)], ['21', '22', '23', '24'])).
% 0.47/0.64  thf('26', plain,
% 0.47/0.64      ((~ (l1_pre_topc @ sk_A)
% 0.47/0.64        | (m1_subset_1 @ 
% 0.47/0.64           (sk_D @ sk_C @ sk_B @ 
% 0.47/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.47/0.64        | (v5_pre_topc @ sk_C @ 
% 0.47/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))),
% 0.47/0.64      inference('sup-', [status(thm)], ['18', '25'])).
% 0.47/0.64  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('28', plain,
% 0.47/0.64      (((m1_subset_1 @ 
% 0.47/0.64         (sk_D @ sk_C @ sk_B @ 
% 0.47/0.64          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.47/0.64        | (v5_pre_topc @ sk_C @ 
% 0.47/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))),
% 0.47/0.64      inference('demod', [status(thm)], ['26', '27'])).
% 0.47/0.64  thf('29', plain,
% 0.47/0.64      (((v5_pre_topc @ sk_D_1 @ 
% 0.47/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)
% 0.47/0.64        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('30', plain,
% 0.47/0.64      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.47/0.64         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.47/0.64      inference('split', [status(esa)], ['29'])).
% 0.47/0.64  thf('31', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_C @ 
% 0.47/0.64        (k1_zfmisc_1 @ 
% 0.47/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('32', plain,
% 0.47/0.64      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.47/0.64         (~ (l1_pre_topc @ X5)
% 0.47/0.64          | ~ (v5_pre_topc @ X6 @ X7 @ X5)
% 0.47/0.64          | ~ (v4_pre_topc @ X8 @ X5)
% 0.47/0.64          | (v4_pre_topc @ 
% 0.47/0.64             (k8_relset_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5) @ X6 @ X8) @ 
% 0.47/0.64             X7)
% 0.47/0.64          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.47/0.64          | ~ (m1_subset_1 @ X6 @ 
% 0.47/0.64               (k1_zfmisc_1 @ 
% 0.47/0.64                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))))
% 0.47/0.64          | ~ (v1_funct_2 @ X6 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))
% 0.47/0.64          | ~ (v1_funct_1 @ X6)
% 0.47/0.64          | ~ (l1_pre_topc @ X7))),
% 0.47/0.64      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.47/0.64  thf('33', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (l1_pre_topc @ sk_A)
% 0.47/0.64          | ~ (v1_funct_1 @ sk_C)
% 0.47/0.64          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.47/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.47/0.64          | (v4_pre_topc @ 
% 0.47/0.64             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.64              sk_C @ X0) @ 
% 0.47/0.64             sk_A)
% 0.47/0.64          | ~ (v4_pre_topc @ X0 @ sk_B)
% 0.47/0.64          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.47/0.64          | ~ (l1_pre_topc @ sk_B))),
% 0.47/0.64      inference('sup-', [status(thm)], ['31', '32'])).
% 0.47/0.64  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('36', plain,
% 0.47/0.64      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('37', plain, ((l1_pre_topc @ sk_B)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('38', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.47/0.64          | (v4_pre_topc @ 
% 0.47/0.64             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.64              sk_C @ X0) @ 
% 0.47/0.64             sk_A)
% 0.47/0.64          | ~ (v4_pre_topc @ X0 @ sk_B)
% 0.47/0.64          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.47/0.64      inference('demod', [status(thm)], ['33', '34', '35', '36', '37'])).
% 0.47/0.64  thf('39', plain,
% 0.47/0.64      ((![X0 : $i]:
% 0.47/0.64          (~ (v4_pre_topc @ X0 @ sk_B)
% 0.47/0.64           | (v4_pre_topc @ 
% 0.47/0.64              (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.64               sk_C @ X0) @ 
% 0.47/0.64              sk_A)
% 0.47/0.64           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))))
% 0.47/0.64         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['30', '38'])).
% 0.47/0.64  thf('40', plain,
% 0.47/0.64      (((v5_pre_topc @ sk_D_1 @ 
% 0.47/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)
% 0.47/0.64        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('41', plain, (((sk_C) = (sk_D_1))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('42', plain,
% 0.47/0.64      (((v5_pre_topc @ sk_C @ 
% 0.47/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)
% 0.47/0.64        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.47/0.64      inference('demod', [status(thm)], ['40', '41'])).
% 0.47/0.64  thf('43', plain,
% 0.47/0.64      (((v5_pre_topc @ sk_C @ 
% 0.47/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))
% 0.47/0.64         <= (((v5_pre_topc @ sk_C @ 
% 0.47/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.47/0.64               sk_B)))),
% 0.47/0.64      inference('split', [status(esa)], ['42'])).
% 0.47/0.64  thf('44', plain,
% 0.47/0.64      ((~ (v5_pre_topc @ sk_D_1 @ 
% 0.47/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)
% 0.47/0.64        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('45', plain,
% 0.47/0.64      ((~ (v5_pre_topc @ sk_D_1 @ 
% 0.47/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))
% 0.47/0.64         <= (~
% 0.47/0.64             ((v5_pre_topc @ sk_D_1 @ 
% 0.47/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.47/0.64               sk_B)))),
% 0.47/0.64      inference('split', [status(esa)], ['44'])).
% 0.47/0.64  thf('46', plain, (((sk_C) = (sk_D_1))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('47', plain,
% 0.47/0.64      ((~ (v5_pre_topc @ sk_C @ 
% 0.47/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))
% 0.47/0.64         <= (~
% 0.47/0.64             ((v5_pre_topc @ sk_D_1 @ 
% 0.47/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.47/0.64               sk_B)))),
% 0.47/0.64      inference('demod', [status(thm)], ['45', '46'])).
% 0.47/0.64  thf('48', plain,
% 0.47/0.64      (~
% 0.47/0.64       ((v5_pre_topc @ sk_C @ 
% 0.47/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)) | 
% 0.47/0.64       ((v5_pre_topc @ sk_D_1 @ 
% 0.47/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))),
% 0.47/0.64      inference('sup-', [status(thm)], ['43', '47'])).
% 0.47/0.64  thf('49', plain,
% 0.47/0.64      ((~ (v5_pre_topc @ sk_D_1 @ 
% 0.47/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)
% 0.47/0.64        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('50', plain, (((sk_C) = (sk_D_1))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('51', plain,
% 0.47/0.64      ((~ (v5_pre_topc @ sk_C @ 
% 0.47/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)
% 0.47/0.64        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.47/0.64      inference('demod', [status(thm)], ['49', '50'])).
% 0.47/0.64  thf('52', plain,
% 0.47/0.64      (~
% 0.47/0.64       ((v5_pre_topc @ sk_C @ 
% 0.47/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)) | 
% 0.47/0.64       ~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.47/0.64      inference('split', [status(esa)], ['51'])).
% 0.47/0.64  thf('53', plain,
% 0.47/0.64      (![X11 : $i]:
% 0.47/0.64         ((m1_subset_1 @ (u1_pre_topc @ X11) @ 
% 0.47/0.64           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))
% 0.47/0.64          | ~ (l1_pre_topc @ X11))),
% 0.47/0.64      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.47/0.64  thf('54', plain,
% 0.47/0.64      (![X9 : $i, X10 : $i]:
% 0.47/0.64         ((v1_pre_topc @ (g1_pre_topc @ X9 @ X10))
% 0.47/0.64          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X9))))),
% 0.47/0.64      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 0.47/0.64  thf('55', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (l1_pre_topc @ X0)
% 0.47/0.64          | (v1_pre_topc @ 
% 0.47/0.64             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['53', '54'])).
% 0.47/0.64  thf(abstractness_v1_pre_topc, axiom,
% 0.47/0.64    (![A:$i]:
% 0.47/0.64     ( ( l1_pre_topc @ A ) =>
% 0.47/0.64       ( ( v1_pre_topc @ A ) =>
% 0.47/0.64         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.47/0.64  thf('56', plain,
% 0.47/0.64      (![X4 : $i]:
% 0.47/0.64         (~ (v1_pre_topc @ X4)
% 0.47/0.64          | ((X4) = (g1_pre_topc @ (u1_struct_0 @ X4) @ (u1_pre_topc @ X4)))
% 0.47/0.64          | ~ (l1_pre_topc @ X4))),
% 0.47/0.64      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.47/0.64  thf('57', plain,
% 0.47/0.64      (![X11 : $i]:
% 0.47/0.64         ((m1_subset_1 @ (u1_pre_topc @ X11) @ 
% 0.47/0.64           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))
% 0.47/0.64          | ~ (l1_pre_topc @ X11))),
% 0.47/0.64      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.47/0.64  thf(free_g1_pre_topc, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.47/0.64       ( ![C:$i,D:$i]:
% 0.47/0.64         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.47/0.64           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.47/0.64  thf('58', plain,
% 0.47/0.64      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.47/0.64         (((g1_pre_topc @ X14 @ X15) != (g1_pre_topc @ X12 @ X13))
% 0.47/0.64          | ((X14) = (X12))
% 0.47/0.64          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X14))))),
% 0.47/0.64      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.47/0.64  thf('59', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.64         (~ (l1_pre_topc @ X0)
% 0.47/0.64          | ((u1_struct_0 @ X0) = (X1))
% 0.47/0.64          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.47/0.64              != (g1_pre_topc @ X1 @ X2)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['57', '58'])).
% 0.47/0.64  thf('60', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.64         (((X0) != (g1_pre_topc @ X2 @ X1))
% 0.47/0.64          | ~ (l1_pre_topc @ X0)
% 0.47/0.64          | ~ (v1_pre_topc @ X0)
% 0.47/0.64          | ((u1_struct_0 @ X0) = (X2))
% 0.47/0.64          | ~ (l1_pre_topc @ X0))),
% 0.47/0.64      inference('sup-', [status(thm)], ['56', '59'])).
% 0.47/0.64  thf('61', plain,
% 0.47/0.64      (![X1 : $i, X2 : $i]:
% 0.47/0.64         (((u1_struct_0 @ (g1_pre_topc @ X2 @ X1)) = (X2))
% 0.47/0.64          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 0.47/0.64          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['60'])).
% 0.47/0.64  thf('62', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (l1_pre_topc @ X0)
% 0.47/0.64          | ~ (l1_pre_topc @ 
% 0.47/0.64               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.47/0.64          | ((u1_struct_0 @ 
% 0.47/0.64              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.47/0.64              = (u1_struct_0 @ X0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['55', '61'])).
% 0.47/0.64  thf('63', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (l1_pre_topc @ X0)
% 0.47/0.64          | (l1_pre_topc @ 
% 0.47/0.64             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['0', '1'])).
% 0.47/0.64  thf('64', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((u1_struct_0 @ 
% 0.47/0.64            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.47/0.64            = (u1_struct_0 @ X0))
% 0.47/0.64          | ~ (l1_pre_topc @ X0))),
% 0.47/0.64      inference('clc', [status(thm)], ['62', '63'])).
% 0.47/0.64  thf('65', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_C @ 
% 0.47/0.64        (k1_zfmisc_1 @ 
% 0.47/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('66', plain,
% 0.47/0.64      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.47/0.64         (~ (l1_pre_topc @ X5)
% 0.47/0.64          | (m1_subset_1 @ (sk_D @ X6 @ X5 @ X7) @ 
% 0.47/0.64             (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.47/0.64          | (v5_pre_topc @ X6 @ X7 @ X5)
% 0.47/0.64          | ~ (m1_subset_1 @ X6 @ 
% 0.47/0.64               (k1_zfmisc_1 @ 
% 0.47/0.64                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))))
% 0.47/0.64          | ~ (v1_funct_2 @ X6 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))
% 0.47/0.64          | ~ (v1_funct_1 @ X6)
% 0.47/0.64          | ~ (l1_pre_topc @ X7))),
% 0.47/0.64      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.47/0.64  thf('67', plain,
% 0.47/0.64      ((~ (l1_pre_topc @ sk_A)
% 0.47/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.47/0.64        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.47/0.64        | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.47/0.64        | (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.47/0.64           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.47/0.64        | ~ (l1_pre_topc @ sk_B))),
% 0.47/0.64      inference('sup-', [status(thm)], ['65', '66'])).
% 0.47/0.64  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('69', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('70', plain,
% 0.47/0.64      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('71', plain, ((l1_pre_topc @ sk_B)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('72', plain,
% 0.47/0.64      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.47/0.64        | (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.47/0.64           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.47/0.64      inference('demod', [status(thm)], ['67', '68', '69', '70', '71'])).
% 0.47/0.64  thf('73', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (l1_pre_topc @ X0)
% 0.47/0.64          | (l1_pre_topc @ 
% 0.47/0.64             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['0', '1'])).
% 0.47/0.64  thf('74', plain,
% 0.47/0.64      (((v5_pre_topc @ sk_D_1 @ 
% 0.47/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))
% 0.47/0.64         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.47/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.47/0.64               sk_B)))),
% 0.47/0.64      inference('split', [status(esa)], ['29'])).
% 0.47/0.64  thf('75', plain, (((sk_C) = (sk_D_1))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('76', plain,
% 0.47/0.64      (((v5_pre_topc @ sk_C @ 
% 0.47/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))
% 0.47/0.64         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.47/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.47/0.64               sk_B)))),
% 0.47/0.64      inference('demod', [status(thm)], ['74', '75'])).
% 0.47/0.64  thf('77', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_C @ 
% 0.47/0.64        (k1_zfmisc_1 @ 
% 0.47/0.64         (k2_zfmisc_1 @ 
% 0.47/0.64          (u1_struct_0 @ 
% 0.47/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64          (u1_struct_0 @ sk_B))))),
% 0.47/0.64      inference('demod', [status(thm)], ['4', '5'])).
% 0.47/0.64  thf('78', plain,
% 0.47/0.64      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.47/0.64         (~ (l1_pre_topc @ X5)
% 0.47/0.64          | ~ (v5_pre_topc @ X6 @ X7 @ X5)
% 0.47/0.64          | ~ (v4_pre_topc @ X8 @ X5)
% 0.47/0.64          | (v4_pre_topc @ 
% 0.47/0.64             (k8_relset_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5) @ X6 @ X8) @ 
% 0.47/0.64             X7)
% 0.47/0.64          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.47/0.64          | ~ (m1_subset_1 @ X6 @ 
% 0.47/0.64               (k1_zfmisc_1 @ 
% 0.47/0.64                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))))
% 0.47/0.64          | ~ (v1_funct_2 @ X6 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))
% 0.47/0.64          | ~ (v1_funct_1 @ X6)
% 0.47/0.64          | ~ (l1_pre_topc @ X7))),
% 0.47/0.64      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.47/0.64  thf('79', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (l1_pre_topc @ 
% 0.47/0.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.47/0.64          | ~ (v1_funct_1 @ sk_C)
% 0.47/0.64          | ~ (v1_funct_2 @ sk_C @ 
% 0.47/0.64               (u1_struct_0 @ 
% 0.47/0.64                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64               (u1_struct_0 @ sk_B))
% 0.47/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.47/0.64          | (v4_pre_topc @ 
% 0.47/0.64             (k8_relset_1 @ 
% 0.47/0.64              (u1_struct_0 @ 
% 0.47/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64              (u1_struct_0 @ sk_B) @ sk_C @ X0) @ 
% 0.47/0.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.47/0.64          | ~ (v4_pre_topc @ X0 @ sk_B)
% 0.47/0.64          | ~ (v5_pre_topc @ sk_C @ 
% 0.47/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.47/0.64               sk_B)
% 0.47/0.64          | ~ (l1_pre_topc @ sk_B))),
% 0.47/0.64      inference('sup-', [status(thm)], ['77', '78'])).
% 0.47/0.64  thf('80', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('81', plain,
% 0.47/0.64      ((v1_funct_2 @ sk_C @ 
% 0.47/0.64        (u1_struct_0 @ 
% 0.47/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64        (u1_struct_0 @ sk_B))),
% 0.47/0.64      inference('demod', [status(thm)], ['10', '11'])).
% 0.47/0.64  thf('82', plain, ((l1_pre_topc @ sk_B)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('83', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (l1_pre_topc @ 
% 0.47/0.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.47/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.47/0.64          | (v4_pre_topc @ 
% 0.47/0.64             (k8_relset_1 @ 
% 0.47/0.64              (u1_struct_0 @ 
% 0.47/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64              (u1_struct_0 @ sk_B) @ sk_C @ X0) @ 
% 0.47/0.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.47/0.64          | ~ (v4_pre_topc @ X0 @ sk_B)
% 0.47/0.64          | ~ (v5_pre_topc @ sk_C @ 
% 0.47/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.47/0.64               sk_B))),
% 0.47/0.64      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 0.47/0.64  thf('84', plain,
% 0.47/0.64      ((![X0 : $i]:
% 0.47/0.64          (~ (v4_pre_topc @ X0 @ sk_B)
% 0.47/0.64           | (v4_pre_topc @ 
% 0.47/0.64              (k8_relset_1 @ 
% 0.47/0.64               (u1_struct_0 @ 
% 0.47/0.64                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64               (u1_struct_0 @ sk_B) @ sk_C @ X0) @ 
% 0.47/0.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.47/0.64           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.47/0.64           | ~ (l1_pre_topc @ 
% 0.47/0.64                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.47/0.64         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.47/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.47/0.64               sk_B)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['76', '83'])).
% 0.47/0.64  thf('85', plain,
% 0.47/0.64      ((![X0 : $i]:
% 0.47/0.64          (~ (l1_pre_topc @ sk_A)
% 0.47/0.64           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.47/0.64           | (v4_pre_topc @ 
% 0.47/0.64              (k8_relset_1 @ 
% 0.47/0.64               (u1_struct_0 @ 
% 0.47/0.64                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64               (u1_struct_0 @ sk_B) @ sk_C @ X0) @ 
% 0.47/0.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.47/0.64           | ~ (v4_pre_topc @ X0 @ sk_B)))
% 0.47/0.64         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.47/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.47/0.64               sk_B)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['73', '84'])).
% 0.47/0.64  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('87', plain,
% 0.47/0.64      ((![X0 : $i]:
% 0.47/0.64          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.47/0.64           | (v4_pre_topc @ 
% 0.47/0.64              (k8_relset_1 @ 
% 0.47/0.64               (u1_struct_0 @ 
% 0.47/0.64                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64               (u1_struct_0 @ sk_B) @ sk_C @ X0) @ 
% 0.47/0.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.47/0.64           | ~ (v4_pre_topc @ X0 @ sk_B)))
% 0.47/0.64         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.47/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.47/0.64               sk_B)))),
% 0.47/0.64      inference('demod', [status(thm)], ['85', '86'])).
% 0.47/0.64  thf('88', plain,
% 0.47/0.64      ((((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.47/0.64         | ~ (v4_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.47/0.64         | (v4_pre_topc @ 
% 0.47/0.64            (k8_relset_1 @ 
% 0.47/0.64             (u1_struct_0 @ 
% 0.47/0.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64             (u1_struct_0 @ sk_B) @ sk_C @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.47/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.47/0.64         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.47/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.47/0.64               sk_B)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['72', '87'])).
% 0.47/0.64  thf('89', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_C @ 
% 0.47/0.64        (k1_zfmisc_1 @ 
% 0.47/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('90', plain,
% 0.47/0.64      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.47/0.64         (~ (l1_pre_topc @ X5)
% 0.47/0.64          | (v4_pre_topc @ (sk_D @ X6 @ X5 @ X7) @ X5)
% 0.47/0.64          | (v5_pre_topc @ X6 @ X7 @ X5)
% 0.47/0.64          | ~ (m1_subset_1 @ X6 @ 
% 0.47/0.64               (k1_zfmisc_1 @ 
% 0.47/0.64                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))))
% 0.47/0.64          | ~ (v1_funct_2 @ X6 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))
% 0.47/0.64          | ~ (v1_funct_1 @ X6)
% 0.47/0.64          | ~ (l1_pre_topc @ X7))),
% 0.47/0.64      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.47/0.64  thf('91', plain,
% 0.47/0.64      ((~ (l1_pre_topc @ sk_A)
% 0.47/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.47/0.64        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.47/0.64        | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.47/0.64        | (v4_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.47/0.64        | ~ (l1_pre_topc @ sk_B))),
% 0.47/0.64      inference('sup-', [status(thm)], ['89', '90'])).
% 0.47/0.64  thf('92', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('93', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('94', plain,
% 0.47/0.64      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('95', plain, ((l1_pre_topc @ sk_B)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('96', plain,
% 0.47/0.64      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.47/0.64        | (v4_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.47/0.64      inference('demod', [status(thm)], ['91', '92', '93', '94', '95'])).
% 0.47/0.64  thf('97', plain,
% 0.47/0.64      ((((v4_pre_topc @ 
% 0.47/0.64          (k8_relset_1 @ 
% 0.47/0.64           (u1_struct_0 @ 
% 0.47/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64           (u1_struct_0 @ sk_B) @ sk_C @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.47/0.64          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.47/0.64         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)))
% 0.47/0.64         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.47/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.47/0.64               sk_B)))),
% 0.47/0.64      inference('clc', [status(thm)], ['88', '96'])).
% 0.47/0.64  thf('98', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_C @ 
% 0.47/0.64        (k1_zfmisc_1 @ 
% 0.47/0.64         (k2_zfmisc_1 @ 
% 0.47/0.64          (u1_struct_0 @ 
% 0.47/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64          (u1_struct_0 @ sk_B))))),
% 0.47/0.64      inference('demod', [status(thm)], ['4', '5'])).
% 0.47/0.64  thf(dt_k8_relset_1, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.64       ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.47/0.64  thf('99', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.64         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.47/0.64          | (m1_subset_1 @ (k8_relset_1 @ X1 @ X2 @ X0 @ X3) @ 
% 0.47/0.64             (k1_zfmisc_1 @ X1)))),
% 0.47/0.64      inference('cnf', [status(esa)], [dt_k8_relset_1])).
% 0.47/0.64  thf('100', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (m1_subset_1 @ 
% 0.47/0.64          (k8_relset_1 @ 
% 0.47/0.64           (u1_struct_0 @ 
% 0.47/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64           (u1_struct_0 @ sk_B) @ sk_C @ X0) @ 
% 0.47/0.64          (k1_zfmisc_1 @ 
% 0.47/0.64           (u1_struct_0 @ 
% 0.47/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['98', '99'])).
% 0.47/0.64  thf(t61_pre_topc, axiom,
% 0.47/0.64    (![A:$i]:
% 0.47/0.64     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.64       ( ![B:$i]:
% 0.47/0.64         ( ( ( v4_pre_topc @ B @ A ) & 
% 0.47/0.64             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) <=>
% 0.47/0.64           ( ( v4_pre_topc @
% 0.47/0.64               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.47/0.64             ( m1_subset_1 @
% 0.47/0.64               B @ 
% 0.47/0.64               ( k1_zfmisc_1 @
% 0.47/0.64                 ( u1_struct_0 @
% 0.47/0.64                   ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ))).
% 0.47/0.64  thf('101', plain,
% 0.47/0.64      (![X16 : $i, X17 : $i]:
% 0.47/0.64         (~ (v4_pre_topc @ X16 @ 
% 0.47/0.64             (g1_pre_topc @ (u1_struct_0 @ X17) @ (u1_pre_topc @ X17)))
% 0.47/0.64          | ~ (m1_subset_1 @ X16 @ 
% 0.47/0.64               (k1_zfmisc_1 @ 
% 0.47/0.64                (u1_struct_0 @ 
% 0.47/0.64                 (g1_pre_topc @ (u1_struct_0 @ X17) @ (u1_pre_topc @ X17)))))
% 0.47/0.64          | (v4_pre_topc @ X16 @ X17)
% 0.47/0.64          | ~ (l1_pre_topc @ X17)
% 0.47/0.64          | ~ (v2_pre_topc @ X17))),
% 0.47/0.64      inference('cnf', [status(esa)], [t61_pre_topc])).
% 0.47/0.64  thf('102', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v2_pre_topc @ sk_A)
% 0.47/0.64          | ~ (l1_pre_topc @ sk_A)
% 0.47/0.64          | (v4_pre_topc @ 
% 0.47/0.64             (k8_relset_1 @ 
% 0.47/0.64              (u1_struct_0 @ 
% 0.47/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64              (u1_struct_0 @ sk_B) @ sk_C @ X0) @ 
% 0.47/0.64             sk_A)
% 0.47/0.64          | ~ (v4_pre_topc @ 
% 0.47/0.64               (k8_relset_1 @ 
% 0.47/0.64                (u1_struct_0 @ 
% 0.47/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64                (u1_struct_0 @ sk_B) @ sk_C @ X0) @ 
% 0.47/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['100', '101'])).
% 0.47/0.64  thf('103', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('104', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('105', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((v4_pre_topc @ 
% 0.47/0.64           (k8_relset_1 @ 
% 0.47/0.64            (u1_struct_0 @ 
% 0.47/0.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64            (u1_struct_0 @ sk_B) @ sk_C @ X0) @ 
% 0.47/0.64           sk_A)
% 0.47/0.64          | ~ (v4_pre_topc @ 
% 0.47/0.64               (k8_relset_1 @ 
% 0.47/0.64                (u1_struct_0 @ 
% 0.47/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64                (u1_struct_0 @ sk_B) @ sk_C @ X0) @ 
% 0.47/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 0.47/0.64      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.47/0.64  thf('106', plain,
% 0.47/0.64      ((((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.47/0.64         | (v4_pre_topc @ 
% 0.47/0.64            (k8_relset_1 @ 
% 0.47/0.64             (u1_struct_0 @ 
% 0.47/0.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64             (u1_struct_0 @ sk_B) @ sk_C @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.47/0.64            sk_A)))
% 0.47/0.64         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.47/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.47/0.64               sk_B)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['97', '105'])).
% 0.47/0.64  thf('107', plain,
% 0.47/0.64      ((((v4_pre_topc @ 
% 0.47/0.64          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.47/0.64           (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.47/0.64          sk_A)
% 0.47/0.64         | ~ (l1_pre_topc @ sk_A)
% 0.47/0.64         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)))
% 0.47/0.64         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.47/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.47/0.64               sk_B)))),
% 0.47/0.64      inference('sup+', [status(thm)], ['64', '106'])).
% 0.47/0.64  thf('108', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('109', plain,
% 0.47/0.64      ((((v4_pre_topc @ 
% 0.47/0.64          (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.47/0.64           (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 0.47/0.64          sk_A)
% 0.47/0.64         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)))
% 0.47/0.64         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.47/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.47/0.64               sk_B)))),
% 0.47/0.64      inference('demod', [status(thm)], ['107', '108'])).
% 0.47/0.64  thf('110', plain,
% 0.47/0.64      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.47/0.64         (~ (l1_pre_topc @ X5)
% 0.47/0.64          | ~ (v4_pre_topc @ 
% 0.47/0.64               (k8_relset_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5) @ X6 @ 
% 0.47/0.64                (sk_D @ X6 @ X5 @ X7)) @ 
% 0.47/0.64               X7)
% 0.47/0.64          | (v5_pre_topc @ X6 @ X7 @ X5)
% 0.47/0.64          | ~ (m1_subset_1 @ X6 @ 
% 0.47/0.64               (k1_zfmisc_1 @ 
% 0.47/0.64                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))))
% 0.47/0.64          | ~ (v1_funct_2 @ X6 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))
% 0.47/0.64          | ~ (v1_funct_1 @ X6)
% 0.47/0.64          | ~ (l1_pre_topc @ X7))),
% 0.47/0.64      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.47/0.64  thf('111', plain,
% 0.47/0.64      ((((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.47/0.64         | ~ (l1_pre_topc @ sk_A)
% 0.47/0.64         | ~ (v1_funct_1 @ sk_C)
% 0.47/0.64         | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.47/0.64         | ~ (m1_subset_1 @ sk_C @ 
% 0.47/0.64              (k1_zfmisc_1 @ 
% 0.47/0.64               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.47/0.64         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.47/0.64         | ~ (l1_pre_topc @ sk_B)))
% 0.47/0.64         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.47/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.47/0.64               sk_B)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['109', '110'])).
% 0.47/0.64  thf('112', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('113', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('114', plain,
% 0.47/0.64      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('115', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_C @ 
% 0.47/0.64        (k1_zfmisc_1 @ 
% 0.47/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('116', plain, ((l1_pre_topc @ sk_B)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('117', plain,
% 0.47/0.64      ((((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.47/0.64         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)))
% 0.47/0.64         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.47/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.47/0.64               sk_B)))),
% 0.47/0.64      inference('demod', [status(thm)],
% 0.47/0.64                ['111', '112', '113', '114', '115', '116'])).
% 0.47/0.64  thf('118', plain,
% 0.47/0.64      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.47/0.64         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.47/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.47/0.64               sk_B)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['117'])).
% 0.47/0.64  thf('119', plain,
% 0.47/0.64      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.47/0.64         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.47/0.64      inference('split', [status(esa)], ['44'])).
% 0.47/0.64  thf('120', plain,
% 0.47/0.64      (~
% 0.47/0.64       ((v5_pre_topc @ sk_D_1 @ 
% 0.47/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)) | 
% 0.47/0.64       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.47/0.64      inference('sup-', [status(thm)], ['118', '119'])).
% 0.47/0.64  thf('121', plain,
% 0.47/0.64      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) | 
% 0.47/0.64       ((v5_pre_topc @ sk_C @ 
% 0.47/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))),
% 0.47/0.64      inference('split', [status(esa)], ['42'])).
% 0.47/0.64  thf('122', plain, (((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.47/0.64      inference('sat_resolution*', [status(thm)], ['48', '52', '120', '121'])).
% 0.47/0.64  thf('123', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v4_pre_topc @ X0 @ sk_B)
% 0.47/0.64          | (v4_pre_topc @ 
% 0.47/0.64             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.64              sk_C @ X0) @ 
% 0.47/0.64             sk_A)
% 0.47/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.47/0.64      inference('simpl_trail', [status(thm)], ['39', '122'])).
% 0.47/0.64  thf('124', plain,
% 0.47/0.64      (((v5_pre_topc @ sk_C @ 
% 0.47/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)
% 0.47/0.64        | (v4_pre_topc @ 
% 0.47/0.64           (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.47/0.64            (sk_D @ sk_C @ sk_B @ 
% 0.47/0.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) @ 
% 0.47/0.64           sk_A)
% 0.47/0.64        | ~ (v4_pre_topc @ 
% 0.47/0.64             (sk_D @ sk_C @ sk_B @ 
% 0.47/0.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64             sk_B))),
% 0.47/0.64      inference('sup-', [status(thm)], ['28', '123'])).
% 0.47/0.64  thf('125', plain,
% 0.47/0.64      ((~ (v5_pre_topc @ sk_C @ 
% 0.47/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))
% 0.47/0.64         <= (~
% 0.47/0.64             ((v5_pre_topc @ sk_D_1 @ 
% 0.47/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.47/0.64               sk_B)))),
% 0.47/0.64      inference('demod', [status(thm)], ['45', '46'])).
% 0.47/0.64  thf('126', plain,
% 0.47/0.64      (((v5_pre_topc @ sk_C @ 
% 0.47/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))
% 0.47/0.64         <= (((v5_pre_topc @ sk_D_1 @ 
% 0.47/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.47/0.64               sk_B)))),
% 0.47/0.64      inference('demod', [status(thm)], ['74', '75'])).
% 0.47/0.64  thf('127', plain,
% 0.47/0.64      ((~ (v5_pre_topc @ sk_C @ 
% 0.47/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))
% 0.47/0.64         <= (~
% 0.47/0.64             ((v5_pre_topc @ sk_C @ 
% 0.47/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.47/0.64               sk_B)))),
% 0.47/0.64      inference('split', [status(esa)], ['51'])).
% 0.47/0.64  thf('128', plain,
% 0.47/0.64      (~
% 0.47/0.64       ((v5_pre_topc @ sk_D_1 @ 
% 0.47/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)) | 
% 0.47/0.64       ((v5_pre_topc @ sk_C @ 
% 0.47/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))),
% 0.47/0.64      inference('sup-', [status(thm)], ['126', '127'])).
% 0.47/0.64  thf('129', plain,
% 0.47/0.64      (~
% 0.47/0.64       ((v5_pre_topc @ sk_D_1 @ 
% 0.47/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))),
% 0.47/0.64      inference('sat_resolution*', [status(thm)], ['48', '52', '120', '128'])).
% 0.47/0.64  thf('130', plain,
% 0.47/0.64      (~ (v5_pre_topc @ sk_C @ 
% 0.47/0.64          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)),
% 0.47/0.64      inference('simpl_trail', [status(thm)], ['125', '129'])).
% 0.47/0.64  thf('131', plain,
% 0.47/0.64      ((~ (v4_pre_topc @ 
% 0.47/0.64           (sk_D @ sk_C @ sk_B @ 
% 0.47/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64           sk_B)
% 0.47/0.64        | (v4_pre_topc @ 
% 0.47/0.64           (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.47/0.64            (sk_D @ sk_C @ sk_B @ 
% 0.47/0.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) @ 
% 0.47/0.64           sk_A))),
% 0.47/0.64      inference('clc', [status(thm)], ['124', '130'])).
% 0.47/0.64  thf('132', plain,
% 0.47/0.64      (((v5_pre_topc @ sk_C @ 
% 0.47/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)
% 0.47/0.64        | (v4_pre_topc @ 
% 0.47/0.64           (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.47/0.64            (sk_D @ sk_C @ sk_B @ 
% 0.47/0.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) @ 
% 0.47/0.64           sk_A))),
% 0.47/0.64      inference('sup-', [status(thm)], ['17', '131'])).
% 0.47/0.64  thf('133', plain,
% 0.47/0.64      (~ (v5_pre_topc @ sk_C @ 
% 0.47/0.64          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)),
% 0.47/0.64      inference('simpl_trail', [status(thm)], ['125', '129'])).
% 0.47/0.64  thf('134', plain,
% 0.47/0.64      ((v4_pre_topc @ 
% 0.47/0.64        (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.47/0.64         (sk_D @ sk_C @ sk_B @ 
% 0.47/0.64          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) @ 
% 0.47/0.64        sk_A)),
% 0.47/0.64      inference('clc', [status(thm)], ['132', '133'])).
% 0.47/0.64  thf('135', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((u1_struct_0 @ 
% 0.47/0.64            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.47/0.64            = (u1_struct_0 @ X0))
% 0.47/0.64          | ~ (l1_pre_topc @ X0))),
% 0.47/0.64      inference('clc', [status(thm)], ['62', '63'])).
% 0.47/0.64  thf('136', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((u1_struct_0 @ 
% 0.47/0.64            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.47/0.64            = (u1_struct_0 @ X0))
% 0.47/0.64          | ~ (l1_pre_topc @ X0))),
% 0.47/0.64      inference('clc', [status(thm)], ['62', '63'])).
% 0.47/0.64  thf('137', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (m1_subset_1 @ 
% 0.47/0.64          (k8_relset_1 @ 
% 0.47/0.64           (u1_struct_0 @ 
% 0.47/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64           (u1_struct_0 @ sk_B) @ sk_C @ X0) @ 
% 0.47/0.64          (k1_zfmisc_1 @ 
% 0.47/0.64           (u1_struct_0 @ 
% 0.47/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['98', '99'])).
% 0.47/0.64  thf('138', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((m1_subset_1 @ 
% 0.47/0.64           (k8_relset_1 @ 
% 0.47/0.64            (u1_struct_0 @ 
% 0.47/0.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64            (u1_struct_0 @ sk_B) @ sk_C @ X0) @ 
% 0.47/0.64           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.47/0.64          | ~ (l1_pre_topc @ sk_A))),
% 0.47/0.64      inference('sup+', [status(thm)], ['136', '137'])).
% 0.47/0.64  thf('139', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('140', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (m1_subset_1 @ 
% 0.47/0.64          (k8_relset_1 @ 
% 0.47/0.64           (u1_struct_0 @ 
% 0.47/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64           (u1_struct_0 @ sk_B) @ sk_C @ X0) @ 
% 0.47/0.64          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.64      inference('demod', [status(thm)], ['138', '139'])).
% 0.47/0.64  thf('141', plain,
% 0.47/0.64      (![X17 : $i, X18 : $i]:
% 0.47/0.64         (~ (v4_pre_topc @ X18 @ X17)
% 0.47/0.64          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.47/0.64          | (v4_pre_topc @ X18 @ 
% 0.47/0.64             (g1_pre_topc @ (u1_struct_0 @ X17) @ (u1_pre_topc @ X17)))
% 0.47/0.64          | ~ (l1_pre_topc @ X17)
% 0.47/0.64          | ~ (v2_pre_topc @ X17))),
% 0.47/0.64      inference('cnf', [status(esa)], [t61_pre_topc])).
% 0.47/0.64  thf('142', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v2_pre_topc @ sk_A)
% 0.47/0.64          | ~ (l1_pre_topc @ sk_A)
% 0.47/0.64          | (v4_pre_topc @ 
% 0.47/0.64             (k8_relset_1 @ 
% 0.47/0.64              (u1_struct_0 @ 
% 0.47/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64              (u1_struct_0 @ sk_B) @ sk_C @ X0) @ 
% 0.47/0.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.47/0.64          | ~ (v4_pre_topc @ 
% 0.47/0.64               (k8_relset_1 @ 
% 0.47/0.64                (u1_struct_0 @ 
% 0.47/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64                (u1_struct_0 @ sk_B) @ sk_C @ X0) @ 
% 0.47/0.64               sk_A))),
% 0.47/0.64      inference('sup-', [status(thm)], ['140', '141'])).
% 0.47/0.64  thf('143', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('144', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('145', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         ((v4_pre_topc @ 
% 0.47/0.64           (k8_relset_1 @ 
% 0.47/0.64            (u1_struct_0 @ 
% 0.47/0.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64            (u1_struct_0 @ sk_B) @ sk_C @ X0) @ 
% 0.47/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.47/0.64          | ~ (v4_pre_topc @ 
% 0.47/0.64               (k8_relset_1 @ 
% 0.47/0.64                (u1_struct_0 @ 
% 0.47/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64                (u1_struct_0 @ sk_B) @ sk_C @ X0) @ 
% 0.47/0.64               sk_A))),
% 0.47/0.64      inference('demod', [status(thm)], ['142', '143', '144'])).
% 0.47/0.64  thf('146', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v4_pre_topc @ 
% 0.47/0.64             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.64              sk_C @ X0) @ 
% 0.47/0.64             sk_A)
% 0.47/0.64          | ~ (l1_pre_topc @ sk_A)
% 0.47/0.64          | (v4_pre_topc @ 
% 0.47/0.64             (k8_relset_1 @ 
% 0.47/0.64              (u1_struct_0 @ 
% 0.47/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64              (u1_struct_0 @ sk_B) @ sk_C @ X0) @ 
% 0.47/0.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['135', '145'])).
% 0.47/0.64  thf('147', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('148', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v4_pre_topc @ 
% 0.47/0.64             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.64              sk_C @ X0) @ 
% 0.47/0.64             sk_A)
% 0.47/0.64          | (v4_pre_topc @ 
% 0.47/0.64             (k8_relset_1 @ 
% 0.47/0.64              (u1_struct_0 @ 
% 0.47/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64              (u1_struct_0 @ sk_B) @ sk_C @ X0) @ 
% 0.47/0.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 0.47/0.64      inference('demod', [status(thm)], ['146', '147'])).
% 0.47/0.64  thf('149', plain,
% 0.47/0.64      ((v4_pre_topc @ 
% 0.47/0.64        (k8_relset_1 @ 
% 0.47/0.64         (u1_struct_0 @ 
% 0.47/0.64          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64         (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.47/0.64         (sk_D @ sk_C @ sk_B @ 
% 0.47/0.64          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) @ 
% 0.47/0.64        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['134', '148'])).
% 0.47/0.64  thf('150', plain,
% 0.47/0.64      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.47/0.64         (~ (l1_pre_topc @ X5)
% 0.47/0.64          | ~ (v4_pre_topc @ 
% 0.47/0.64               (k8_relset_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5) @ X6 @ 
% 0.47/0.64                (sk_D @ X6 @ X5 @ X7)) @ 
% 0.47/0.64               X7)
% 0.47/0.64          | (v5_pre_topc @ X6 @ X7 @ X5)
% 0.47/0.64          | ~ (m1_subset_1 @ X6 @ 
% 0.47/0.64               (k1_zfmisc_1 @ 
% 0.47/0.64                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))))
% 0.47/0.64          | ~ (v1_funct_2 @ X6 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))
% 0.47/0.64          | ~ (v1_funct_1 @ X6)
% 0.47/0.64          | ~ (l1_pre_topc @ X7))),
% 0.47/0.64      inference('cnf', [status(esa)], [d12_pre_topc])).
% 0.47/0.64  thf('151', plain,
% 0.47/0.64      ((~ (l1_pre_topc @ 
% 0.47/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.47/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.47/0.64        | ~ (v1_funct_2 @ sk_C @ 
% 0.47/0.64             (u1_struct_0 @ 
% 0.47/0.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64             (u1_struct_0 @ sk_B))
% 0.47/0.64        | ~ (m1_subset_1 @ sk_C @ 
% 0.47/0.64             (k1_zfmisc_1 @ 
% 0.47/0.64              (k2_zfmisc_1 @ 
% 0.47/0.64               (u1_struct_0 @ 
% 0.47/0.64                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64               (u1_struct_0 @ sk_B))))
% 0.47/0.64        | (v5_pre_topc @ sk_C @ 
% 0.47/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)
% 0.47/0.64        | ~ (l1_pre_topc @ sk_B))),
% 0.47/0.64      inference('sup-', [status(thm)], ['149', '150'])).
% 0.47/0.64  thf('152', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('153', plain,
% 0.47/0.64      ((v1_funct_2 @ sk_C @ 
% 0.47/0.64        (u1_struct_0 @ 
% 0.47/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64        (u1_struct_0 @ sk_B))),
% 0.47/0.64      inference('demod', [status(thm)], ['10', '11'])).
% 0.47/0.64  thf('154', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_C @ 
% 0.47/0.64        (k1_zfmisc_1 @ 
% 0.47/0.64         (k2_zfmisc_1 @ 
% 0.47/0.64          (u1_struct_0 @ 
% 0.47/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.47/0.64          (u1_struct_0 @ sk_B))))),
% 0.47/0.64      inference('demod', [status(thm)], ['4', '5'])).
% 0.47/0.64  thf('155', plain, ((l1_pre_topc @ sk_B)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('156', plain,
% 0.47/0.64      ((~ (l1_pre_topc @ 
% 0.47/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.47/0.64        | (v5_pre_topc @ sk_C @ 
% 0.47/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))),
% 0.47/0.64      inference('demod', [status(thm)], ['151', '152', '153', '154', '155'])).
% 0.47/0.64  thf('157', plain,
% 0.47/0.64      (~ (v5_pre_topc @ sk_C @ 
% 0.47/0.64          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)),
% 0.47/0.64      inference('simpl_trail', [status(thm)], ['125', '129'])).
% 0.47/0.64  thf('158', plain,
% 0.47/0.64      (~ (l1_pre_topc @ 
% 0.47/0.64          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.47/0.64      inference('clc', [status(thm)], ['156', '157'])).
% 0.47/0.64  thf('159', plain, (~ (l1_pre_topc @ sk_A)),
% 0.47/0.64      inference('sup-', [status(thm)], ['2', '158'])).
% 0.47/0.64  thf('160', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('161', plain, ($false), inference('demod', [status(thm)], ['159', '160'])).
% 0.47/0.64  
% 0.47/0.64  % SZS output end Refutation
% 0.47/0.64  
% 0.47/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
