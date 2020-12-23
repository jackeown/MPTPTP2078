%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1132+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.45lcfAPX9Q

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:06 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :  177 (1226 expanded)
%              Number of leaves         :   26 ( 361 expanded)
%              Depth                    :   28
%              Number of atoms          : 2414 (42059 expanded)
%              Number of equality atoms :   13 ( 580 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t63_pre_topc,conjecture,(
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
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )
                 => ( ( C = D )
                   => ( ( v5_pre_topc @ C @ A @ B )
                    <=> ( v5_pre_topc @ D @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) ) ) )).

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
                      & ( v1_funct_2 @ D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )
                   => ( ( C = D )
                     => ( ( v5_pre_topc @ C @ A @ B )
                      <=> ( v5_pre_topc @ D @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t63_pre_topc])).

thf('0',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A_1 @ sk_B_1 )
   <= ~ ( v5_pre_topc @ sk_C @ sk_A_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A_1 @ sk_B_1 )
    | ~ ( v5_pre_topc @ sk_D_1 @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X11: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X11 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(dt_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) )
        & ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

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

thf('10',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( sk_D @ X2 @ X1 @ X3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( v5_pre_topc @ X2 @ X3 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('11',plain,
    ( ~ ( l1_pre_topc @ sk_A_1 )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) @ sk_A_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) @ sk_A_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['11','12','13','16'])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) @ sk_A_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) @ sk_A_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t61_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v4_pre_topc @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
        <=> ( ( v4_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v4_pre_topc @ X25 @ ( g1_pre_topc @ ( u1_struct_0 @ X26 ) @ ( u1_pre_topc @ X26 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X26 ) @ ( u1_pre_topc @ X26 ) ) ) ) )
      | ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t61_pre_topc])).

thf('22',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v2_pre_topc @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) @ sk_A_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) @ sk_A_1 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) @ sk_A_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) @ sk_A_1 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('28',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ( v4_pre_topc @ ( sk_D @ X2 @ X1 @ X3 ) @ X1 )
      | ( v5_pre_topc @ X2 @ X3 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('29',plain,
    ( ~ ( l1_pre_topc @ sk_A_1 )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) @ sk_A_1 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('33',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) @ sk_A_1 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('34',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) @ sk_A_1 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['26','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) @ sk_A_1 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) @ sk_A_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['25','36'])).

thf('38',plain,
    ( ( v5_pre_topc @ sk_D_1 @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A_1 @ sk_B_1 )
   <= ( v5_pre_topc @ sk_C @ sk_A_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ~ ( v5_pre_topc @ X2 @ X3 @ X1 )
      | ~ ( v4_pre_topc @ X4 @ X1 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) @ X2 @ X4 ) @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A_1 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ X0 ) @ sk_A_1 )
      | ~ ( v4_pre_topc @ X0 @ sk_B_1 )
      | ~ ( v5_pre_topc @ sk_C @ sk_A_1 @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A_1 ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ X0 ) @ sk_A_1 )
      | ~ ( v4_pre_topc @ X0 @ sk_B_1 )
      | ~ ( v5_pre_topc @ sk_C @ sk_A_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['42','43','44','45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('49',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( ( k8_relset_1 @ X14 @ X15 @ X13 @ X16 )
        = ( k10_relat_1 @ X13 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A_1 )
      | ~ ( v4_pre_topc @ X0 @ sk_B_1 )
      | ~ ( v5_pre_topc @ sk_C @ sk_A_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['47','50'])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ~ ( v4_pre_topc @ X0 @ sk_B_1 )
        | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A_1 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ) )
   <= ( v5_pre_topc @ sk_C @ sk_A_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['39','51'])).

thf('53',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) @ sk_A_1 ) ) @ sk_A_1 )
      | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) @ sk_A_1 ) @ sk_B_1 ) )
   <= ( v5_pre_topc @ sk_C @ sk_A_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['37','52'])).

thf('54',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) @ sk_A_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('55',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v4_pre_topc @ X25 @ ( g1_pre_topc @ ( u1_struct_0 @ X26 ) @ ( u1_pre_topc @ X26 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X26 ) @ ( u1_pre_topc @ X26 ) ) ) ) )
      | ( v4_pre_topc @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t61_pre_topc])).

thf('56',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v2_pre_topc @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) @ sk_A_1 ) @ sk_B_1 )
    | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) @ sk_A_1 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) @ sk_A_1 ) @ sk_B_1 )
    | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) @ sk_A_1 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) @ sk_A_1 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('61',plain,
    ( ( v4_pre_topc @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) @ sk_A_1 ) @ sk_B_1 )
    | ( v5_pre_topc @ sk_C @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) @ sk_A_1 ) ) @ sk_A_1 )
      | ( v5_pre_topc @ sk_C @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( v5_pre_topc @ sk_C @ sk_A_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['53','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('64',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( ( k8_relset_1 @ X14 @ X15 @ X13 @ X16 )
        = ( k10_relat_1 @ X13 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) @ X2 @ ( sk_D @ X2 @ X1 @ X3 ) ) @ X3 )
      | ( v5_pre_topc @ X2 @ X3 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('67',plain,
    ( ~ ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) @ sk_A_1 ) ) @ sk_A_1 )
    | ~ ( l1_pre_topc @ sk_A_1 )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('72',plain,
    ( ~ ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) @ sk_A_1 ) ) @ sk_A_1 )
    | ( v5_pre_topc @ sk_C @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['67','68','69','70','71'])).

thf('73',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( v5_pre_topc @ sk_C @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( v5_pre_topc @ sk_C @ sk_A_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['62','72'])).

thf('74',plain,
    ( ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( v5_pre_topc @ sk_C @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( v5_pre_topc @ sk_C @ sk_A_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ( ~ ( l1_pre_topc @ sk_B_1 )
      | ( v5_pre_topc @ sk_C @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( v5_pre_topc @ sk_C @ sk_A_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['5','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ( v5_pre_topc @ sk_C @ sk_A_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ~ ( v5_pre_topc @ sk_D_1 @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('79',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ~ ( v5_pre_topc @ sk_D_1 @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( v5_pre_topc @ sk_D_1 @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A_1 @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['2','81'])).

thf('83',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A_1 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('85',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) @ X2 @ ( sk_D @ X2 @ X1 @ X3 ) ) @ X3 )
      | ( v5_pre_topc @ X2 @ X3 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('86',plain,
    ( ~ ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B_1 @ sk_A_1 ) ) @ sk_A_1 )
    | ~ ( l1_pre_topc @ sk_A_1 )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A_1 @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A_1 ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ~ ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B_1 @ sk_A_1 ) ) @ sk_A_1 )
    | ( v5_pre_topc @ sk_C @ sk_A_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['86','87','88','89','90','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( sk_D @ X2 @ X1 @ X3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( v5_pre_topc @ X2 @ X3 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('95',plain,
    ( ~ ( l1_pre_topc @ sk_A_1 )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v5_pre_topc @ sk_C @ sk_A_1 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B_1 @ sk_A_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A_1 ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A_1 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B_1 @ sk_A_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['95','96','97','98','99'])).

thf('101',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v4_pre_topc @ X27 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( v4_pre_topc @ X27 @ ( g1_pre_topc @ ( u1_struct_0 @ X26 ) @ ( u1_pre_topc @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t61_pre_topc])).

thf('102',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A_1 @ sk_B_1 )
    | ~ ( v2_pre_topc @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B_1 @ sk_A_1 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B_1 @ sk_A_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A_1 @ sk_B_1 )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B_1 @ sk_A_1 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B_1 @ sk_A_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ( v4_pre_topc @ ( sk_D @ X2 @ X1 @ X3 ) @ X1 )
      | ( v5_pre_topc @ X2 @ X3 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('108',plain,
    ( ~ ( l1_pre_topc @ sk_A_1 )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v5_pre_topc @ sk_C @ sk_A_1 @ sk_B_1 )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B_1 @ sk_A_1 ) @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A_1 ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A_1 @ sk_B_1 )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B_1 @ sk_A_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['108','109','110','111','112'])).

thf('114',plain,
    ( ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B_1 @ sk_A_1 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['105','113'])).

thf('115',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A_1 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B_1 @ sk_A_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['95','96','97','98','99'])).

thf('116',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v4_pre_topc @ X27 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X26 ) @ ( u1_pre_topc @ X26 ) ) ) ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t61_pre_topc])).

thf('117',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A_1 @ sk_B_1 )
    | ~ ( v2_pre_topc @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B_1 @ sk_A_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) )
    | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B_1 @ sk_A_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A_1 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B_1 @ sk_A_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) )
    | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B_1 @ sk_A_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A_1 @ sk_B_1 )
    | ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B_1 @ sk_A_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['108','109','110','111','112'])).

thf('122',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B_1 @ sk_A_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('124',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('125',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ~ ( v5_pre_topc @ X2 @ X3 @ X1 )
      | ~ ( v4_pre_topc @ X4 @ X1 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) @ X2 @ X4 ) @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A_1 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) @ sk_C @ X0 ) @ sk_A_1 )
      | ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( v5_pre_topc @ sk_C @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) @ sk_C @ X0 ) @ sk_A_1 )
      | ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( v5_pre_topc @ sk_C @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['126','127','128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A_1 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('132',plain,
    ( ( v5_pre_topc @ sk_D_1 @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['38'])).

thf('133',plain,(
    sk_C = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ( v5_pre_topc @ sk_D_1 @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( v5_pre_topc @ sk_D_1 @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['38'])).

thf('136',plain,(
    v5_pre_topc @ sk_D_1 @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','81','135'])).

thf('137',plain,(
    v5_pre_topc @ sk_C @ sk_A_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference(simpl_trail,[status(thm)],['134','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) )
      | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A_1 )
      | ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['130','131','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['123','138'])).

thf('140',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A_1 @ sk_B_1 )
    | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B_1 @ sk_A_1 ) ) @ sk_A_1 )
    | ~ ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B_1 @ sk_A_1 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['122','141'])).

thf('143',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A_1 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','82'])).

thf('144',plain,
    ( ~ ( v4_pre_topc @ ( sk_D @ sk_C @ sk_B_1 @ sk_A_1 ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B_1 @ sk_A_1 ) ) @ sk_A_1 ) ),
    inference(clc,[status(thm)],['142','143'])).

thf('145',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A_1 @ sk_B_1 )
    | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B_1 @ sk_A_1 ) ) @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['114','144'])).

thf('146',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A_1 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','82'])).

thf('147',plain,(
    v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( sk_D @ sk_C @ sk_B_1 @ sk_A_1 ) ) @ sk_A_1 ),
    inference(clc,[status(thm)],['145','146'])).

thf('148',plain,(
    v5_pre_topc @ sk_C @ sk_A_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['92','147'])).

thf('149',plain,(
    $false ),
    inference(demod,[status(thm)],['83','148'])).


%------------------------------------------------------------------------------
