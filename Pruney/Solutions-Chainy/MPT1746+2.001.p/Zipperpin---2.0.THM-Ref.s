%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.g6woB40bOG

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:37 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 174 expanded)
%              Number of leaves         :   25 (  64 expanded)
%              Depth                    :   13
%              Number of atoms          :  964 (3659 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(t55_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( v2_pre_topc @ A )
        & ~ ( v2_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ( l1_pre_topc @ B )
            & ( v2_pre_topc @ B )
            & ~ ( v2_struct_0 @ B ) )
         => ! [C: $i] :
              ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( v1_funct_1 @ C ) )
             => ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) )
                  & ( v5_pre_topc @ C @ A @ B )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( v1_funct_1 @ C ) )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( r1_tmap_1 @ A @ B @ C @ D ) ) ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ D @ C @ B @ A )
    <=> ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
       => ( r1_tmap_1 @ A @ B @ C @ D ) ) ) )).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
    <=> ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
        & ( v5_pre_topc @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf(zf_stmt_4,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( zip_tseitin_0 @ C @ B @ A )
              <=> ! [D: $i] :
                    ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) ) ) )).

thf(zf_stmt_5,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v2_pre_topc @ B )
              & ( l1_pre_topc @ B ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( ( zip_tseitin_0 @ C @ B @ A )
                <=> ! [D: $i] :
                      ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[zf_stmt_4])).

thf('0',plain,(
    ! [X13: $i] :
      ( ( zip_tseitin_1 @ X13 @ sk_C @ sk_B @ sk_A )
      | ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('1',plain,
    ( ! [X13: $i] :
        ( zip_tseitin_1 @ X13 @ sk_C @ sk_B @ sk_A )
    | ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ! [X13: $i] :
        ( zip_tseitin_1 @ X13 @ sk_C @ sk_B @ sk_A )
   <= ! [X13: $i] :
        ( zip_tseitin_1 @ X13 @ sk_C @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(t49_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
             => ( ( v5_pre_topc @ C @ B @ A )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) )
                   => ( r1_tmap_1 @ B @ A @ C @ D ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X1 @ X0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ( v5_pre_topc @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t49_tmap_1])).

thf('5',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('8',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('9',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('11',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['5','6','7','8','9','10','11'])).

thf('13',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ( r1_tmap_1 @ X9 @ X10 @ X11 @ X8 )
      | ~ ( zip_tseitin_1 @ X8 @ X11 @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ~ ( zip_tseitin_1 @ ( sk_D @ sk_C @ sk_A @ sk_B ) @ X1 @ X0 @ sk_A )
      | ( r1_tmap_1 @ sk_A @ X0 @ X1 @ ( sk_D @ sk_C @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ ( sk_D @ sk_C @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X13: $i] :
        ( zip_tseitin_1 @ X13 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tmap_1 @ X0 @ X2 @ X1 @ ( sk_D @ X1 @ X0 @ X2 ) )
      | ( v5_pre_topc @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t49_tmap_1])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ ( sk_D @ sk_C @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('20',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('21',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('22',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('24',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ ( sk_D @ sk_C @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19','20','21','22','23','24'])).

thf('26',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_B ) )
   <= ! [X13: $i] :
        ( zip_tseitin_1 @ X13 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['15','25'])).

thf('27',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X13: $i] :
        ( zip_tseitin_1 @ X13 @ sk_C @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('29',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) )
   <= ! [X13: $i] :
        ( zip_tseitin_1 @ X13 @ sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('31',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ! [X13: $i] :
        ( zip_tseitin_1 @ X13 @ sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('33',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( zip_tseitin_0 @ X4 @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v5_pre_topc @ X4 @ X7 @ X5 )
      | ~ ( v1_funct_2 @ X4 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('34',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('36',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('37',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A )
   <= ! [X13: $i] :
        ( zip_tseitin_1 @ X13 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','37'])).

thf('39',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('40',plain,
    ( ~ ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A )
   <= ~ ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['39'])).

thf('41',plain,
    ( ~ ! [X13: $i] :
          ( zip_tseitin_1 @ X13 @ sk_C @ sk_B @ sk_A )
    | ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['39'])).

thf('43',plain,(
    ! [X8: $i,X10: $i,X11: $i,X12: $i] :
      ( ( zip_tseitin_1 @ X8 @ X11 @ X10 @ X12 )
      | ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('44',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
   <= ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['39'])).

thf('45',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A )
   <= ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('47',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v5_pre_topc @ X4 @ X6 @ X5 )
      | ~ ( zip_tseitin_0 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('48',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v5_pre_topc @ X1 @ X0 @ X2 )
      | ( r1_tmap_1 @ X0 @ X2 @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t49_tmap_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('53',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('54',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('55',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('57',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52','53','54','55','56','57'])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_B ) )
   <= ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['48','58'])).

thf('60',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
      & ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('62',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 ) )
   <= ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
      & ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('64',plain,
    ( ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1 )
   <= ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
      & ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X8: $i,X10: $i,X11: $i,X12: $i] :
      ( ( zip_tseitin_1 @ X8 @ X11 @ X10 @ X12 )
      | ~ ( r1_tmap_1 @ X12 @ X10 @ X11 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('66',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
   <= ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
      & ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
   <= ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['39'])).

thf('68',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','41','42','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.g6woB40bOG
% 0.15/0.35  % Computer   : n006.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 15:42:08 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 67 iterations in 0.035s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.22/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.50  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.22/0.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.22/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.50  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.22/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.50  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.22/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.50  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.22/0.50  thf(t55_tmap_1, conjecture,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( l1_pre_topc @ A ) & ( v2_pre_topc @ A ) & ( ~( v2_struct_0 @ A ) ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( ( l1_pre_topc @ B ) & ( v2_pre_topc @ B ) & 
% 0.22/0.50             ( ~( v2_struct_0 @ B ) ) ) =>
% 0.22/0.50           ( ![C:$i]:
% 0.22/0.50             ( ( ( m1_subset_1 @
% 0.22/0.50                   C @ 
% 0.22/0.50                   ( k1_zfmisc_1 @
% 0.22/0.50                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.22/0.50                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.50                 ( v1_funct_1 @ C ) ) =>
% 0.22/0.50               ( ( ( m1_subset_1 @
% 0.22/0.50                     C @ 
% 0.22/0.50                     ( k1_zfmisc_1 @
% 0.22/0.50                       ( k2_zfmisc_1 @
% 0.22/0.50                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.22/0.50                   ( v5_pre_topc @ C @ A @ B ) & 
% 0.22/0.50                   ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.50                   ( v1_funct_1 @ C ) ) <=>
% 0.22/0.50                 ( ![D:$i]:
% 0.22/0.50                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.50                     ( r1_tmap_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.22/0.50  thf(zf_stmt_1, axiom,
% 0.22/0.50    (![D:$i,C:$i,B:$i,A:$i]:
% 0.22/0.50     ( ( zip_tseitin_1 @ D @ C @ B @ A ) <=>
% 0.22/0.50       ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.50         ( r1_tmap_1 @ A @ B @ C @ D ) ) ))).
% 0.22/0.50  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.22/0.50  thf(zf_stmt_3, axiom,
% 0.22/0.50    (![C:$i,B:$i,A:$i]:
% 0.22/0.50     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 0.22/0.50       ( ( v1_funct_1 @ C ) & 
% 0.22/0.50         ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.50         ( v5_pre_topc @ C @ A @ B ) & 
% 0.22/0.50         ( m1_subset_1 @
% 0.22/0.50           C @ 
% 0.22/0.50           ( k1_zfmisc_1 @
% 0.22/0.50             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_4, conjecture,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.50             ( l1_pre_topc @ B ) ) =>
% 0.22/0.50           ( ![C:$i]:
% 0.22/0.50             ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.50                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.50                 ( m1_subset_1 @
% 0.22/0.50                   C @ 
% 0.22/0.50                   ( k1_zfmisc_1 @
% 0.22/0.50                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.50               ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 0.22/0.50                 ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_5, negated_conjecture,
% 0.22/0.50    (~( ![A:$i]:
% 0.22/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.50            ( l1_pre_topc @ A ) ) =>
% 0.22/0.50          ( ![B:$i]:
% 0.22/0.50            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.50                ( l1_pre_topc @ B ) ) =>
% 0.22/0.50              ( ![C:$i]:
% 0.22/0.50                ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.50                    ( v1_funct_2 @
% 0.22/0.50                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.50                    ( m1_subset_1 @
% 0.22/0.50                      C @ 
% 0.22/0.50                      ( k1_zfmisc_1 @
% 0.22/0.50                        ( k2_zfmisc_1 @
% 0.22/0.50                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.50                  ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 0.22/0.50                    ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [zf_stmt_4])).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      (![X13 : $i]:
% 0.22/0.50         ((zip_tseitin_1 @ X13 @ sk_C @ sk_B @ sk_A)
% 0.22/0.50          | (zip_tseitin_0 @ sk_C @ sk_B @ sk_A))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      ((![X13 : $i]: (zip_tseitin_1 @ X13 @ sk_C @ sk_B @ sk_A)) | 
% 0.22/0.50       ((zip_tseitin_0 @ sk_C @ sk_B @ sk_A))),
% 0.22/0.50      inference('split', [status(esa)], ['0'])).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      ((![X13 : $i]: (zip_tseitin_1 @ X13 @ sk_C @ sk_B @ sk_A))
% 0.22/0.50         <= ((![X13 : $i]: (zip_tseitin_1 @ X13 @ sk_C @ sk_B @ sk_A)))),
% 0.22/0.50      inference('split', [status(esa)], ['0'])).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ 
% 0.22/0.50        (k1_zfmisc_1 @ 
% 0.22/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.50  thf(t49_tmap_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.50             ( l1_pre_topc @ B ) ) =>
% 0.22/0.50           ( ![C:$i]:
% 0.22/0.50             ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.50                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.50                 ( m1_subset_1 @
% 0.22/0.50                   C @ 
% 0.22/0.50                   ( k1_zfmisc_1 @
% 0.22/0.50                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.22/0.50               ( ( v5_pre_topc @ C @ B @ A ) <=>
% 0.22/0.50                 ( ![D:$i]:
% 0.22/0.50                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.22/0.50                     ( r1_tmap_1 @ B @ A @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X0)
% 0.22/0.50          | ~ (v2_pre_topc @ X0)
% 0.22/0.50          | ~ (l1_pre_topc @ X0)
% 0.22/0.50          | (m1_subset_1 @ (sk_D @ X1 @ X0 @ X2) @ (u1_struct_0 @ X0))
% 0.22/0.50          | (v5_pre_topc @ X1 @ X0 @ X2)
% 0.22/0.50          | ~ (m1_subset_1 @ X1 @ 
% 0.22/0.50               (k1_zfmisc_1 @ 
% 0.22/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X2))))
% 0.22/0.50          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X2))
% 0.22/0.50          | ~ (v1_funct_1 @ X1)
% 0.22/0.50          | ~ (l1_pre_topc @ X2)
% 0.22/0.50          | ~ (v2_pre_topc @ X2)
% 0.22/0.50          | (v2_struct_0 @ X2))),
% 0.22/0.50      inference('cnf', [status(esa)], [t49_tmap_1])).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      (((v2_struct_0 @ sk_B)
% 0.22/0.50        | ~ (v2_pre_topc @ sk_B)
% 0.22/0.50        | ~ (l1_pre_topc @ sk_B)
% 0.22/0.50        | ~ (v1_funct_1 @ sk_C)
% 0.22/0.50        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.22/0.50        | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.22/0.50        | (m1_subset_1 @ (sk_D @ sk_C @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.22/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.50        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.50  thf('6', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.50  thf('7', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.50  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.50  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.50  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (((v2_struct_0 @ sk_B)
% 0.22/0.50        | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.22/0.50        | (m1_subset_1 @ (sk_D @ sk_C @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.22/0.50        | (v2_struct_0 @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['5', '6', '7', '8', '9', '10', '11'])).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.22/0.50          | (r1_tmap_1 @ X9 @ X10 @ X11 @ X8)
% 0.22/0.50          | ~ (zip_tseitin_1 @ X8 @ X11 @ X10 @ X9))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((v2_struct_0 @ sk_A)
% 0.22/0.50          | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.22/0.50          | (v2_struct_0 @ sk_B)
% 0.22/0.50          | ~ (zip_tseitin_1 @ (sk_D @ sk_C @ sk_A @ sk_B) @ X1 @ X0 @ sk_A)
% 0.22/0.50          | (r1_tmap_1 @ sk_A @ X0 @ X1 @ (sk_D @ sk_C @ sk_A @ sk_B)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      ((((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ (sk_D @ sk_C @ sk_A @ sk_B))
% 0.22/0.50         | (v2_struct_0 @ sk_B)
% 0.22/0.50         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.22/0.50         | (v2_struct_0 @ sk_A)))
% 0.22/0.50         <= ((![X13 : $i]: (zip_tseitin_1 @ X13 @ sk_C @ sk_B @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['2', '14'])).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ 
% 0.22/0.50        (k1_zfmisc_1 @ 
% 0.22/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X0)
% 0.22/0.50          | ~ (v2_pre_topc @ X0)
% 0.22/0.50          | ~ (l1_pre_topc @ X0)
% 0.22/0.50          | ~ (r1_tmap_1 @ X0 @ X2 @ X1 @ (sk_D @ X1 @ X0 @ X2))
% 0.22/0.50          | (v5_pre_topc @ X1 @ X0 @ X2)
% 0.22/0.50          | ~ (m1_subset_1 @ X1 @ 
% 0.22/0.50               (k1_zfmisc_1 @ 
% 0.22/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X2))))
% 0.22/0.50          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X2))
% 0.22/0.50          | ~ (v1_funct_1 @ X1)
% 0.22/0.50          | ~ (l1_pre_topc @ X2)
% 0.22/0.50          | ~ (v2_pre_topc @ X2)
% 0.22/0.50          | (v2_struct_0 @ X2))),
% 0.22/0.50      inference('cnf', [status(esa)], [t49_tmap_1])).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      (((v2_struct_0 @ sk_B)
% 0.22/0.50        | ~ (v2_pre_topc @ sk_B)
% 0.22/0.50        | ~ (l1_pre_topc @ sk_B)
% 0.22/0.50        | ~ (v1_funct_1 @ sk_C)
% 0.22/0.50        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.22/0.50        | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.22/0.50        | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ (sk_D @ sk_C @ sk_A @ sk_B))
% 0.22/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.50        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.50  thf('19', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.50  thf('20', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.50  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.50  thf('22', plain,
% 0.22/0.50      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.50  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.50  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.50  thf('25', plain,
% 0.22/0.50      (((v2_struct_0 @ sk_B)
% 0.22/0.50        | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.22/0.50        | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ (sk_D @ sk_C @ sk_A @ sk_B))
% 0.22/0.50        | (v2_struct_0 @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)],
% 0.22/0.50                ['18', '19', '20', '21', '22', '23', '24'])).
% 0.22/0.50  thf('26', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_A)
% 0.22/0.50         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.22/0.50         | (v2_struct_0 @ sk_B)
% 0.22/0.50         | (v2_struct_0 @ sk_A)
% 0.22/0.50         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.22/0.50         | (v2_struct_0 @ sk_B)))
% 0.22/0.50         <= ((![X13 : $i]: (zip_tseitin_1 @ X13 @ sk_C @ sk_B @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['15', '25'])).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_B)
% 0.22/0.50         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.22/0.50         | (v2_struct_0 @ sk_A)))
% 0.22/0.50         <= ((![X13 : $i]: (zip_tseitin_1 @ X13 @ sk_C @ sk_B @ sk_A)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['26'])).
% 0.22/0.50  thf('28', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.50  thf('29', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_A) | (v5_pre_topc @ sk_C @ sk_A @ sk_B)))
% 0.22/0.50         <= ((![X13 : $i]: (zip_tseitin_1 @ X13 @ sk_C @ sk_B @ sk_A)))),
% 0.22/0.50      inference('clc', [status(thm)], ['27', '28'])).
% 0.22/0.50  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.50  thf('31', plain,
% 0.22/0.50      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.22/0.50         <= ((![X13 : $i]: (zip_tseitin_1 @ X13 @ sk_C @ sk_B @ sk_A)))),
% 0.22/0.50      inference('clc', [status(thm)], ['29', '30'])).
% 0.22/0.50  thf('32', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ 
% 0.22/0.50        (k1_zfmisc_1 @ 
% 0.22/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.50  thf('33', plain,
% 0.22/0.50      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.22/0.50         ((zip_tseitin_0 @ X4 @ X5 @ X7)
% 0.22/0.50          | ~ (m1_subset_1 @ X4 @ 
% 0.22/0.50               (k1_zfmisc_1 @ 
% 0.22/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))))
% 0.22/0.50          | ~ (v5_pre_topc @ X4 @ X7 @ X5)
% 0.22/0.50          | ~ (v1_funct_2 @ X4 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X5))
% 0.22/0.50          | ~ (v1_funct_1 @ X4))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.50  thf('34', plain,
% 0.22/0.50      ((~ (v1_funct_1 @ sk_C)
% 0.22/0.50        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.22/0.50        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.22/0.50        | (zip_tseitin_0 @ sk_C @ sk_B @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.50  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.50  thf('36', plain,
% 0.22/0.50      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.50  thf('37', plain,
% 0.22/0.50      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.22/0.50        | (zip_tseitin_0 @ sk_C @ sk_B @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.22/0.50  thf('38', plain,
% 0.22/0.50      (((zip_tseitin_0 @ sk_C @ sk_B @ sk_A))
% 0.22/0.50         <= ((![X13 : $i]: (zip_tseitin_1 @ X13 @ sk_C @ sk_B @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['31', '37'])).
% 0.22/0.50  thf('39', plain,
% 0.22/0.50      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B @ sk_A)
% 0.22/0.50        | ~ (zip_tseitin_0 @ sk_C @ sk_B @ sk_A))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.50  thf('40', plain,
% 0.22/0.50      ((~ (zip_tseitin_0 @ sk_C @ sk_B @ sk_A))
% 0.22/0.50         <= (~ ((zip_tseitin_0 @ sk_C @ sk_B @ sk_A)))),
% 0.22/0.50      inference('split', [status(esa)], ['39'])).
% 0.22/0.50  thf('41', plain,
% 0.22/0.50      (~ (![X13 : $i]: (zip_tseitin_1 @ X13 @ sk_C @ sk_B @ sk_A)) | 
% 0.22/0.50       ((zip_tseitin_0 @ sk_C @ sk_B @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['38', '40'])).
% 0.22/0.50  thf('42', plain,
% 0.22/0.50      (~ ((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B @ sk_A)) | 
% 0.22/0.50       ~ ((zip_tseitin_0 @ sk_C @ sk_B @ sk_A))),
% 0.22/0.50      inference('split', [status(esa)], ['39'])).
% 0.22/0.50  thf('43', plain,
% 0.22/0.50      (![X8 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.50         ((zip_tseitin_1 @ X8 @ X11 @ X10 @ X12)
% 0.22/0.50          | (m1_subset_1 @ X8 @ (u1_struct_0 @ X12)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.50  thf('44', plain,
% 0.22/0.50      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B @ sk_A))
% 0.22/0.50         <= (~ ((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B @ sk_A)))),
% 0.22/0.50      inference('split', [status(esa)], ['39'])).
% 0.22/0.50  thf('45', plain,
% 0.22/0.50      (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.50         <= (~ ((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['43', '44'])).
% 0.22/0.50  thf('46', plain,
% 0.22/0.50      (((zip_tseitin_0 @ sk_C @ sk_B @ sk_A))
% 0.22/0.50         <= (((zip_tseitin_0 @ sk_C @ sk_B @ sk_A)))),
% 0.22/0.50      inference('split', [status(esa)], ['0'])).
% 0.22/0.50  thf('47', plain,
% 0.22/0.50      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.50         ((v5_pre_topc @ X4 @ X6 @ X5) | ~ (zip_tseitin_0 @ X4 @ X5 @ X6))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.50  thf('48', plain,
% 0.22/0.50      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.22/0.50         <= (((zip_tseitin_0 @ sk_C @ sk_B @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['46', '47'])).
% 0.22/0.50  thf('49', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ 
% 0.22/0.50        (k1_zfmisc_1 @ 
% 0.22/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.50  thf('50', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X0)
% 0.22/0.50          | ~ (v2_pre_topc @ X0)
% 0.22/0.50          | ~ (l1_pre_topc @ X0)
% 0.22/0.50          | ~ (v5_pre_topc @ X1 @ X0 @ X2)
% 0.22/0.50          | (r1_tmap_1 @ X0 @ X2 @ X1 @ X3)
% 0.22/0.50          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X0))
% 0.22/0.50          | ~ (m1_subset_1 @ X1 @ 
% 0.22/0.50               (k1_zfmisc_1 @ 
% 0.22/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X2))))
% 0.22/0.50          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X2))
% 0.22/0.50          | ~ (v1_funct_1 @ X1)
% 0.22/0.50          | ~ (l1_pre_topc @ X2)
% 0.22/0.50          | ~ (v2_pre_topc @ X2)
% 0.22/0.50          | (v2_struct_0 @ X2))),
% 0.22/0.50      inference('cnf', [status(esa)], [t49_tmap_1])).
% 0.22/0.50  thf('51', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((v2_struct_0 @ sk_B)
% 0.22/0.50          | ~ (v2_pre_topc @ sk_B)
% 0.22/0.50          | ~ (l1_pre_topc @ sk_B)
% 0.22/0.50          | ~ (v1_funct_1 @ sk_C)
% 0.22/0.50          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.22/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.50          | (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 0.22/0.50          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.22/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.50          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.50          | (v2_struct_0 @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['49', '50'])).
% 0.22/0.50  thf('52', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.50  thf('53', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.50  thf('54', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.50  thf('55', plain,
% 0.22/0.50      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.50  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.50  thf('57', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.50  thf('58', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((v2_struct_0 @ sk_B)
% 0.22/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.50          | (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 0.22/0.50          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.22/0.50          | (v2_struct_0 @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)],
% 0.22/0.50                ['51', '52', '53', '54', '55', '56', '57'])).
% 0.22/0.50  thf('59', plain,
% 0.22/0.50      ((![X0 : $i]:
% 0.22/0.50          ((v2_struct_0 @ sk_A)
% 0.22/0.50           | (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 0.22/0.50           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.50           | (v2_struct_0 @ sk_B)))
% 0.22/0.50         <= (((zip_tseitin_0 @ sk_C @ sk_B @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['48', '58'])).
% 0.22/0.50  thf('60', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_B)
% 0.22/0.50         | (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1)
% 0.22/0.50         | (v2_struct_0 @ sk_A)))
% 0.22/0.50         <= (~ ((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B @ sk_A)) & 
% 0.22/0.50             ((zip_tseitin_0 @ sk_C @ sk_B @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['45', '59'])).
% 0.22/0.50  thf('61', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.50  thf('62', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_A) | (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1)))
% 0.22/0.50         <= (~ ((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B @ sk_A)) & 
% 0.22/0.50             ((zip_tseitin_0 @ sk_C @ sk_B @ sk_A)))),
% 0.22/0.50      inference('clc', [status(thm)], ['60', '61'])).
% 0.22/0.50  thf('63', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.50  thf('64', plain,
% 0.22/0.50      (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D_1))
% 0.22/0.50         <= (~ ((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B @ sk_A)) & 
% 0.22/0.50             ((zip_tseitin_0 @ sk_C @ sk_B @ sk_A)))),
% 0.22/0.50      inference('clc', [status(thm)], ['62', '63'])).
% 0.22/0.50  thf('65', plain,
% 0.22/0.50      (![X8 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.50         ((zip_tseitin_1 @ X8 @ X11 @ X10 @ X12)
% 0.22/0.50          | ~ (r1_tmap_1 @ X12 @ X10 @ X11 @ X8))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.50  thf('66', plain,
% 0.22/0.50      (((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B @ sk_A))
% 0.22/0.50         <= (~ ((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B @ sk_A)) & 
% 0.22/0.50             ((zip_tseitin_0 @ sk_C @ sk_B @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['64', '65'])).
% 0.22/0.50  thf('67', plain,
% 0.22/0.50      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B @ sk_A))
% 0.22/0.50         <= (~ ((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B @ sk_A)))),
% 0.22/0.50      inference('split', [status(esa)], ['39'])).
% 0.22/0.50  thf('68', plain,
% 0.22/0.50      (((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B @ sk_A)) | 
% 0.22/0.50       ~ ((zip_tseitin_0 @ sk_C @ sk_B @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['66', '67'])).
% 0.22/0.50  thf('69', plain, ($false),
% 0.22/0.50      inference('sat_resolution*', [status(thm)], ['1', '41', '42', '68'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
