%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5gdauBwLWa

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:37 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  184 (1170 expanded)
%              Number of leaves         :   43 ( 356 expanded)
%              Depth                    :   29
%              Number of atoms          : 1630 (28650 expanded)
%              Number of equality atoms :   59 ( 708 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t57_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( v2_pre_topc @ C )
                & ( l1_pre_topc @ C ) )
             => ( ( ( ( u1_struct_0 @ A )
                    = ( u1_struct_0 @ B ) )
                  & ( r1_tarski @ ( u1_pre_topc @ B ) @ ( u1_pre_topc @ A ) ) )
               => ! [D: $i] :
                    ( ( ( v1_funct_1 @ D )
                      & ( v1_funct_2 @ D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) )
                      & ( v5_pre_topc @ D @ B @ C )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) )
                   => ( ( v1_funct_1 @ D )
                      & ( v1_funct_2 @ D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) )
                      & ( v5_pre_topc @ D @ A @ C )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v2_pre_topc @ B )
              & ( l1_pre_topc @ B ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( v2_pre_topc @ C )
                  & ( l1_pre_topc @ C ) )
               => ( ( ( ( u1_struct_0 @ A )
                      = ( u1_struct_0 @ B ) )
                    & ( r1_tarski @ ( u1_pre_topc @ B ) @ ( u1_pre_topc @ A ) ) )
                 => ! [D: $i] :
                      ( ( ( v1_funct_1 @ D )
                        & ( v1_funct_2 @ D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) )
                        & ( v5_pre_topc @ D @ B @ C )
                        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) )
                     => ( ( v1_funct_1 @ D )
                        & ( v1_funct_2 @ D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) )
                        & ( v5_pre_topc @ D @ A @ C )
                        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t57_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( v1_funct_1 @ C ) )
             => ( ( ( ( k2_struct_0 @ B )
                    = k1_xboole_0 )
                 => ( ( k2_struct_0 @ A )
                    = k1_xboole_0 ) )
               => ( ( v5_pre_topc @ C @ A @ B )
                <=> ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ( ( v3_pre_topc @ D @ B )
                       => ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ A ) ) ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( ( k2_struct_0 @ B )
          = k1_xboole_0 )
       => ( ( k2_struct_0 @ A )
          = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 )
      | ( ( k2_struct_0 @ X13 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('5',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('6',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('8',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('9',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['3','10'])).

thf('12',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('13',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('14',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('17',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['11','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['2','19'])).

thf('21',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['11','18'])).

thf(zf_stmt_2,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v5_pre_topc @ C @ A @ B )
      <=> ! [D: $i] :
            ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ D @ C @ B @ A )
    <=> ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
       => ( ( v3_pre_topc @ D @ B )
         => ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ A ) ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( zip_tseitin_0 @ B @ A )
               => ( zip_tseitin_2 @ C @ B @ A ) ) ) ) ) )).

thf('22',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_2 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ( zip_tseitin_2 @ X1 @ X0 @ sk_B )
      | ~ ( zip_tseitin_0 @ X0 @ sk_B )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['11','18'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ( zip_tseitin_2 @ X1 @ X0 @ sk_B )
      | ~ ( zip_tseitin_0 @ X0 @ sk_B )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ~ ( zip_tseitin_0 @ sk_C_1 @ sk_B )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_C_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_D_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('30',plain,(
    v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( v1_funct_2 @ sk_D_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('35',plain,(
    v1_funct_2 @ sk_D_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ~ ( zip_tseitin_0 @ sk_C_1 @ sk_B )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['27','28','35','36'])).

thf('38',plain,
    ( ( ( k2_struct_0 @ sk_C_1 )
      = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','37'])).

thf('39',plain,(
    v5_pre_topc @ sk_D_1 @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( v5_pre_topc @ X22 @ X20 @ X21 )
      | ( zip_tseitin_1 @ X23 @ X22 @ X21 @ X20 )
      | ~ ( zip_tseitin_2 @ X22 @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ sk_D_1 @ sk_C_1 @ sk_B )
      | ( zip_tseitin_1 @ X0 @ sk_D_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ sk_C_1 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ X0 @ sk_D_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 )
      | ( ( k2_struct_0 @ X13 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('44',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['2','19'])).

thf('45',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('46',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_2 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ( zip_tseitin_2 @ X2 @ X1 @ X0 )
      | ~ ( zip_tseitin_0 @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ~ ( zip_tseitin_0 @ sk_C_1 @ sk_A )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_C_1 @ sk_A )
    | ~ ( v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('51',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('52',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    v1_funct_2 @ sk_D_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('54',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('57',plain,
    ( ~ ( zip_tseitin_0 @ sk_C_1 @ sk_A )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49','52','53','54','55','56'])).

thf('58',plain,
    ( ( ( k2_struct_0 @ sk_C_1 )
      = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','57'])).

thf('59',plain,(
    ! [X15: $i,X16: $i,X18: $i,X19: $i] :
      ( ( zip_tseitin_1 @ X15 @ X18 @ X16 @ X19 )
      | ( v3_pre_topc @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('60',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D @ X20 @ X21 @ X22 ) @ X22 @ X21 @ X20 )
      | ( v5_pre_topc @ X22 @ X20 @ X21 )
      | ~ ( zip_tseitin_2 @ X22 @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v3_pre_topc @ ( sk_D @ X0 @ X1 @ X2 ) @ X1 )
      | ~ ( zip_tseitin_2 @ X2 @ X1 @ X0 )
      | ( v5_pre_topc @ X2 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k2_struct_0 @ sk_C_1 )
      = k1_xboole_0 )
    | ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1 )
    | ( v3_pre_topc @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,
    ( ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) )
    | ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1 )
   <= ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['63'])).

thf('65',plain,(
    v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('66',plain,
    ( ~ ( v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ~ ( v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['63'])).

thf('67',plain,(
    v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ~ ( v1_funct_1 @ sk_D_1 )
   <= ~ ( v1_funct_1 @ sk_D_1 ) ),
    inference(split,[status(esa)],['63'])).

thf('70',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['2','19'])).

thf('72',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('73',plain,
    ( ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) ) ) )
   <= ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) ) ) ) ),
    inference(split,[status(esa)],['63'])).

thf('74',plain,
    ( ( ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) ) ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('76',plain,
    ( ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) ) ) )
   <= ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['71','76'])).

thf('78',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) ) ) )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['63'])).

thf('79',plain,(
    ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['67','70','77','78'])).

thf('80',plain,(
    ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['64','79'])).

thf('81',plain,
    ( ( v3_pre_topc @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_C_1 )
    | ( ( k2_struct_0 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['62','80'])).

thf('82',plain,
    ( ( ( k2_struct_0 @ sk_C_1 )
      = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','57'])).

thf('83',plain,(
    ! [X15: $i,X16: $i,X18: $i,X19: $i] :
      ( ( zip_tseitin_1 @ X15 @ X18 @ X16 @ X19 )
      | ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('84',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D @ X20 @ X21 @ X22 ) @ X22 @ X21 @ X20 )
      | ( v5_pre_topc @ X22 @ X20 @ X21 )
      | ~ ( zip_tseitin_2 @ X22 @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X0 @ X1 @ X2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( zip_tseitin_2 @ X2 @ X1 @ X0 )
      | ( v5_pre_topc @ X2 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( k2_struct_0 @ sk_C_1 )
      = k1_xboole_0 )
    | ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,(
    ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['64','79'])).

thf('88',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( ( k2_struct_0 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) @ X18 @ X15 ) @ X17 )
      | ~ ( v3_pre_topc @ X15 @ X16 )
      | ~ ( zip_tseitin_1 @ X15 @ X18 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_struct_0 @ sk_C_1 )
        = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) @ X1 @ sk_C_1 @ X0 )
      | ~ ( v3_pre_topc @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_C_1 )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_C_1 ) @ X1 @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_struct_0 @ sk_C_1 )
        = k1_xboole_0 )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_C_1 ) @ X1 @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) ) @ X0 )
      | ~ ( zip_tseitin_1 @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) @ X1 @ sk_C_1 @ X0 )
      | ( ( k2_struct_0 @ sk_C_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['81','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) @ X1 @ sk_C_1 @ X0 )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_C_1 ) @ X1 @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) ) @ X0 )
      | ( ( k2_struct_0 @ sk_C_1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ( ( k2_struct_0 @ sk_C_1 )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_C_1 )
      = k1_xboole_0 )
    | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['42','92'])).

thf('94',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['11','18'])).

thf('95',plain,
    ( ( ( k2_struct_0 @ sk_C_1 )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_C_1 )
      = k1_xboole_0 )
    | ( v3_pre_topc @ ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( v3_pre_topc @ ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) ) @ sk_B )
    | ( ( k2_struct_0 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['2','19'])).

thf(dt_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('98',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) )
      | ( m1_subset_1 @ ( k8_relset_1 @ X5 @ X6 @ X4 @ X7 ) @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relset_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['11','18'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('101',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v3_pre_topc @ X9 @ X10 )
      | ( r2_hidden @ X9 @ ( u1_pre_topc @ X10 ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B ) )
      | ~ ( v3_pre_topc @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B ) )
      | ~ ( v3_pre_topc @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 @ X0 ) @ sk_B )
      | ( r2_hidden @ ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 @ X0 ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['99','104'])).

thf('106',plain,
    ( ( ( k2_struct_0 @ sk_C_1 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['96','105'])).

thf('107',plain,(
    r1_tarski @ ( u1_pre_topc @ sk_B ) @ ( u1_pre_topc @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( ( k2_struct_0 @ sk_C_1 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['106','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('112',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('113',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( r2_hidden @ X9 @ ( u1_pre_topc @ X10 ) )
      | ( v3_pre_topc @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 @ X0 ) @ ( u1_pre_topc @ sk_A ) )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['111','116'])).

thf('118',plain,
    ( ( ( k2_struct_0 @ sk_C_1 )
      = k1_xboole_0 )
    | ( v3_pre_topc @ ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) @ sk_D_1 @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['110','117'])).

thf('119',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('120',plain,(
    ! [X15: $i,X16: $i,X18: $i,X19: $i] :
      ( ( zip_tseitin_1 @ X15 @ X18 @ X16 @ X19 )
      | ~ ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X16 ) @ X18 @ X15 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_pre_topc @ ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ X2 ) @ X1 @ X0 ) @ sk_A )
      | ( zip_tseitin_1 @ X0 @ X1 @ X2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( ( k2_struct_0 @ sk_C_1 )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ ( sk_D @ sk_A @ sk_C_1 @ sk_D_1 ) @ sk_D_1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['118','121'])).

thf('123',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D @ X20 @ X21 @ X22 ) @ X22 @ X21 @ X20 )
      | ( v5_pre_topc @ X22 @ X20 @ X21 )
      | ~ ( zip_tseitin_2 @ X22 @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('124',plain,
    ( ( ( k2_struct_0 @ sk_C_1 )
      = k1_xboole_0 )
    | ~ ( zip_tseitin_2 @ sk_D_1 @ sk_C_1 @ sk_A )
    | ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ( ( k2_struct_0 @ sk_C_1 )
      = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','57'])).

thf('126',plain,
    ( ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1 )
    | ( ( k2_struct_0 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,(
    ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['64','79'])).

thf('128',plain,
    ( ( k2_struct_0 @ sk_C_1 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('130',plain,(
    ! [X12: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['128','132'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('134',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('135',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('137',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    v2_struct_0 @ sk_C_1 ),
    inference(demod,[status(thm)],['133','134','137'])).

thf('139',plain,(
    $false ),
    inference(demod,[status(thm)],['0','138'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5gdauBwLWa
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:21:12 EST 2020
% 0.21/0.34  % CPUTime    : 
% 0.21/0.34  % Running portfolio for 600 s
% 0.21/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.42/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.59  % Solved by: fo/fo7.sh
% 0.42/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.59  % done 269 iterations in 0.136s
% 0.42/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.59  % SZS output start Refutation
% 0.42/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.59  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.42/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.59  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.42/0.59  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.42/0.59  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.42/0.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.42/0.59  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.42/0.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.42/0.59  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.42/0.59  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.42/0.59  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.42/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.42/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.59  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.42/0.59  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.42/0.59  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.42/0.59  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.42/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.42/0.59  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.42/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.42/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.42/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.42/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.59  thf(t57_tmap_1, conjecture,
% 0.42/0.59    (![A:$i]:
% 0.42/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.59       ( ![B:$i]:
% 0.42/0.59         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.42/0.59             ( l1_pre_topc @ B ) ) =>
% 0.42/0.59           ( ![C:$i]:
% 0.42/0.59             ( ( ( ~( v2_struct_0 @ C ) ) & ( v2_pre_topc @ C ) & 
% 0.42/0.59                 ( l1_pre_topc @ C ) ) =>
% 0.42/0.59               ( ( ( ( u1_struct_0 @ A ) = ( u1_struct_0 @ B ) ) & 
% 0.42/0.59                   ( r1_tarski @ ( u1_pre_topc @ B ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.42/0.59                 ( ![D:$i]:
% 0.42/0.59                   ( ( ( v1_funct_1 @ D ) & 
% 0.42/0.59                       ( v1_funct_2 @
% 0.42/0.59                         D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) & 
% 0.42/0.59                       ( v5_pre_topc @ D @ B @ C ) & 
% 0.42/0.59                       ( m1_subset_1 @
% 0.42/0.59                         D @ 
% 0.42/0.59                         ( k1_zfmisc_1 @
% 0.42/0.59                           ( k2_zfmisc_1 @
% 0.42/0.59                             ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) =>
% 0.42/0.59                     ( ( v1_funct_1 @ D ) & 
% 0.42/0.59                       ( v1_funct_2 @
% 0.42/0.59                         D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) ) & 
% 0.42/0.59                       ( v5_pre_topc @ D @ A @ C ) & 
% 0.42/0.59                       ( m1_subset_1 @
% 0.42/0.59                         D @ 
% 0.42/0.59                         ( k1_zfmisc_1 @
% 0.42/0.59                           ( k2_zfmisc_1 @
% 0.42/0.59                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.42/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.59    (~( ![A:$i]:
% 0.42/0.59        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.42/0.59            ( l1_pre_topc @ A ) ) =>
% 0.42/0.59          ( ![B:$i]:
% 0.42/0.59            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.42/0.59                ( l1_pre_topc @ B ) ) =>
% 0.42/0.59              ( ![C:$i]:
% 0.42/0.59                ( ( ( ~( v2_struct_0 @ C ) ) & ( v2_pre_topc @ C ) & 
% 0.42/0.59                    ( l1_pre_topc @ C ) ) =>
% 0.42/0.59                  ( ( ( ( u1_struct_0 @ A ) = ( u1_struct_0 @ B ) ) & 
% 0.42/0.59                      ( r1_tarski @ ( u1_pre_topc @ B ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.42/0.59                    ( ![D:$i]:
% 0.42/0.59                      ( ( ( v1_funct_1 @ D ) & 
% 0.42/0.59                          ( v1_funct_2 @
% 0.42/0.59                            D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) & 
% 0.42/0.59                          ( v5_pre_topc @ D @ B @ C ) & 
% 0.42/0.59                          ( m1_subset_1 @
% 0.42/0.59                            D @ 
% 0.42/0.59                            ( k1_zfmisc_1 @
% 0.42/0.59                              ( k2_zfmisc_1 @
% 0.42/0.59                                ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) =>
% 0.42/0.59                        ( ( v1_funct_1 @ D ) & 
% 0.42/0.59                          ( v1_funct_2 @
% 0.42/0.59                            D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) ) & 
% 0.42/0.59                          ( v5_pre_topc @ D @ A @ C ) & 
% 0.42/0.59                          ( m1_subset_1 @
% 0.42/0.59                            D @ 
% 0.42/0.59                            ( k1_zfmisc_1 @
% 0.42/0.59                              ( k2_zfmisc_1 @
% 0.42/0.59                                ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.42/0.59    inference('cnf.neg', [status(esa)], [t57_tmap_1])).
% 0.42/0.59  thf('0', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf(t55_tops_2, axiom,
% 0.42/0.59    (![A:$i]:
% 0.42/0.59     ( ( l1_pre_topc @ A ) =>
% 0.42/0.59       ( ![B:$i]:
% 0.42/0.59         ( ( l1_pre_topc @ B ) =>
% 0.42/0.59           ( ![C:$i]:
% 0.42/0.59             ( ( ( m1_subset_1 @
% 0.42/0.59                   C @ 
% 0.42/0.59                   ( k1_zfmisc_1 @
% 0.42/0.59                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.42/0.59                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.42/0.59                 ( v1_funct_1 @ C ) ) =>
% 0.42/0.59               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.42/0.59                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.59                 ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.42/0.59                   ( ![D:$i]:
% 0.42/0.59                     ( ( m1_subset_1 @
% 0.42/0.59                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.42/0.59                       ( ( v3_pre_topc @ D @ B ) =>
% 0.42/0.59                         ( v3_pre_topc @
% 0.42/0.59                           ( k8_relset_1 @
% 0.42/0.59                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.42/0.59                           A ) ) ) ) ) ) ) ) ) ) ))).
% 0.42/0.59  thf(zf_stmt_1, axiom,
% 0.42/0.59    (![B:$i,A:$i]:
% 0.42/0.59     ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.42/0.59         ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.59       ( zip_tseitin_0 @ B @ A ) ))).
% 0.42/0.59  thf('1', plain,
% 0.42/0.59      (![X13 : $i, X14 : $i]:
% 0.42/0.59         ((zip_tseitin_0 @ X13 @ X14) | ((k2_struct_0 @ X13) = (k1_xboole_0)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.59  thf('2', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_D_1 @ 
% 0.42/0.59        (k1_zfmisc_1 @ 
% 0.42/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('3', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('4', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf(d3_struct_0, axiom,
% 0.42/0.59    (![A:$i]:
% 0.42/0.59     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.42/0.59  thf('5', plain,
% 0.42/0.59      (![X8 : $i]:
% 0.42/0.59         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.42/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.59  thf('6', plain,
% 0.42/0.59      ((((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_B))),
% 0.42/0.59      inference('sup+', [status(thm)], ['4', '5'])).
% 0.42/0.59  thf('7', plain, ((l1_pre_topc @ sk_B)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf(dt_l1_pre_topc, axiom,
% 0.42/0.59    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.42/0.59  thf('8', plain, (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.42/0.59      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.42/0.59  thf('9', plain, ((l1_struct_0 @ sk_B)),
% 0.42/0.59      inference('sup-', [status(thm)], ['7', '8'])).
% 0.42/0.59  thf('10', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.42/0.59      inference('demod', [status(thm)], ['6', '9'])).
% 0.42/0.59  thf('11', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B))),
% 0.42/0.59      inference('demod', [status(thm)], ['3', '10'])).
% 0.42/0.59  thf('12', plain,
% 0.42/0.59      (![X8 : $i]:
% 0.42/0.59         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.42/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.59  thf('13', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.42/0.59      inference('demod', [status(thm)], ['6', '9'])).
% 0.42/0.59  thf('14', plain,
% 0.42/0.59      ((((k2_struct_0 @ sk_B) = (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.42/0.59      inference('sup+', [status(thm)], ['12', '13'])).
% 0.42/0.59  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('16', plain,
% 0.42/0.59      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.42/0.59      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.42/0.59  thf('17', plain, ((l1_struct_0 @ sk_A)),
% 0.42/0.59      inference('sup-', [status(thm)], ['15', '16'])).
% 0.42/0.59  thf('18', plain, (((k2_struct_0 @ sk_B) = (k2_struct_0 @ sk_A))),
% 0.42/0.59      inference('demod', [status(thm)], ['14', '17'])).
% 0.42/0.59  thf('19', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.42/0.59      inference('demod', [status(thm)], ['11', '18'])).
% 0.42/0.59  thf('20', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_D_1 @ 
% 0.42/0.59        (k1_zfmisc_1 @ 
% 0.42/0.59         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C_1))))),
% 0.42/0.59      inference('demod', [status(thm)], ['2', '19'])).
% 0.42/0.59  thf('21', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.42/0.59      inference('demod', [status(thm)], ['11', '18'])).
% 0.42/0.59  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.42/0.59  thf(zf_stmt_3, axiom,
% 0.42/0.59    (![C:$i,B:$i,A:$i]:
% 0.42/0.59     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.42/0.59       ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.42/0.59         ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) ))).
% 0.42/0.59  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.42/0.59  thf(zf_stmt_5, axiom,
% 0.42/0.59    (![D:$i,C:$i,B:$i,A:$i]:
% 0.42/0.59     ( ( zip_tseitin_1 @ D @ C @ B @ A ) <=>
% 0.42/0.59       ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.42/0.59         ( ( v3_pre_topc @ D @ B ) =>
% 0.42/0.59           ( v3_pre_topc @
% 0.42/0.59             ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.42/0.59             A ) ) ) ))).thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $o).
% 0.42/0.59  thf(zf_stmt_7, axiom,
% 0.42/0.59    (![A:$i]:
% 0.42/0.59     ( ( l1_pre_topc @ A ) =>
% 0.42/0.59       ( ![B:$i]:
% 0.42/0.59         ( ( l1_pre_topc @ B ) =>
% 0.42/0.59           ( ![C:$i]:
% 0.42/0.59             ( ( ( v1_funct_1 @ C ) & 
% 0.42/0.59                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.42/0.59                 ( m1_subset_1 @
% 0.42/0.59                   C @ 
% 0.42/0.59                   ( k1_zfmisc_1 @
% 0.42/0.59                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.42/0.59               ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) ) ) ) ) ))).
% 0.42/0.59  thf('22', plain,
% 0.42/0.59      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.42/0.59         (~ (l1_pre_topc @ X24)
% 0.42/0.59          | ~ (zip_tseitin_0 @ X24 @ X25)
% 0.42/0.59          | (zip_tseitin_2 @ X26 @ X24 @ X25)
% 0.42/0.59          | ~ (m1_subset_1 @ X26 @ 
% 0.42/0.59               (k1_zfmisc_1 @ 
% 0.42/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X24))))
% 0.42/0.59          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X24))
% 0.42/0.59          | ~ (v1_funct_1 @ X26)
% 0.42/0.59          | ~ (l1_pre_topc @ X25))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.42/0.59  thf('23', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i]:
% 0.42/0.59         (~ (m1_subset_1 @ X1 @ 
% 0.42/0.59             (k1_zfmisc_1 @ 
% 0.42/0.59              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.42/0.59          | ~ (l1_pre_topc @ sk_B)
% 0.42/0.59          | ~ (v1_funct_1 @ X1)
% 0.42/0.59          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.42/0.59          | (zip_tseitin_2 @ X1 @ X0 @ sk_B)
% 0.42/0.59          | ~ (zip_tseitin_0 @ X0 @ sk_B)
% 0.42/0.59          | ~ (l1_pre_topc @ X0))),
% 0.42/0.59      inference('sup-', [status(thm)], ['21', '22'])).
% 0.42/0.59  thf('24', plain, ((l1_pre_topc @ sk_B)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('25', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.42/0.59      inference('demod', [status(thm)], ['11', '18'])).
% 0.42/0.59  thf('26', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i]:
% 0.42/0.59         (~ (m1_subset_1 @ X1 @ 
% 0.42/0.59             (k1_zfmisc_1 @ 
% 0.42/0.59              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.42/0.59          | ~ (v1_funct_1 @ X1)
% 0.42/0.59          | ~ (v1_funct_2 @ X1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 0.42/0.59          | (zip_tseitin_2 @ X1 @ X0 @ sk_B)
% 0.42/0.59          | ~ (zip_tseitin_0 @ X0 @ sk_B)
% 0.42/0.59          | ~ (l1_pre_topc @ X0))),
% 0.42/0.59      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.42/0.59  thf('27', plain,
% 0.42/0.59      ((~ (l1_pre_topc @ sk_C_1)
% 0.42/0.59        | ~ (zip_tseitin_0 @ sk_C_1 @ sk_B)
% 0.42/0.59        | (zip_tseitin_2 @ sk_D_1 @ sk_C_1 @ sk_B)
% 0.42/0.59        | ~ (v1_funct_2 @ sk_D_1 @ (k2_struct_0 @ sk_A) @ 
% 0.42/0.59             (u1_struct_0 @ sk_C_1))
% 0.42/0.59        | ~ (v1_funct_1 @ sk_D_1))),
% 0.42/0.59      inference('sup-', [status(thm)], ['20', '26'])).
% 0.42/0.59  thf('28', plain, ((l1_pre_topc @ sk_C_1)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('29', plain,
% 0.42/0.59      (![X8 : $i]:
% 0.42/0.59         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.42/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.59  thf('30', plain,
% 0.42/0.59      ((v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('31', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('32', plain,
% 0.42/0.59      ((v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C_1))),
% 0.42/0.59      inference('demod', [status(thm)], ['30', '31'])).
% 0.42/0.59  thf('33', plain,
% 0.42/0.59      (((v1_funct_2 @ sk_D_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C_1))
% 0.42/0.59        | ~ (l1_struct_0 @ sk_A))),
% 0.42/0.59      inference('sup+', [status(thm)], ['29', '32'])).
% 0.42/0.59  thf('34', plain, ((l1_struct_0 @ sk_A)),
% 0.42/0.59      inference('sup-', [status(thm)], ['15', '16'])).
% 0.42/0.59  thf('35', plain,
% 0.42/0.59      ((v1_funct_2 @ sk_D_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C_1))),
% 0.42/0.59      inference('demod', [status(thm)], ['33', '34'])).
% 0.42/0.59  thf('36', plain, ((v1_funct_1 @ sk_D_1)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('37', plain,
% 0.42/0.59      ((~ (zip_tseitin_0 @ sk_C_1 @ sk_B)
% 0.42/0.59        | (zip_tseitin_2 @ sk_D_1 @ sk_C_1 @ sk_B))),
% 0.42/0.59      inference('demod', [status(thm)], ['27', '28', '35', '36'])).
% 0.42/0.59  thf('38', plain,
% 0.42/0.59      ((((k2_struct_0 @ sk_C_1) = (k1_xboole_0))
% 0.42/0.59        | (zip_tseitin_2 @ sk_D_1 @ sk_C_1 @ sk_B))),
% 0.42/0.59      inference('sup-', [status(thm)], ['1', '37'])).
% 0.42/0.59  thf('39', plain, ((v5_pre_topc @ sk_D_1 @ sk_B @ sk_C_1)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('40', plain,
% 0.42/0.59      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.42/0.59         (~ (v5_pre_topc @ X22 @ X20 @ X21)
% 0.42/0.59          | (zip_tseitin_1 @ X23 @ X22 @ X21 @ X20)
% 0.42/0.59          | ~ (zip_tseitin_2 @ X22 @ X21 @ X20))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.42/0.59  thf('41', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         (~ (zip_tseitin_2 @ sk_D_1 @ sk_C_1 @ sk_B)
% 0.42/0.59          | (zip_tseitin_1 @ X0 @ sk_D_1 @ sk_C_1 @ sk_B))),
% 0.42/0.59      inference('sup-', [status(thm)], ['39', '40'])).
% 0.42/0.59  thf('42', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         (((k2_struct_0 @ sk_C_1) = (k1_xboole_0))
% 0.42/0.59          | (zip_tseitin_1 @ X0 @ sk_D_1 @ sk_C_1 @ sk_B))),
% 0.42/0.59      inference('sup-', [status(thm)], ['38', '41'])).
% 0.42/0.59  thf('43', plain,
% 0.42/0.59      (![X13 : $i, X14 : $i]:
% 0.42/0.59         ((zip_tseitin_0 @ X13 @ X14) | ((k2_struct_0 @ X13) = (k1_xboole_0)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.59  thf('44', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_D_1 @ 
% 0.42/0.59        (k1_zfmisc_1 @ 
% 0.42/0.59         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C_1))))),
% 0.42/0.59      inference('demod', [status(thm)], ['2', '19'])).
% 0.42/0.59  thf('45', plain,
% 0.42/0.59      (![X8 : $i]:
% 0.42/0.59         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.42/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.59  thf('46', plain,
% 0.42/0.59      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.42/0.59         (~ (l1_pre_topc @ X24)
% 0.42/0.59          | ~ (zip_tseitin_0 @ X24 @ X25)
% 0.42/0.59          | (zip_tseitin_2 @ X26 @ X24 @ X25)
% 0.42/0.59          | ~ (m1_subset_1 @ X26 @ 
% 0.42/0.59               (k1_zfmisc_1 @ 
% 0.42/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X24))))
% 0.42/0.59          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X24))
% 0.42/0.59          | ~ (v1_funct_1 @ X26)
% 0.42/0.59          | ~ (l1_pre_topc @ X25))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.42/0.60  thf('47', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.60         (~ (m1_subset_1 @ X2 @ 
% 0.42/0.60             (k1_zfmisc_1 @ 
% 0.42/0.60              (k2_zfmisc_1 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1))))
% 0.42/0.60          | ~ (l1_struct_0 @ X0)
% 0.42/0.60          | ~ (l1_pre_topc @ X0)
% 0.42/0.60          | ~ (v1_funct_1 @ X2)
% 0.42/0.60          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.42/0.60          | (zip_tseitin_2 @ X2 @ X1 @ X0)
% 0.42/0.60          | ~ (zip_tseitin_0 @ X1 @ X0)
% 0.42/0.60          | ~ (l1_pre_topc @ X1))),
% 0.42/0.60      inference('sup-', [status(thm)], ['45', '46'])).
% 0.42/0.60  thf('48', plain,
% 0.42/0.60      ((~ (l1_pre_topc @ sk_C_1)
% 0.42/0.60        | ~ (zip_tseitin_0 @ sk_C_1 @ sk_A)
% 0.42/0.60        | (zip_tseitin_2 @ sk_D_1 @ sk_C_1 @ sk_A)
% 0.42/0.60        | ~ (v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.60             (u1_struct_0 @ sk_C_1))
% 0.42/0.60        | ~ (v1_funct_1 @ sk_D_1)
% 0.42/0.60        | ~ (l1_pre_topc @ sk_A)
% 0.42/0.60        | ~ (l1_struct_0 @ sk_A))),
% 0.42/0.60      inference('sup-', [status(thm)], ['44', '47'])).
% 0.42/0.60  thf('49', plain, ((l1_pre_topc @ sk_C_1)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('50', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.42/0.60      inference('demod', [status(thm)], ['6', '9'])).
% 0.42/0.60  thf('51', plain, (((k2_struct_0 @ sk_B) = (k2_struct_0 @ sk_A))),
% 0.42/0.60      inference('demod', [status(thm)], ['14', '17'])).
% 0.42/0.60  thf('52', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.42/0.60      inference('demod', [status(thm)], ['50', '51'])).
% 0.42/0.60  thf('53', plain,
% 0.42/0.60      ((v1_funct_2 @ sk_D_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C_1))),
% 0.42/0.60      inference('demod', [status(thm)], ['33', '34'])).
% 0.42/0.60  thf('54', plain, ((v1_funct_1 @ sk_D_1)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('56', plain, ((l1_struct_0 @ sk_A)),
% 0.42/0.60      inference('sup-', [status(thm)], ['15', '16'])).
% 0.42/0.60  thf('57', plain,
% 0.42/0.60      ((~ (zip_tseitin_0 @ sk_C_1 @ sk_A)
% 0.42/0.60        | (zip_tseitin_2 @ sk_D_1 @ sk_C_1 @ sk_A))),
% 0.42/0.60      inference('demod', [status(thm)],
% 0.42/0.60                ['48', '49', '52', '53', '54', '55', '56'])).
% 0.42/0.60  thf('58', plain,
% 0.42/0.60      ((((k2_struct_0 @ sk_C_1) = (k1_xboole_0))
% 0.42/0.60        | (zip_tseitin_2 @ sk_D_1 @ sk_C_1 @ sk_A))),
% 0.42/0.60      inference('sup-', [status(thm)], ['43', '57'])).
% 0.42/0.60  thf('59', plain,
% 0.42/0.60      (![X15 : $i, X16 : $i, X18 : $i, X19 : $i]:
% 0.42/0.60         ((zip_tseitin_1 @ X15 @ X18 @ X16 @ X19) | (v3_pre_topc @ X15 @ X16))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.42/0.60  thf('60', plain,
% 0.42/0.60      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.42/0.60         (~ (zip_tseitin_1 @ (sk_D @ X20 @ X21 @ X22) @ X22 @ X21 @ X20)
% 0.42/0.60          | (v5_pre_topc @ X22 @ X20 @ X21)
% 0.42/0.60          | ~ (zip_tseitin_2 @ X22 @ X21 @ X20))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.42/0.60  thf('61', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.60         ((v3_pre_topc @ (sk_D @ X0 @ X1 @ X2) @ X1)
% 0.42/0.60          | ~ (zip_tseitin_2 @ X2 @ X1 @ X0)
% 0.42/0.60          | (v5_pre_topc @ X2 @ X0 @ X1))),
% 0.42/0.60      inference('sup-', [status(thm)], ['59', '60'])).
% 0.42/0.60  thf('62', plain,
% 0.42/0.60      ((((k2_struct_0 @ sk_C_1) = (k1_xboole_0))
% 0.42/0.60        | (v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1)
% 0.42/0.60        | (v3_pre_topc @ (sk_D @ sk_A @ sk_C_1 @ sk_D_1) @ sk_C_1))),
% 0.42/0.60      inference('sup-', [status(thm)], ['58', '61'])).
% 0.42/0.60  thf('63', plain,
% 0.42/0.60      ((~ (v1_funct_1 @ sk_D_1)
% 0.42/0.60        | ~ (v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.60             (u1_struct_0 @ sk_C_1))
% 0.42/0.60        | ~ (v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1)
% 0.42/0.60        | ~ (m1_subset_1 @ sk_D_1 @ 
% 0.42/0.60             (k1_zfmisc_1 @ 
% 0.42/0.60              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C_1)))))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('64', plain,
% 0.42/0.60      ((~ (v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1))
% 0.42/0.60         <= (~ ((v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1)))),
% 0.42/0.60      inference('split', [status(esa)], ['63'])).
% 0.42/0.60  thf('65', plain,
% 0.42/0.60      ((v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C_1))),
% 0.42/0.60      inference('demod', [status(thm)], ['30', '31'])).
% 0.42/0.60  thf('66', plain,
% 0.42/0.60      ((~ (v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C_1)))
% 0.42/0.60         <= (~
% 0.42/0.60             ((v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_A) @ 
% 0.42/0.60               (u1_struct_0 @ sk_C_1))))),
% 0.42/0.60      inference('split', [status(esa)], ['63'])).
% 0.42/0.60  thf('67', plain,
% 0.42/0.60      (((v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C_1)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['65', '66'])).
% 0.42/0.60  thf('68', plain, ((v1_funct_1 @ sk_D_1)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('69', plain, ((~ (v1_funct_1 @ sk_D_1)) <= (~ ((v1_funct_1 @ sk_D_1)))),
% 0.42/0.60      inference('split', [status(esa)], ['63'])).
% 0.42/0.60  thf('70', plain, (((v1_funct_1 @ sk_D_1))),
% 0.42/0.60      inference('sup-', [status(thm)], ['68', '69'])).
% 0.42/0.60  thf('71', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_D_1 @ 
% 0.42/0.60        (k1_zfmisc_1 @ 
% 0.42/0.60         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C_1))))),
% 0.42/0.60      inference('demod', [status(thm)], ['2', '19'])).
% 0.42/0.60  thf('72', plain,
% 0.42/0.60      (![X8 : $i]:
% 0.42/0.60         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.42/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.60  thf('73', plain,
% 0.42/0.60      ((~ (m1_subset_1 @ sk_D_1 @ 
% 0.42/0.60           (k1_zfmisc_1 @ 
% 0.42/0.60            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C_1)))))
% 0.42/0.60         <= (~
% 0.42/0.60             ((m1_subset_1 @ sk_D_1 @ 
% 0.42/0.60               (k1_zfmisc_1 @ 
% 0.42/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C_1))))))),
% 0.42/0.60      inference('split', [status(esa)], ['63'])).
% 0.42/0.60  thf('74', plain,
% 0.42/0.60      (((~ (m1_subset_1 @ sk_D_1 @ 
% 0.42/0.60            (k1_zfmisc_1 @ 
% 0.42/0.60             (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C_1))))
% 0.42/0.60         | ~ (l1_struct_0 @ sk_A)))
% 0.42/0.60         <= (~
% 0.42/0.60             ((m1_subset_1 @ sk_D_1 @ 
% 0.42/0.60               (k1_zfmisc_1 @ 
% 0.42/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C_1))))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['72', '73'])).
% 0.42/0.60  thf('75', plain, ((l1_struct_0 @ sk_A)),
% 0.42/0.60      inference('sup-', [status(thm)], ['15', '16'])).
% 0.42/0.60  thf('76', plain,
% 0.42/0.60      ((~ (m1_subset_1 @ sk_D_1 @ 
% 0.42/0.60           (k1_zfmisc_1 @ 
% 0.42/0.60            (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C_1)))))
% 0.42/0.60         <= (~
% 0.42/0.60             ((m1_subset_1 @ sk_D_1 @ 
% 0.42/0.60               (k1_zfmisc_1 @ 
% 0.42/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C_1))))))),
% 0.42/0.60      inference('demod', [status(thm)], ['74', '75'])).
% 0.42/0.60  thf('77', plain,
% 0.42/0.60      (((m1_subset_1 @ sk_D_1 @ 
% 0.42/0.60         (k1_zfmisc_1 @ 
% 0.42/0.60          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C_1)))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['71', '76'])).
% 0.42/0.60  thf('78', plain,
% 0.42/0.60      (~ ((v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1)) | 
% 0.42/0.60       ~
% 0.42/0.60       ((m1_subset_1 @ sk_D_1 @ 
% 0.42/0.60         (k1_zfmisc_1 @ 
% 0.42/0.60          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C_1))))) | 
% 0.42/0.60       ~ ((v1_funct_1 @ sk_D_1)) | 
% 0.42/0.60       ~
% 0.42/0.60       ((v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C_1)))),
% 0.42/0.60      inference('split', [status(esa)], ['63'])).
% 0.42/0.60  thf('79', plain, (~ ((v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1))),
% 0.42/0.60      inference('sat_resolution*', [status(thm)], ['67', '70', '77', '78'])).
% 0.42/0.60  thf('80', plain, (~ (v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1)),
% 0.42/0.60      inference('simpl_trail', [status(thm)], ['64', '79'])).
% 0.42/0.60  thf('81', plain,
% 0.42/0.60      (((v3_pre_topc @ (sk_D @ sk_A @ sk_C_1 @ sk_D_1) @ sk_C_1)
% 0.42/0.60        | ((k2_struct_0 @ sk_C_1) = (k1_xboole_0)))),
% 0.42/0.60      inference('clc', [status(thm)], ['62', '80'])).
% 0.42/0.60  thf('82', plain,
% 0.42/0.60      ((((k2_struct_0 @ sk_C_1) = (k1_xboole_0))
% 0.42/0.60        | (zip_tseitin_2 @ sk_D_1 @ sk_C_1 @ sk_A))),
% 0.42/0.60      inference('sup-', [status(thm)], ['43', '57'])).
% 0.42/0.60  thf('83', plain,
% 0.42/0.60      (![X15 : $i, X16 : $i, X18 : $i, X19 : $i]:
% 0.42/0.60         ((zip_tseitin_1 @ X15 @ X18 @ X16 @ X19)
% 0.42/0.60          | (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16))))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.42/0.60  thf('84', plain,
% 0.42/0.60      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.42/0.60         (~ (zip_tseitin_1 @ (sk_D @ X20 @ X21 @ X22) @ X22 @ X21 @ X20)
% 0.42/0.60          | (v5_pre_topc @ X22 @ X20 @ X21)
% 0.42/0.60          | ~ (zip_tseitin_2 @ X22 @ X21 @ X20))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.42/0.60  thf('85', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.60         ((m1_subset_1 @ (sk_D @ X0 @ X1 @ X2) @ 
% 0.42/0.60           (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.42/0.60          | ~ (zip_tseitin_2 @ X2 @ X1 @ X0)
% 0.42/0.60          | (v5_pre_topc @ X2 @ X0 @ X1))),
% 0.42/0.60      inference('sup-', [status(thm)], ['83', '84'])).
% 0.42/0.60  thf('86', plain,
% 0.42/0.60      ((((k2_struct_0 @ sk_C_1) = (k1_xboole_0))
% 0.42/0.60        | (v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1)
% 0.42/0.60        | (m1_subset_1 @ (sk_D @ sk_A @ sk_C_1 @ sk_D_1) @ 
% 0.42/0.60           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['82', '85'])).
% 0.42/0.60  thf('87', plain, (~ (v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1)),
% 0.42/0.60      inference('simpl_trail', [status(thm)], ['64', '79'])).
% 0.42/0.60  thf('88', plain,
% 0.42/0.60      (((m1_subset_1 @ (sk_D @ sk_A @ sk_C_1 @ sk_D_1) @ 
% 0.42/0.60         (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.42/0.60        | ((k2_struct_0 @ sk_C_1) = (k1_xboole_0)))),
% 0.42/0.60      inference('clc', [status(thm)], ['86', '87'])).
% 0.42/0.60  thf('89', plain,
% 0.42/0.60      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.42/0.60         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.42/0.60          | (v3_pre_topc @ 
% 0.42/0.60             (k8_relset_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16) @ X18 @ 
% 0.42/0.60              X15) @ 
% 0.42/0.60             X17)
% 0.42/0.60          | ~ (v3_pre_topc @ X15 @ X16)
% 0.42/0.60          | ~ (zip_tseitin_1 @ X15 @ X18 @ X16 @ X17))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.42/0.60  thf('90', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         (((k2_struct_0 @ sk_C_1) = (k1_xboole_0))
% 0.42/0.60          | ~ (zip_tseitin_1 @ (sk_D @ sk_A @ sk_C_1 @ sk_D_1) @ X1 @ sk_C_1 @ 
% 0.42/0.60               X0)
% 0.42/0.60          | ~ (v3_pre_topc @ (sk_D @ sk_A @ sk_C_1 @ sk_D_1) @ sk_C_1)
% 0.42/0.60          | (v3_pre_topc @ 
% 0.42/0.60             (k8_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_C_1) @ X1 @ 
% 0.42/0.60              (sk_D @ sk_A @ sk_C_1 @ sk_D_1)) @ 
% 0.42/0.60             X0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['88', '89'])).
% 0.42/0.60  thf('91', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         (((k2_struct_0 @ sk_C_1) = (k1_xboole_0))
% 0.42/0.60          | (v3_pre_topc @ 
% 0.42/0.60             (k8_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_C_1) @ X1 @ 
% 0.42/0.60              (sk_D @ sk_A @ sk_C_1 @ sk_D_1)) @ 
% 0.42/0.60             X0)
% 0.42/0.60          | ~ (zip_tseitin_1 @ (sk_D @ sk_A @ sk_C_1 @ sk_D_1) @ X1 @ sk_C_1 @ 
% 0.42/0.60               X0)
% 0.42/0.60          | ((k2_struct_0 @ sk_C_1) = (k1_xboole_0)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['81', '90'])).
% 0.42/0.60  thf('92', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         (~ (zip_tseitin_1 @ (sk_D @ sk_A @ sk_C_1 @ sk_D_1) @ X1 @ sk_C_1 @ X0)
% 0.42/0.60          | (v3_pre_topc @ 
% 0.42/0.60             (k8_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_C_1) @ X1 @ 
% 0.42/0.60              (sk_D @ sk_A @ sk_C_1 @ sk_D_1)) @ 
% 0.42/0.60             X0)
% 0.42/0.60          | ((k2_struct_0 @ sk_C_1) = (k1_xboole_0)))),
% 0.42/0.60      inference('simplify', [status(thm)], ['91'])).
% 0.42/0.60  thf('93', plain,
% 0.42/0.60      ((((k2_struct_0 @ sk_C_1) = (k1_xboole_0))
% 0.42/0.60        | ((k2_struct_0 @ sk_C_1) = (k1_xboole_0))
% 0.42/0.60        | (v3_pre_topc @ 
% 0.42/0.60           (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1) @ 
% 0.42/0.60            sk_D_1 @ (sk_D @ sk_A @ sk_C_1 @ sk_D_1)) @ 
% 0.42/0.60           sk_B))),
% 0.42/0.60      inference('sup-', [status(thm)], ['42', '92'])).
% 0.42/0.60  thf('94', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.42/0.60      inference('demod', [status(thm)], ['11', '18'])).
% 0.42/0.60  thf('95', plain,
% 0.42/0.60      ((((k2_struct_0 @ sk_C_1) = (k1_xboole_0))
% 0.42/0.60        | ((k2_struct_0 @ sk_C_1) = (k1_xboole_0))
% 0.42/0.60        | (v3_pre_topc @ 
% 0.42/0.60           (k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C_1) @ 
% 0.42/0.60            sk_D_1 @ (sk_D @ sk_A @ sk_C_1 @ sk_D_1)) @ 
% 0.42/0.60           sk_B))),
% 0.42/0.60      inference('demod', [status(thm)], ['93', '94'])).
% 0.42/0.60  thf('96', plain,
% 0.42/0.60      (((v3_pre_topc @ 
% 0.42/0.60         (k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C_1) @ 
% 0.42/0.60          sk_D_1 @ (sk_D @ sk_A @ sk_C_1 @ sk_D_1)) @ 
% 0.42/0.60         sk_B)
% 0.42/0.60        | ((k2_struct_0 @ sk_C_1) = (k1_xboole_0)))),
% 0.42/0.60      inference('simplify', [status(thm)], ['95'])).
% 0.42/0.60  thf('97', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_D_1 @ 
% 0.42/0.60        (k1_zfmisc_1 @ 
% 0.42/0.60         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C_1))))),
% 0.42/0.60      inference('demod', [status(thm)], ['2', '19'])).
% 0.42/0.60  thf(dt_k8_relset_1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.60       ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.42/0.60  thf('98', plain,
% 0.42/0.60      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.42/0.60         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6)))
% 0.42/0.60          | (m1_subset_1 @ (k8_relset_1 @ X5 @ X6 @ X4 @ X7) @ 
% 0.42/0.60             (k1_zfmisc_1 @ X5)))),
% 0.42/0.60      inference('cnf', [status(esa)], [dt_k8_relset_1])).
% 0.42/0.60  thf('99', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (m1_subset_1 @ 
% 0.42/0.60          (k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C_1) @ 
% 0.42/0.60           sk_D_1 @ X0) @ 
% 0.42/0.60          (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['97', '98'])).
% 0.42/0.60  thf('100', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.42/0.60      inference('demod', [status(thm)], ['11', '18'])).
% 0.42/0.60  thf(d5_pre_topc, axiom,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( l1_pre_topc @ A ) =>
% 0.42/0.60       ( ![B:$i]:
% 0.42/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.60           ( ( v3_pre_topc @ B @ A ) <=>
% 0.42/0.60             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.42/0.60  thf('101', plain,
% 0.42/0.60      (![X9 : $i, X10 : $i]:
% 0.42/0.60         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.42/0.60          | ~ (v3_pre_topc @ X9 @ X10)
% 0.42/0.60          | (r2_hidden @ X9 @ (u1_pre_topc @ X10))
% 0.42/0.60          | ~ (l1_pre_topc @ X10))),
% 0.42/0.60      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.42/0.60  thf('102', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.42/0.60          | ~ (l1_pre_topc @ sk_B)
% 0.42/0.60          | (r2_hidden @ X0 @ (u1_pre_topc @ sk_B))
% 0.42/0.60          | ~ (v3_pre_topc @ X0 @ sk_B))),
% 0.42/0.60      inference('sup-', [status(thm)], ['100', '101'])).
% 0.42/0.60  thf('103', plain, ((l1_pre_topc @ sk_B)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('104', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.42/0.60          | (r2_hidden @ X0 @ (u1_pre_topc @ sk_B))
% 0.42/0.60          | ~ (v3_pre_topc @ X0 @ sk_B))),
% 0.42/0.60      inference('demod', [status(thm)], ['102', '103'])).
% 0.42/0.60  thf('105', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (v3_pre_topc @ 
% 0.42/0.60             (k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C_1) @ 
% 0.42/0.60              sk_D_1 @ X0) @ 
% 0.42/0.60             sk_B)
% 0.42/0.60          | (r2_hidden @ 
% 0.42/0.60             (k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C_1) @ 
% 0.42/0.60              sk_D_1 @ X0) @ 
% 0.42/0.60             (u1_pre_topc @ sk_B)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['99', '104'])).
% 0.42/0.60  thf('106', plain,
% 0.42/0.60      ((((k2_struct_0 @ sk_C_1) = (k1_xboole_0))
% 0.42/0.60        | (r2_hidden @ 
% 0.42/0.60           (k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C_1) @ 
% 0.42/0.60            sk_D_1 @ (sk_D @ sk_A @ sk_C_1 @ sk_D_1)) @ 
% 0.42/0.60           (u1_pre_topc @ sk_B)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['96', '105'])).
% 0.42/0.60  thf('107', plain,
% 0.42/0.60      ((r1_tarski @ (u1_pre_topc @ sk_B) @ (u1_pre_topc @ sk_A))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf(d3_tarski, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( r1_tarski @ A @ B ) <=>
% 0.42/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.42/0.60  thf('108', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X0 @ X1)
% 0.42/0.60          | (r2_hidden @ X0 @ X2)
% 0.42/0.60          | ~ (r1_tarski @ X1 @ X2))),
% 0.42/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.42/0.60  thf('109', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((r2_hidden @ X0 @ (u1_pre_topc @ sk_A))
% 0.42/0.60          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_B)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['107', '108'])).
% 0.42/0.60  thf('110', plain,
% 0.42/0.60      ((((k2_struct_0 @ sk_C_1) = (k1_xboole_0))
% 0.42/0.60        | (r2_hidden @ 
% 0.42/0.60           (k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C_1) @ 
% 0.42/0.60            sk_D_1 @ (sk_D @ sk_A @ sk_C_1 @ sk_D_1)) @ 
% 0.42/0.60           (u1_pre_topc @ sk_A)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['106', '109'])).
% 0.42/0.60  thf('111', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (m1_subset_1 @ 
% 0.42/0.60          (k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C_1) @ 
% 0.42/0.60           sk_D_1 @ X0) @ 
% 0.42/0.60          (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['97', '98'])).
% 0.42/0.60  thf('112', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.42/0.60      inference('demod', [status(thm)], ['50', '51'])).
% 0.42/0.60  thf('113', plain,
% 0.42/0.60      (![X9 : $i, X10 : $i]:
% 0.42/0.60         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.42/0.60          | ~ (r2_hidden @ X9 @ (u1_pre_topc @ X10))
% 0.42/0.60          | (v3_pre_topc @ X9 @ X10)
% 0.42/0.60          | ~ (l1_pre_topc @ X10))),
% 0.42/0.60      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.42/0.60  thf('114', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.42/0.60          | ~ (l1_pre_topc @ sk_A)
% 0.42/0.60          | (v3_pre_topc @ X0 @ sk_A)
% 0.42/0.60          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_A)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['112', '113'])).
% 0.42/0.60  thf('115', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('116', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.42/0.60          | (v3_pre_topc @ X0 @ sk_A)
% 0.42/0.60          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_A)))),
% 0.42/0.60      inference('demod', [status(thm)], ['114', '115'])).
% 0.42/0.60  thf('117', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (r2_hidden @ 
% 0.42/0.60             (k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C_1) @ 
% 0.42/0.60              sk_D_1 @ X0) @ 
% 0.42/0.60             (u1_pre_topc @ sk_A))
% 0.42/0.60          | (v3_pre_topc @ 
% 0.42/0.60             (k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C_1) @ 
% 0.42/0.60              sk_D_1 @ X0) @ 
% 0.42/0.60             sk_A))),
% 0.42/0.60      inference('sup-', [status(thm)], ['111', '116'])).
% 0.42/0.60  thf('118', plain,
% 0.42/0.60      ((((k2_struct_0 @ sk_C_1) = (k1_xboole_0))
% 0.42/0.60        | (v3_pre_topc @ 
% 0.42/0.60           (k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C_1) @ 
% 0.42/0.60            sk_D_1 @ (sk_D @ sk_A @ sk_C_1 @ sk_D_1)) @ 
% 0.42/0.60           sk_A))),
% 0.42/0.60      inference('sup-', [status(thm)], ['110', '117'])).
% 0.42/0.60  thf('119', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.42/0.60      inference('demod', [status(thm)], ['50', '51'])).
% 0.42/0.60  thf('120', plain,
% 0.42/0.60      (![X15 : $i, X16 : $i, X18 : $i, X19 : $i]:
% 0.42/0.60         ((zip_tseitin_1 @ X15 @ X18 @ X16 @ X19)
% 0.42/0.60          | ~ (v3_pre_topc @ 
% 0.42/0.60               (k8_relset_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X16) @ 
% 0.42/0.60                X18 @ X15) @ 
% 0.42/0.60               X19))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.42/0.60  thf('121', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.60         (~ (v3_pre_topc @ 
% 0.42/0.60             (k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ X2) @ X1 @ X0) @ 
% 0.42/0.60             sk_A)
% 0.42/0.60          | (zip_tseitin_1 @ X0 @ X1 @ X2 @ sk_A))),
% 0.42/0.60      inference('sup-', [status(thm)], ['119', '120'])).
% 0.42/0.60  thf('122', plain,
% 0.42/0.60      ((((k2_struct_0 @ sk_C_1) = (k1_xboole_0))
% 0.42/0.60        | (zip_tseitin_1 @ (sk_D @ sk_A @ sk_C_1 @ sk_D_1) @ sk_D_1 @ sk_C_1 @ 
% 0.42/0.60           sk_A))),
% 0.42/0.60      inference('sup-', [status(thm)], ['118', '121'])).
% 0.42/0.60  thf('123', plain,
% 0.42/0.60      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.42/0.60         (~ (zip_tseitin_1 @ (sk_D @ X20 @ X21 @ X22) @ X22 @ X21 @ X20)
% 0.42/0.60          | (v5_pre_topc @ X22 @ X20 @ X21)
% 0.42/0.60          | ~ (zip_tseitin_2 @ X22 @ X21 @ X20))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.42/0.60  thf('124', plain,
% 0.42/0.60      ((((k2_struct_0 @ sk_C_1) = (k1_xboole_0))
% 0.42/0.60        | ~ (zip_tseitin_2 @ sk_D_1 @ sk_C_1 @ sk_A)
% 0.42/0.60        | (v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1))),
% 0.42/0.60      inference('sup-', [status(thm)], ['122', '123'])).
% 0.42/0.60  thf('125', plain,
% 0.42/0.60      ((((k2_struct_0 @ sk_C_1) = (k1_xboole_0))
% 0.42/0.60        | (zip_tseitin_2 @ sk_D_1 @ sk_C_1 @ sk_A))),
% 0.42/0.60      inference('sup-', [status(thm)], ['43', '57'])).
% 0.42/0.60  thf('126', plain,
% 0.42/0.60      (((v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1)
% 0.42/0.60        | ((k2_struct_0 @ sk_C_1) = (k1_xboole_0)))),
% 0.42/0.60      inference('clc', [status(thm)], ['124', '125'])).
% 0.42/0.60  thf('127', plain, (~ (v5_pre_topc @ sk_D_1 @ sk_A @ sk_C_1)),
% 0.42/0.60      inference('simpl_trail', [status(thm)], ['64', '79'])).
% 0.42/0.60  thf('128', plain, (((k2_struct_0 @ sk_C_1) = (k1_xboole_0))),
% 0.42/0.60      inference('clc', [status(thm)], ['126', '127'])).
% 0.42/0.60  thf('129', plain,
% 0.42/0.60      (![X8 : $i]:
% 0.42/0.60         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.42/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.60  thf(fc2_struct_0, axiom,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.42/0.60       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.42/0.60  thf('130', plain,
% 0.42/0.60      (![X12 : $i]:
% 0.42/0.60         (~ (v1_xboole_0 @ (u1_struct_0 @ X12))
% 0.42/0.60          | ~ (l1_struct_0 @ X12)
% 0.42/0.60          | (v2_struct_0 @ X12))),
% 0.42/0.60      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.42/0.60  thf('131', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.42/0.60          | ~ (l1_struct_0 @ X0)
% 0.42/0.60          | (v2_struct_0 @ X0)
% 0.42/0.60          | ~ (l1_struct_0 @ X0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['129', '130'])).
% 0.42/0.60  thf('132', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((v2_struct_0 @ X0)
% 0.42/0.60          | ~ (l1_struct_0 @ X0)
% 0.42/0.60          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.42/0.60      inference('simplify', [status(thm)], ['131'])).
% 0.42/0.60  thf('133', plain,
% 0.42/0.60      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.42/0.60        | ~ (l1_struct_0 @ sk_C_1)
% 0.42/0.60        | (v2_struct_0 @ sk_C_1))),
% 0.42/0.60      inference('sup-', [status(thm)], ['128', '132'])).
% 0.42/0.60  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.42/0.60  thf('134', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.42/0.60      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.42/0.60  thf('135', plain, ((l1_pre_topc @ sk_C_1)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('136', plain,
% 0.42/0.60      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.42/0.60      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.42/0.60  thf('137', plain, ((l1_struct_0 @ sk_C_1)),
% 0.42/0.60      inference('sup-', [status(thm)], ['135', '136'])).
% 0.42/0.60  thf('138', plain, ((v2_struct_0 @ sk_C_1)),
% 0.42/0.60      inference('demod', [status(thm)], ['133', '134', '137'])).
% 0.42/0.60  thf('139', plain, ($false), inference('demod', [status(thm)], ['0', '138'])).
% 0.42/0.60  
% 0.42/0.60  % SZS output end Refutation
% 0.42/0.60  
% 0.42/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
