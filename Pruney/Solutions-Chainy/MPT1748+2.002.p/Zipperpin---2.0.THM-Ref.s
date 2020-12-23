%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZpiDOSsl1J

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:37 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  191 (1179 expanded)
%              Number of leaves         :   44 ( 359 expanded)
%              Depth                    :   30
%              Number of atoms          : 1684 (28718 expanded)
%              Number of equality atoms :   60 ( 709 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ~ ( v2_struct_0 @ sk_C ) ),
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
    ! [X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 )
      | ( ( k2_struct_0 @ X15 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) ),
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
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
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
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
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
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
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
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
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
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_2 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( v1_funct_2 @ X28 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
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
    ( ~ ( l1_pre_topc @ sk_C )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_C @ sk_B )
    | ~ ( v1_funct_2 @ sk_D_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('30',plain,(
    v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( v1_funct_2 @ sk_D_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('35',plain,(
    v1_funct_2 @ sk_D_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ~ ( zip_tseitin_0 @ sk_C @ sk_B )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['27','28','35','36'])).

thf('38',plain,
    ( ( ( k2_struct_0 @ sk_C )
      = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['1','37'])).

thf('39',plain,(
    v5_pre_topc @ sk_D_1 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( v5_pre_topc @ X24 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X25 @ X24 @ X23 @ X22 )
      | ~ ( zip_tseitin_2 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ sk_D_1 @ sk_C @ sk_B )
      | ( zip_tseitin_1 @ X0 @ sk_D_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ sk_C )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ X0 @ sk_D_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 )
      | ( ( k2_struct_0 @ X15 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('44',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['2','19'])).

thf('45',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('46',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_2 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( v1_funct_2 @ X28 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
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
    ( ~ ( l1_pre_topc @ sk_C )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_A )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_C @ sk_A )
    | ~ ( v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_C ),
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
    v1_funct_2 @ sk_D_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ),
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
    ( ~ ( zip_tseitin_0 @ sk_C @ sk_A )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['48','49','52','53','54','55','56'])).

thf('58',plain,
    ( ( ( k2_struct_0 @ sk_C )
      = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['43','57'])).

thf('59',plain,(
    ! [X17: $i,X18: $i,X20: $i,X21: $i] :
      ( ( zip_tseitin_1 @ X17 @ X20 @ X18 @ X21 )
      | ( v3_pre_topc @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('60',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D @ X22 @ X23 @ X24 ) @ X24 @ X23 @ X22 )
      | ( v5_pre_topc @ X24 @ X22 @ X23 )
      | ~ ( zip_tseitin_2 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v3_pre_topc @ ( sk_D @ X0 @ X1 @ X2 ) @ X1 )
      | ~ ( zip_tseitin_2 @ X2 @ X1 @ X0 )
      | ( v5_pre_topc @ X2 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k2_struct_0 @ sk_C )
      = k1_xboole_0 )
    | ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C )
    | ( v3_pre_topc @ ( sk_D @ sk_A @ sk_C @ sk_D_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,
    ( ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) )
    | ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C )
   <= ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['63'])).

thf('65',plain,(
    v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('66',plain,
    ( ~ ( v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) )
   <= ~ ( v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(split,[status(esa)],['63'])).

thf('67',plain,(
    v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ),
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
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['2','19'])).

thf('72',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('73',plain,
    ( ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) )
   <= ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) ) ),
    inference(split,[status(esa)],['63'])).

thf('74',plain,
    ( ( ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('76',plain,
    ( ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) )
   <= ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['71','76'])).

thf('78',plain,
    ( ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(split,[status(esa)],['63'])).

thf('79',plain,(
    ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['67','70','77','78'])).

thf('80',plain,(
    ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['64','79'])).

thf('81',plain,
    ( ( v3_pre_topc @ ( sk_D @ sk_A @ sk_C @ sk_D_1 ) @ sk_C )
    | ( ( k2_struct_0 @ sk_C )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['62','80'])).

thf('82',plain,
    ( ( ( k2_struct_0 @ sk_C )
      = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['43','57'])).

thf('83',plain,(
    ! [X17: $i,X18: $i,X20: $i,X21: $i] :
      ( ( zip_tseitin_1 @ X17 @ X20 @ X18 @ X21 )
      | ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('84',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_1 @ X1 @ X3 @ X0 @ X2 )
      | ( r1_tarski @ X1 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D @ X22 @ X23 @ X24 ) @ X24 @ X23 @ X22 )
      | ( v5_pre_topc @ X24 @ X22 @ X23 )
      | ~ ( zip_tseitin_2 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( sk_D @ X0 @ X1 @ X2 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( zip_tseitin_2 @ X2 @ X1 @ X0 )
      | ( v5_pre_topc @ X2 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( k2_struct_0 @ sk_C )
      = k1_xboole_0 )
    | ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C )
    | ( r1_tarski @ ( sk_D @ sk_A @ sk_C @ sk_D_1 ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['82','87'])).

thf('89',plain,(
    ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['64','79'])).

thf('90',plain,
    ( ( r1_tarski @ ( sk_D @ sk_A @ sk_C @ sk_D_1 ) @ ( u1_struct_0 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_C )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('92',plain,
    ( ( ( k2_struct_0 @ sk_C )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_D @ sk_A @ sk_C @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X18 ) @ X20 @ X17 ) @ X19 )
      | ~ ( v3_pre_topc @ X17 @ X18 )
      | ~ ( zip_tseitin_1 @ X17 @ X20 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_struct_0 @ sk_C )
        = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ ( sk_D @ sk_A @ sk_C @ sk_D_1 ) @ X1 @ sk_C @ X0 )
      | ~ ( v3_pre_topc @ ( sk_D @ sk_A @ sk_C @ sk_D_1 ) @ sk_C )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_C ) @ X1 @ ( sk_D @ sk_A @ sk_C @ sk_D_1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_struct_0 @ sk_C )
        = k1_xboole_0 )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_C ) @ X1 @ ( sk_D @ sk_A @ sk_C @ sk_D_1 ) ) @ X0 )
      | ~ ( zip_tseitin_1 @ ( sk_D @ sk_A @ sk_C @ sk_D_1 ) @ X1 @ sk_C @ X0 )
      | ( ( k2_struct_0 @ sk_C )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['81','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D @ sk_A @ sk_C @ sk_D_1 ) @ X1 @ sk_C @ X0 )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_C ) @ X1 @ ( sk_D @ sk_A @ sk_C @ sk_D_1 ) ) @ X0 )
      | ( ( k2_struct_0 @ sk_C )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,
    ( ( ( k2_struct_0 @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_C )
      = k1_xboole_0 )
    | ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ ( sk_D @ sk_A @ sk_C @ sk_D_1 ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['42','96'])).

thf('98',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['11','18'])).

thf('99',plain,
    ( ( ( k2_struct_0 @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_C )
      = k1_xboole_0 )
    | ( v3_pre_topc @ ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ ( sk_D @ sk_A @ sk_C @ sk_D_1 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( v3_pre_topc @ ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ ( sk_D @ sk_A @ sk_C @ sk_D_1 ) ) @ sk_B )
    | ( ( k2_struct_0 @ sk_C )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['2','19'])).

thf(dt_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('102',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ( m1_subset_1 @ ( k8_relset_1 @ X7 @ X8 @ X6 @ X9 ) @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relset_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
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

thf('105',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v3_pre_topc @ X11 @ X12 )
      | ( r2_hidden @ X11 @ ( u1_pre_topc @ X12 ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B ) )
      | ~ ( v3_pre_topc @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B ) )
      | ~ ( v3_pre_topc @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ X0 ) @ sk_B )
      | ( r2_hidden @ ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ X0 ) @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['103','108'])).

thf('110',plain,
    ( ( ( k2_struct_0 @ sk_C )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ ( sk_D @ sk_A @ sk_C @ sk_D_1 ) ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['100','109'])).

thf('111',plain,(
    r1_tarski @ ( u1_pre_topc @ sk_B ) @ ( u1_pre_topc @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('113',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( ( k2_struct_0 @ sk_C )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ ( sk_D @ sk_A @ sk_C @ sk_D_1 ) ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['110','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('118',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('119',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( r2_hidden @ X11 @ ( u1_pre_topc @ X12 ) )
      | ( v3_pre_topc @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ X0 ) @ ( u1_pre_topc @ sk_A ) )
      | ( v3_pre_topc @ ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['117','122'])).

thf('124',plain,
    ( ( ( k2_struct_0 @ sk_C )
      = k1_xboole_0 )
    | ( v3_pre_topc @ ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ ( sk_D @ sk_A @ sk_C @ sk_D_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['116','123'])).

thf('125',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('126',plain,(
    ! [X17: $i,X18: $i,X20: $i,X21: $i] :
      ( ( zip_tseitin_1 @ X17 @ X20 @ X18 @ X21 )
      | ~ ( v3_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X18 ) @ X20 @ X17 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_pre_topc @ ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ X2 ) @ X1 @ X0 ) @ sk_A )
      | ( zip_tseitin_1 @ X0 @ X1 @ X2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( ( k2_struct_0 @ sk_C )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ ( sk_D @ sk_A @ sk_C @ sk_D_1 ) @ sk_D_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['124','127'])).

thf('129',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D @ X22 @ X23 @ X24 ) @ X24 @ X23 @ X22 )
      | ( v5_pre_topc @ X24 @ X22 @ X23 )
      | ~ ( zip_tseitin_2 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('130',plain,
    ( ( ( k2_struct_0 @ sk_C )
      = k1_xboole_0 )
    | ~ ( zip_tseitin_2 @ sk_D_1 @ sk_C @ sk_A )
    | ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( ( k2_struct_0 @ sk_C )
      = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['43','57'])).

thf('132',plain,
    ( ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C )
    | ( ( k2_struct_0 @ sk_C )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['130','131'])).

thf('133',plain,(
    ~ ( v5_pre_topc @ sk_D_1 @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['64','79'])).

thf('134',plain,
    ( ( k2_struct_0 @ sk_C )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('136',plain,(
    ! [X14: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['134','138'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('140',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('141',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('143',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    v2_struct_0 @ sk_C ),
    inference(demod,[status(thm)],['139','140','143'])).

thf('145',plain,(
    $false ),
    inference(demod,[status(thm)],['0','144'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZpiDOSsl1J
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:22:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.46/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.64  % Solved by: fo/fo7.sh
% 0.46/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.64  % done 367 iterations in 0.185s
% 0.46/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.64  % SZS output start Refutation
% 0.46/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.64  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.64  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.46/0.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.64  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.64  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.46/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.64  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.64  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.46/0.64  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.46/0.64  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.64  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.46/0.64  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.46/0.64  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.46/0.64  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.64  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.46/0.64  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.46/0.64  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.64  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.46/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.64  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.46/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.64  thf(t57_tmap_1, conjecture,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.46/0.64             ( l1_pre_topc @ B ) ) =>
% 0.46/0.64           ( ![C:$i]:
% 0.46/0.64             ( ( ( ~( v2_struct_0 @ C ) ) & ( v2_pre_topc @ C ) & 
% 0.46/0.64                 ( l1_pre_topc @ C ) ) =>
% 0.46/0.64               ( ( ( ( u1_struct_0 @ A ) = ( u1_struct_0 @ B ) ) & 
% 0.46/0.64                   ( r1_tarski @ ( u1_pre_topc @ B ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.46/0.64                 ( ![D:$i]:
% 0.46/0.64                   ( ( ( v1_funct_1 @ D ) & 
% 0.46/0.64                       ( v1_funct_2 @
% 0.46/0.64                         D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) & 
% 0.46/0.64                       ( v5_pre_topc @ D @ B @ C ) & 
% 0.46/0.64                       ( m1_subset_1 @
% 0.46/0.64                         D @ 
% 0.46/0.64                         ( k1_zfmisc_1 @
% 0.46/0.64                           ( k2_zfmisc_1 @
% 0.46/0.64                             ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) =>
% 0.46/0.64                     ( ( v1_funct_1 @ D ) & 
% 0.46/0.64                       ( v1_funct_2 @
% 0.46/0.64                         D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) ) & 
% 0.46/0.64                       ( v5_pre_topc @ D @ A @ C ) & 
% 0.46/0.64                       ( m1_subset_1 @
% 0.46/0.64                         D @ 
% 0.46/0.64                         ( k1_zfmisc_1 @
% 0.46/0.64                           ( k2_zfmisc_1 @
% 0.46/0.64                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.64    (~( ![A:$i]:
% 0.46/0.64        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.46/0.64            ( l1_pre_topc @ A ) ) =>
% 0.46/0.64          ( ![B:$i]:
% 0.46/0.64            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.46/0.64                ( l1_pre_topc @ B ) ) =>
% 0.46/0.64              ( ![C:$i]:
% 0.46/0.64                ( ( ( ~( v2_struct_0 @ C ) ) & ( v2_pre_topc @ C ) & 
% 0.46/0.64                    ( l1_pre_topc @ C ) ) =>
% 0.46/0.64                  ( ( ( ( u1_struct_0 @ A ) = ( u1_struct_0 @ B ) ) & 
% 0.46/0.64                      ( r1_tarski @ ( u1_pre_topc @ B ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.46/0.64                    ( ![D:$i]:
% 0.46/0.64                      ( ( ( v1_funct_1 @ D ) & 
% 0.46/0.64                          ( v1_funct_2 @
% 0.46/0.64                            D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) & 
% 0.46/0.64                          ( v5_pre_topc @ D @ B @ C ) & 
% 0.46/0.64                          ( m1_subset_1 @
% 0.46/0.64                            D @ 
% 0.46/0.64                            ( k1_zfmisc_1 @
% 0.46/0.64                              ( k2_zfmisc_1 @
% 0.46/0.64                                ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) =>
% 0.46/0.64                        ( ( v1_funct_1 @ D ) & 
% 0.46/0.64                          ( v1_funct_2 @
% 0.46/0.64                            D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) ) & 
% 0.46/0.64                          ( v5_pre_topc @ D @ A @ C ) & 
% 0.46/0.64                          ( m1_subset_1 @
% 0.46/0.64                            D @ 
% 0.46/0.64                            ( k1_zfmisc_1 @
% 0.46/0.64                              ( k2_zfmisc_1 @
% 0.46/0.64                                ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.46/0.64    inference('cnf.neg', [status(esa)], [t57_tmap_1])).
% 0.46/0.64  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(t55_tops_2, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( l1_pre_topc @ A ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( l1_pre_topc @ B ) =>
% 0.46/0.64           ( ![C:$i]:
% 0.46/0.64             ( ( ( m1_subset_1 @
% 0.46/0.64                   C @ 
% 0.46/0.64                   ( k1_zfmisc_1 @
% 0.46/0.64                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.46/0.64                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.64                 ( v1_funct_1 @ C ) ) =>
% 0.46/0.64               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.64                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.64                 ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.46/0.64                   ( ![D:$i]:
% 0.46/0.64                     ( ( m1_subset_1 @
% 0.46/0.64                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.46/0.64                       ( ( v3_pre_topc @ D @ B ) =>
% 0.46/0.64                         ( v3_pre_topc @
% 0.46/0.64                           ( k8_relset_1 @
% 0.46/0.64                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.46/0.64                           A ) ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_1, axiom,
% 0.46/0.64    (![B:$i,A:$i]:
% 0.46/0.64     ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.64         ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.64       ( zip_tseitin_0 @ B @ A ) ))).
% 0.46/0.64  thf('1', plain,
% 0.46/0.64      (![X15 : $i, X16 : $i]:
% 0.46/0.64         ((zip_tseitin_0 @ X15 @ X16) | ((k2_struct_0 @ X15) = (k1_xboole_0)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.64  thf('2', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_D_1 @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('3', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('4', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(d3_struct_0, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.46/0.64  thf('5', plain,
% 0.46/0.64      (![X10 : $i]:
% 0.46/0.64         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.64  thf('6', plain,
% 0.46/0.64      ((((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.64      inference('sup+', [status(thm)], ['4', '5'])).
% 0.46/0.64  thf('7', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(dt_l1_pre_topc, axiom,
% 0.46/0.64    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.46/0.64  thf('8', plain, (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.64  thf('9', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.64      inference('sup-', [status(thm)], ['7', '8'])).
% 0.46/0.64  thf('10', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['6', '9'])).
% 0.46/0.64  thf('11', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['3', '10'])).
% 0.46/0.64  thf('12', plain,
% 0.46/0.64      (![X10 : $i]:
% 0.46/0.64         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.64  thf('13', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['6', '9'])).
% 0.46/0.64  thf('14', plain,
% 0.46/0.64      ((((k2_struct_0 @ sk_B) = (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.64      inference('sup+', [status(thm)], ['12', '13'])).
% 0.46/0.64  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('16', plain,
% 0.46/0.64      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.64  thf('17', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.64      inference('sup-', [status(thm)], ['15', '16'])).
% 0.46/0.64  thf('18', plain, (((k2_struct_0 @ sk_B) = (k2_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['14', '17'])).
% 0.46/0.64  thf('19', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['11', '18'])).
% 0.46/0.64  thf('20', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_D_1 @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C))))),
% 0.46/0.64      inference('demod', [status(thm)], ['2', '19'])).
% 0.46/0.64  thf('21', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['11', '18'])).
% 0.46/0.64  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.46/0.64  thf(zf_stmt_3, axiom,
% 0.46/0.64    (![C:$i,B:$i,A:$i]:
% 0.46/0.64     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.46/0.64       ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.46/0.64         ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.46/0.64  thf(zf_stmt_5, axiom,
% 0.46/0.64    (![D:$i,C:$i,B:$i,A:$i]:
% 0.46/0.64     ( ( zip_tseitin_1 @ D @ C @ B @ A ) <=>
% 0.46/0.64       ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.46/0.64         ( ( v3_pre_topc @ D @ B ) =>
% 0.46/0.64           ( v3_pre_topc @
% 0.46/0.64             ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.46/0.64             A ) ) ) ))).thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $o).
% 0.46/0.64  thf(zf_stmt_7, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( l1_pre_topc @ A ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( l1_pre_topc @ B ) =>
% 0.46/0.64           ( ![C:$i]:
% 0.46/0.64             ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.64                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.64                 ( m1_subset_1 @
% 0.46/0.64                   C @ 
% 0.46/0.64                   ( k1_zfmisc_1 @
% 0.46/0.64                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.64               ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) ) ) ) ) ))).
% 0.46/0.64  thf('22', plain,
% 0.46/0.64      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.46/0.64         (~ (l1_pre_topc @ X26)
% 0.46/0.64          | ~ (zip_tseitin_0 @ X26 @ X27)
% 0.46/0.64          | (zip_tseitin_2 @ X28 @ X26 @ X27)
% 0.46/0.64          | ~ (m1_subset_1 @ X28 @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))))
% 0.46/0.64          | ~ (v1_funct_2 @ X28 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))
% 0.46/0.64          | ~ (v1_funct_1 @ X28)
% 0.46/0.64          | ~ (l1_pre_topc @ X27))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.46/0.64  thf('23', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X1 @ 
% 0.46/0.64             (k1_zfmisc_1 @ 
% 0.46/0.64              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.46/0.64          | ~ (l1_pre_topc @ sk_B)
% 0.46/0.64          | ~ (v1_funct_1 @ X1)
% 0.46/0.64          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.46/0.64          | (zip_tseitin_2 @ X1 @ X0 @ sk_B)
% 0.46/0.64          | ~ (zip_tseitin_0 @ X0 @ sk_B)
% 0.46/0.64          | ~ (l1_pre_topc @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['21', '22'])).
% 0.46/0.64  thf('24', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('25', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['11', '18'])).
% 0.46/0.64  thf('26', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X1 @ 
% 0.46/0.64             (k1_zfmisc_1 @ 
% 0.46/0.64              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.46/0.64          | ~ (v1_funct_1 @ X1)
% 0.46/0.64          | ~ (v1_funct_2 @ X1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 0.46/0.64          | (zip_tseitin_2 @ X1 @ X0 @ sk_B)
% 0.46/0.64          | ~ (zip_tseitin_0 @ X0 @ sk_B)
% 0.46/0.64          | ~ (l1_pre_topc @ X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.46/0.64  thf('27', plain,
% 0.46/0.64      ((~ (l1_pre_topc @ sk_C)
% 0.46/0.64        | ~ (zip_tseitin_0 @ sk_C @ sk_B)
% 0.46/0.64        | (zip_tseitin_2 @ sk_D_1 @ sk_C @ sk_B)
% 0.46/0.64        | ~ (v1_funct_2 @ sk_D_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C))
% 0.46/0.64        | ~ (v1_funct_1 @ sk_D_1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['20', '26'])).
% 0.46/0.64  thf('28', plain, ((l1_pre_topc @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('29', plain,
% 0.46/0.64      (![X10 : $i]:
% 0.46/0.64         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.64  thf('30', plain,
% 0.46/0.64      ((v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('31', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('32', plain,
% 0.46/0.64      ((v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C))),
% 0.46/0.64      inference('demod', [status(thm)], ['30', '31'])).
% 0.46/0.64  thf('33', plain,
% 0.46/0.64      (((v1_funct_2 @ sk_D_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C))
% 0.46/0.64        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.64      inference('sup+', [status(thm)], ['29', '32'])).
% 0.46/0.64  thf('34', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.64      inference('sup-', [status(thm)], ['15', '16'])).
% 0.46/0.64  thf('35', plain,
% 0.46/0.64      ((v1_funct_2 @ sk_D_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C))),
% 0.46/0.64      inference('demod', [status(thm)], ['33', '34'])).
% 0.46/0.64  thf('36', plain, ((v1_funct_1 @ sk_D_1)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('37', plain,
% 0.46/0.64      ((~ (zip_tseitin_0 @ sk_C @ sk_B)
% 0.46/0.64        | (zip_tseitin_2 @ sk_D_1 @ sk_C @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['27', '28', '35', '36'])).
% 0.46/0.64  thf('38', plain,
% 0.46/0.64      ((((k2_struct_0 @ sk_C) = (k1_xboole_0))
% 0.46/0.64        | (zip_tseitin_2 @ sk_D_1 @ sk_C @ sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['1', '37'])).
% 0.46/0.64  thf('39', plain, ((v5_pre_topc @ sk_D_1 @ sk_B @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('40', plain,
% 0.46/0.64      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.46/0.64         (~ (v5_pre_topc @ X24 @ X22 @ X23)
% 0.46/0.64          | (zip_tseitin_1 @ X25 @ X24 @ X23 @ X22)
% 0.46/0.64          | ~ (zip_tseitin_2 @ X24 @ X23 @ X22))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.64  thf('41', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (zip_tseitin_2 @ sk_D_1 @ sk_C @ sk_B)
% 0.46/0.64          | (zip_tseitin_1 @ X0 @ sk_D_1 @ sk_C @ sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['39', '40'])).
% 0.46/0.64  thf('42', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((k2_struct_0 @ sk_C) = (k1_xboole_0))
% 0.46/0.64          | (zip_tseitin_1 @ X0 @ sk_D_1 @ sk_C @ sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['38', '41'])).
% 0.46/0.64  thf('43', plain,
% 0.46/0.64      (![X15 : $i, X16 : $i]:
% 0.46/0.64         ((zip_tseitin_0 @ X15 @ X16) | ((k2_struct_0 @ X15) = (k1_xboole_0)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.64  thf('44', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_D_1 @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C))))),
% 0.46/0.64      inference('demod', [status(thm)], ['2', '19'])).
% 0.46/0.64  thf('45', plain,
% 0.46/0.64      (![X10 : $i]:
% 0.46/0.64         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.64  thf('46', plain,
% 0.46/0.64      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.46/0.64         (~ (l1_pre_topc @ X26)
% 0.46/0.64          | ~ (zip_tseitin_0 @ X26 @ X27)
% 0.46/0.64          | (zip_tseitin_2 @ X28 @ X26 @ X27)
% 0.46/0.64          | ~ (m1_subset_1 @ X28 @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))))
% 0.46/0.64          | ~ (v1_funct_2 @ X28 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))
% 0.46/0.64          | ~ (v1_funct_1 @ X28)
% 0.46/0.64          | ~ (l1_pre_topc @ X27))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.46/0.64  thf('47', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X2 @ 
% 0.46/0.64             (k1_zfmisc_1 @ 
% 0.46/0.64              (k2_zfmisc_1 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1))))
% 0.46/0.64          | ~ (l1_struct_0 @ X0)
% 0.46/0.64          | ~ (l1_pre_topc @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X2)
% 0.46/0.64          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.46/0.64          | (zip_tseitin_2 @ X2 @ X1 @ X0)
% 0.46/0.64          | ~ (zip_tseitin_0 @ X1 @ X0)
% 0.46/0.64          | ~ (l1_pre_topc @ X1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['45', '46'])).
% 0.46/0.64  thf('48', plain,
% 0.46/0.64      ((~ (l1_pre_topc @ sk_C)
% 0.46/0.64        | ~ (zip_tseitin_0 @ sk_C @ sk_A)
% 0.46/0.64        | (zip_tseitin_2 @ sk_D_1 @ sk_C @ sk_A)
% 0.46/0.64        | ~ (v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C))
% 0.46/0.64        | ~ (v1_funct_1 @ sk_D_1)
% 0.46/0.64        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.64        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['44', '47'])).
% 0.46/0.64  thf('49', plain, ((l1_pre_topc @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('50', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['6', '9'])).
% 0.46/0.64  thf('51', plain, (((k2_struct_0 @ sk_B) = (k2_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['14', '17'])).
% 0.46/0.64  thf('52', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['50', '51'])).
% 0.46/0.64  thf('53', plain,
% 0.46/0.64      ((v1_funct_2 @ sk_D_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C))),
% 0.46/0.64      inference('demod', [status(thm)], ['33', '34'])).
% 0.46/0.64  thf('54', plain, ((v1_funct_1 @ sk_D_1)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('56', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.64      inference('sup-', [status(thm)], ['15', '16'])).
% 0.46/0.64  thf('57', plain,
% 0.46/0.64      ((~ (zip_tseitin_0 @ sk_C @ sk_A)
% 0.46/0.64        | (zip_tseitin_2 @ sk_D_1 @ sk_C @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)],
% 0.46/0.64                ['48', '49', '52', '53', '54', '55', '56'])).
% 0.46/0.64  thf('58', plain,
% 0.46/0.64      ((((k2_struct_0 @ sk_C) = (k1_xboole_0))
% 0.46/0.64        | (zip_tseitin_2 @ sk_D_1 @ sk_C @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['43', '57'])).
% 0.46/0.64  thf('59', plain,
% 0.46/0.64      (![X17 : $i, X18 : $i, X20 : $i, X21 : $i]:
% 0.46/0.64         ((zip_tseitin_1 @ X17 @ X20 @ X18 @ X21) | (v3_pre_topc @ X17 @ X18))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.46/0.64  thf('60', plain,
% 0.46/0.64      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.46/0.64         (~ (zip_tseitin_1 @ (sk_D @ X22 @ X23 @ X24) @ X24 @ X23 @ X22)
% 0.46/0.64          | (v5_pre_topc @ X24 @ X22 @ X23)
% 0.46/0.64          | ~ (zip_tseitin_2 @ X24 @ X23 @ X22))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.64  thf('61', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         ((v3_pre_topc @ (sk_D @ X0 @ X1 @ X2) @ X1)
% 0.46/0.64          | ~ (zip_tseitin_2 @ X2 @ X1 @ X0)
% 0.46/0.64          | (v5_pre_topc @ X2 @ X0 @ X1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['59', '60'])).
% 0.46/0.64  thf('62', plain,
% 0.46/0.64      ((((k2_struct_0 @ sk_C) = (k1_xboole_0))
% 0.46/0.64        | (v5_pre_topc @ sk_D_1 @ sk_A @ sk_C)
% 0.46/0.64        | (v3_pre_topc @ (sk_D @ sk_A @ sk_C @ sk_D_1) @ sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['58', '61'])).
% 0.46/0.64  thf('63', plain,
% 0.46/0.64      ((~ (v1_funct_1 @ sk_D_1)
% 0.46/0.64        | ~ (v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C))
% 0.46/0.64        | ~ (v5_pre_topc @ sk_D_1 @ sk_A @ sk_C)
% 0.46/0.64        | ~ (m1_subset_1 @ sk_D_1 @ 
% 0.46/0.64             (k1_zfmisc_1 @ 
% 0.46/0.64              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C)))))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('64', plain,
% 0.46/0.64      ((~ (v5_pre_topc @ sk_D_1 @ sk_A @ sk_C))
% 0.46/0.64         <= (~ ((v5_pre_topc @ sk_D_1 @ sk_A @ sk_C)))),
% 0.46/0.64      inference('split', [status(esa)], ['63'])).
% 0.46/0.64  thf('65', plain,
% 0.46/0.64      ((v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C))),
% 0.46/0.64      inference('demod', [status(thm)], ['30', '31'])).
% 0.46/0.64  thf('66', plain,
% 0.46/0.64      ((~ (v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C)))
% 0.46/0.64         <= (~
% 0.46/0.64             ((v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.64               (u1_struct_0 @ sk_C))))),
% 0.46/0.64      inference('split', [status(esa)], ['63'])).
% 0.46/0.64  thf('67', plain,
% 0.46/0.64      (((v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['65', '66'])).
% 0.46/0.64  thf('68', plain, ((v1_funct_1 @ sk_D_1)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('69', plain, ((~ (v1_funct_1 @ sk_D_1)) <= (~ ((v1_funct_1 @ sk_D_1)))),
% 0.46/0.64      inference('split', [status(esa)], ['63'])).
% 0.46/0.64  thf('70', plain, (((v1_funct_1 @ sk_D_1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['68', '69'])).
% 0.46/0.64  thf('71', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_D_1 @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C))))),
% 0.46/0.64      inference('demod', [status(thm)], ['2', '19'])).
% 0.46/0.64  thf('72', plain,
% 0.46/0.64      (![X10 : $i]:
% 0.46/0.64         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.64  thf('73', plain,
% 0.46/0.64      ((~ (m1_subset_1 @ sk_D_1 @ 
% 0.46/0.64           (k1_zfmisc_1 @ 
% 0.46/0.64            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C)))))
% 0.46/0.64         <= (~
% 0.46/0.64             ((m1_subset_1 @ sk_D_1 @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C))))))),
% 0.46/0.64      inference('split', [status(esa)], ['63'])).
% 0.46/0.64  thf('74', plain,
% 0.46/0.64      (((~ (m1_subset_1 @ sk_D_1 @ 
% 0.46/0.64            (k1_zfmisc_1 @ 
% 0.46/0.64             (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C))))
% 0.46/0.64         | ~ (l1_struct_0 @ sk_A)))
% 0.46/0.64         <= (~
% 0.46/0.64             ((m1_subset_1 @ sk_D_1 @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C))))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['72', '73'])).
% 0.46/0.64  thf('75', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.64      inference('sup-', [status(thm)], ['15', '16'])).
% 0.46/0.64  thf('76', plain,
% 0.46/0.64      ((~ (m1_subset_1 @ sk_D_1 @ 
% 0.46/0.64           (k1_zfmisc_1 @ 
% 0.46/0.64            (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C)))))
% 0.46/0.64         <= (~
% 0.46/0.64             ((m1_subset_1 @ sk_D_1 @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C))))))),
% 0.46/0.64      inference('demod', [status(thm)], ['74', '75'])).
% 0.46/0.64  thf('77', plain,
% 0.46/0.64      (((m1_subset_1 @ sk_D_1 @ 
% 0.46/0.64         (k1_zfmisc_1 @ 
% 0.46/0.64          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C)))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['71', '76'])).
% 0.46/0.64  thf('78', plain,
% 0.46/0.64      (~ ((v5_pre_topc @ sk_D_1 @ sk_A @ sk_C)) | 
% 0.46/0.64       ~
% 0.46/0.64       ((m1_subset_1 @ sk_D_1 @ 
% 0.46/0.64         (k1_zfmisc_1 @ 
% 0.46/0.64          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C))))) | 
% 0.46/0.64       ~ ((v1_funct_1 @ sk_D_1)) | 
% 0.46/0.64       ~ ((v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C)))),
% 0.46/0.64      inference('split', [status(esa)], ['63'])).
% 0.46/0.64  thf('79', plain, (~ ((v5_pre_topc @ sk_D_1 @ sk_A @ sk_C))),
% 0.46/0.64      inference('sat_resolution*', [status(thm)], ['67', '70', '77', '78'])).
% 0.46/0.64  thf('80', plain, (~ (v5_pre_topc @ sk_D_1 @ sk_A @ sk_C)),
% 0.46/0.64      inference('simpl_trail', [status(thm)], ['64', '79'])).
% 0.46/0.64  thf('81', plain,
% 0.46/0.64      (((v3_pre_topc @ (sk_D @ sk_A @ sk_C @ sk_D_1) @ sk_C)
% 0.46/0.64        | ((k2_struct_0 @ sk_C) = (k1_xboole_0)))),
% 0.46/0.64      inference('clc', [status(thm)], ['62', '80'])).
% 0.46/0.64  thf('82', plain,
% 0.46/0.64      ((((k2_struct_0 @ sk_C) = (k1_xboole_0))
% 0.46/0.64        | (zip_tseitin_2 @ sk_D_1 @ sk_C @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['43', '57'])).
% 0.46/0.64  thf('83', plain,
% 0.46/0.64      (![X17 : $i, X18 : $i, X20 : $i, X21 : $i]:
% 0.46/0.64         ((zip_tseitin_1 @ X17 @ X20 @ X18 @ X21)
% 0.46/0.64          | (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18))))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.46/0.64  thf(t3_subset, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.64  thf('84', plain,
% 0.46/0.64      (![X3 : $i, X4 : $i]:
% 0.46/0.64         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.64  thf('85', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.64         ((zip_tseitin_1 @ X1 @ X3 @ X0 @ X2)
% 0.46/0.64          | (r1_tarski @ X1 @ (u1_struct_0 @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['83', '84'])).
% 0.46/0.64  thf('86', plain,
% 0.46/0.64      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.46/0.64         (~ (zip_tseitin_1 @ (sk_D @ X22 @ X23 @ X24) @ X24 @ X23 @ X22)
% 0.46/0.64          | (v5_pre_topc @ X24 @ X22 @ X23)
% 0.46/0.64          | ~ (zip_tseitin_2 @ X24 @ X23 @ X22))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.64  thf('87', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         ((r1_tarski @ (sk_D @ X0 @ X1 @ X2) @ (u1_struct_0 @ X1))
% 0.46/0.64          | ~ (zip_tseitin_2 @ X2 @ X1 @ X0)
% 0.46/0.64          | (v5_pre_topc @ X2 @ X0 @ X1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['85', '86'])).
% 0.46/0.64  thf('88', plain,
% 0.46/0.64      ((((k2_struct_0 @ sk_C) = (k1_xboole_0))
% 0.46/0.64        | (v5_pre_topc @ sk_D_1 @ sk_A @ sk_C)
% 0.46/0.64        | (r1_tarski @ (sk_D @ sk_A @ sk_C @ sk_D_1) @ (u1_struct_0 @ sk_C)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['82', '87'])).
% 0.46/0.64  thf('89', plain, (~ (v5_pre_topc @ sk_D_1 @ sk_A @ sk_C)),
% 0.46/0.64      inference('simpl_trail', [status(thm)], ['64', '79'])).
% 0.46/0.64  thf('90', plain,
% 0.46/0.64      (((r1_tarski @ (sk_D @ sk_A @ sk_C @ sk_D_1) @ (u1_struct_0 @ sk_C))
% 0.46/0.64        | ((k2_struct_0 @ sk_C) = (k1_xboole_0)))),
% 0.46/0.64      inference('clc', [status(thm)], ['88', '89'])).
% 0.46/0.64  thf('91', plain,
% 0.46/0.64      (![X3 : $i, X5 : $i]:
% 0.46/0.64         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.46/0.64      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.64  thf('92', plain,
% 0.46/0.64      ((((k2_struct_0 @ sk_C) = (k1_xboole_0))
% 0.46/0.64        | (m1_subset_1 @ (sk_D @ sk_A @ sk_C @ sk_D_1) @ 
% 0.46/0.64           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['90', '91'])).
% 0.46/0.64  thf('93', plain,
% 0.46/0.64      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.46/0.64          | (v3_pre_topc @ 
% 0.46/0.64             (k8_relset_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X18) @ X20 @ 
% 0.46/0.64              X17) @ 
% 0.46/0.64             X19)
% 0.46/0.64          | ~ (v3_pre_topc @ X17 @ X18)
% 0.46/0.64          | ~ (zip_tseitin_1 @ X17 @ X20 @ X18 @ X19))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.46/0.64  thf('94', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((k2_struct_0 @ sk_C) = (k1_xboole_0))
% 0.46/0.64          | ~ (zip_tseitin_1 @ (sk_D @ sk_A @ sk_C @ sk_D_1) @ X1 @ sk_C @ X0)
% 0.46/0.64          | ~ (v3_pre_topc @ (sk_D @ sk_A @ sk_C @ sk_D_1) @ sk_C)
% 0.46/0.64          | (v3_pre_topc @ 
% 0.46/0.64             (k8_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_C) @ X1 @ 
% 0.46/0.64              (sk_D @ sk_A @ sk_C @ sk_D_1)) @ 
% 0.46/0.64             X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['92', '93'])).
% 0.46/0.64  thf('95', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((k2_struct_0 @ sk_C) = (k1_xboole_0))
% 0.46/0.64          | (v3_pre_topc @ 
% 0.46/0.64             (k8_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_C) @ X1 @ 
% 0.46/0.64              (sk_D @ sk_A @ sk_C @ sk_D_1)) @ 
% 0.46/0.64             X0)
% 0.46/0.64          | ~ (zip_tseitin_1 @ (sk_D @ sk_A @ sk_C @ sk_D_1) @ X1 @ sk_C @ X0)
% 0.46/0.64          | ((k2_struct_0 @ sk_C) = (k1_xboole_0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['81', '94'])).
% 0.46/0.64  thf('96', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (zip_tseitin_1 @ (sk_D @ sk_A @ sk_C @ sk_D_1) @ X1 @ sk_C @ X0)
% 0.46/0.64          | (v3_pre_topc @ 
% 0.46/0.64             (k8_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_C) @ X1 @ 
% 0.46/0.64              (sk_D @ sk_A @ sk_C @ sk_D_1)) @ 
% 0.46/0.64             X0)
% 0.46/0.64          | ((k2_struct_0 @ sk_C) = (k1_xboole_0)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['95'])).
% 0.46/0.64  thf('97', plain,
% 0.46/0.64      ((((k2_struct_0 @ sk_C) = (k1_xboole_0))
% 0.46/0.64        | ((k2_struct_0 @ sk_C) = (k1_xboole_0))
% 0.46/0.64        | (v3_pre_topc @ 
% 0.46/0.64           (k8_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C) @ 
% 0.46/0.64            sk_D_1 @ (sk_D @ sk_A @ sk_C @ sk_D_1)) @ 
% 0.46/0.64           sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['42', '96'])).
% 0.46/0.64  thf('98', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['11', '18'])).
% 0.46/0.64  thf('99', plain,
% 0.46/0.64      ((((k2_struct_0 @ sk_C) = (k1_xboole_0))
% 0.46/0.64        | ((k2_struct_0 @ sk_C) = (k1_xboole_0))
% 0.46/0.64        | (v3_pre_topc @ 
% 0.46/0.64           (k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C) @ 
% 0.46/0.64            sk_D_1 @ (sk_D @ sk_A @ sk_C @ sk_D_1)) @ 
% 0.46/0.64           sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['97', '98'])).
% 0.46/0.64  thf('100', plain,
% 0.46/0.64      (((v3_pre_topc @ 
% 0.46/0.64         (k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C) @ sk_D_1 @ 
% 0.46/0.64          (sk_D @ sk_A @ sk_C @ sk_D_1)) @ 
% 0.46/0.64         sk_B)
% 0.46/0.64        | ((k2_struct_0 @ sk_C) = (k1_xboole_0)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['99'])).
% 0.46/0.64  thf('101', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_D_1 @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C))))),
% 0.46/0.64      inference('demod', [status(thm)], ['2', '19'])).
% 0.46/0.64  thf(dt_k8_relset_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.64       ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.46/0.64  thf('102', plain,
% 0.46/0.64      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 0.46/0.64          | (m1_subset_1 @ (k8_relset_1 @ X7 @ X8 @ X6 @ X9) @ 
% 0.46/0.64             (k1_zfmisc_1 @ X7)))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k8_relset_1])).
% 0.46/0.64  thf('103', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (m1_subset_1 @ 
% 0.46/0.64          (k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C) @ 
% 0.46/0.64           sk_D_1 @ X0) @ 
% 0.46/0.64          (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['101', '102'])).
% 0.46/0.64  thf('104', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['11', '18'])).
% 0.46/0.64  thf(d5_pre_topc, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( l1_pre_topc @ A ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.64           ( ( v3_pre_topc @ B @ A ) <=>
% 0.46/0.64             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.46/0.64  thf('105', plain,
% 0.46/0.64      (![X11 : $i, X12 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.46/0.64          | ~ (v3_pre_topc @ X11 @ X12)
% 0.46/0.64          | (r2_hidden @ X11 @ (u1_pre_topc @ X12))
% 0.46/0.64          | ~ (l1_pre_topc @ X12))),
% 0.46/0.64      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.46/0.64  thf('106', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.46/0.64          | ~ (l1_pre_topc @ sk_B)
% 0.46/0.64          | (r2_hidden @ X0 @ (u1_pre_topc @ sk_B))
% 0.46/0.64          | ~ (v3_pre_topc @ X0 @ sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['104', '105'])).
% 0.46/0.64  thf('107', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('108', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.46/0.64          | (r2_hidden @ X0 @ (u1_pre_topc @ sk_B))
% 0.46/0.64          | ~ (v3_pre_topc @ X0 @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['106', '107'])).
% 0.46/0.64  thf('109', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v3_pre_topc @ 
% 0.46/0.64             (k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C) @ 
% 0.46/0.64              sk_D_1 @ X0) @ 
% 0.46/0.64             sk_B)
% 0.46/0.64          | (r2_hidden @ 
% 0.46/0.64             (k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C) @ 
% 0.46/0.64              sk_D_1 @ X0) @ 
% 0.46/0.64             (u1_pre_topc @ sk_B)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['103', '108'])).
% 0.46/0.64  thf('110', plain,
% 0.46/0.64      ((((k2_struct_0 @ sk_C) = (k1_xboole_0))
% 0.46/0.64        | (r2_hidden @ 
% 0.46/0.64           (k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C) @ 
% 0.46/0.64            sk_D_1 @ (sk_D @ sk_A @ sk_C @ sk_D_1)) @ 
% 0.46/0.64           (u1_pre_topc @ sk_B)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['100', '109'])).
% 0.46/0.64  thf('111', plain,
% 0.46/0.64      ((r1_tarski @ (u1_pre_topc @ sk_B) @ (u1_pre_topc @ sk_A))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('112', plain,
% 0.46/0.64      (![X3 : $i, X5 : $i]:
% 0.46/0.64         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.46/0.64      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.64  thf('113', plain,
% 0.46/0.64      ((m1_subset_1 @ (u1_pre_topc @ sk_B) @ 
% 0.46/0.64        (k1_zfmisc_1 @ (u1_pre_topc @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['111', '112'])).
% 0.46/0.64  thf(l3_subset_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.64       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.46/0.64  thf('114', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X0 @ X1)
% 0.46/0.64          | (r2_hidden @ X0 @ X2)
% 0.46/0.64          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.46/0.64      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.46/0.64  thf('115', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((r2_hidden @ X0 @ (u1_pre_topc @ sk_A))
% 0.46/0.64          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_B)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['113', '114'])).
% 0.46/0.64  thf('116', plain,
% 0.46/0.64      ((((k2_struct_0 @ sk_C) = (k1_xboole_0))
% 0.46/0.64        | (r2_hidden @ 
% 0.46/0.64           (k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C) @ 
% 0.46/0.64            sk_D_1 @ (sk_D @ sk_A @ sk_C @ sk_D_1)) @ 
% 0.46/0.64           (u1_pre_topc @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['110', '115'])).
% 0.46/0.64  thf('117', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (m1_subset_1 @ 
% 0.46/0.64          (k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C) @ 
% 0.46/0.64           sk_D_1 @ X0) @ 
% 0.46/0.64          (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['101', '102'])).
% 0.46/0.64  thf('118', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['50', '51'])).
% 0.46/0.64  thf('119', plain,
% 0.46/0.64      (![X11 : $i, X12 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.46/0.64          | ~ (r2_hidden @ X11 @ (u1_pre_topc @ X12))
% 0.46/0.64          | (v3_pre_topc @ X11 @ X12)
% 0.46/0.64          | ~ (l1_pre_topc @ X12))),
% 0.46/0.64      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.46/0.64  thf('120', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.46/0.64          | ~ (l1_pre_topc @ sk_A)
% 0.46/0.64          | (v3_pre_topc @ X0 @ sk_A)
% 0.46/0.64          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['118', '119'])).
% 0.46/0.64  thf('121', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('122', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.46/0.64          | (v3_pre_topc @ X0 @ sk_A)
% 0.46/0.64          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_A)))),
% 0.46/0.64      inference('demod', [status(thm)], ['120', '121'])).
% 0.46/0.64  thf('123', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (r2_hidden @ 
% 0.46/0.64             (k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C) @ 
% 0.46/0.64              sk_D_1 @ X0) @ 
% 0.46/0.64             (u1_pre_topc @ sk_A))
% 0.46/0.64          | (v3_pre_topc @ 
% 0.46/0.64             (k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C) @ 
% 0.46/0.64              sk_D_1 @ X0) @ 
% 0.46/0.64             sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['117', '122'])).
% 0.46/0.64  thf('124', plain,
% 0.46/0.64      ((((k2_struct_0 @ sk_C) = (k1_xboole_0))
% 0.46/0.64        | (v3_pre_topc @ 
% 0.46/0.64           (k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_C) @ 
% 0.46/0.64            sk_D_1 @ (sk_D @ sk_A @ sk_C @ sk_D_1)) @ 
% 0.46/0.64           sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['116', '123'])).
% 0.46/0.64  thf('125', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['50', '51'])).
% 0.46/0.64  thf('126', plain,
% 0.46/0.64      (![X17 : $i, X18 : $i, X20 : $i, X21 : $i]:
% 0.46/0.64         ((zip_tseitin_1 @ X17 @ X20 @ X18 @ X21)
% 0.46/0.64          | ~ (v3_pre_topc @ 
% 0.46/0.64               (k8_relset_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X18) @ 
% 0.46/0.64                X20 @ X17) @ 
% 0.46/0.64               X21))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.46/0.64  thf('127', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (v3_pre_topc @ 
% 0.46/0.64             (k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ X2) @ X1 @ X0) @ 
% 0.46/0.64             sk_A)
% 0.46/0.64          | (zip_tseitin_1 @ X0 @ X1 @ X2 @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['125', '126'])).
% 0.46/0.64  thf('128', plain,
% 0.46/0.64      ((((k2_struct_0 @ sk_C) = (k1_xboole_0))
% 0.46/0.64        | (zip_tseitin_1 @ (sk_D @ sk_A @ sk_C @ sk_D_1) @ sk_D_1 @ sk_C @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['124', '127'])).
% 0.46/0.64  thf('129', plain,
% 0.46/0.64      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.46/0.64         (~ (zip_tseitin_1 @ (sk_D @ X22 @ X23 @ X24) @ X24 @ X23 @ X22)
% 0.46/0.64          | (v5_pre_topc @ X24 @ X22 @ X23)
% 0.46/0.64          | ~ (zip_tseitin_2 @ X24 @ X23 @ X22))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.64  thf('130', plain,
% 0.46/0.64      ((((k2_struct_0 @ sk_C) = (k1_xboole_0))
% 0.46/0.64        | ~ (zip_tseitin_2 @ sk_D_1 @ sk_C @ sk_A)
% 0.46/0.64        | (v5_pre_topc @ sk_D_1 @ sk_A @ sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['128', '129'])).
% 0.46/0.64  thf('131', plain,
% 0.46/0.64      ((((k2_struct_0 @ sk_C) = (k1_xboole_0))
% 0.46/0.64        | (zip_tseitin_2 @ sk_D_1 @ sk_C @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['43', '57'])).
% 0.46/0.64  thf('132', plain,
% 0.46/0.64      (((v5_pre_topc @ sk_D_1 @ sk_A @ sk_C)
% 0.46/0.64        | ((k2_struct_0 @ sk_C) = (k1_xboole_0)))),
% 0.46/0.64      inference('clc', [status(thm)], ['130', '131'])).
% 0.46/0.64  thf('133', plain, (~ (v5_pre_topc @ sk_D_1 @ sk_A @ sk_C)),
% 0.46/0.64      inference('simpl_trail', [status(thm)], ['64', '79'])).
% 0.46/0.64  thf('134', plain, (((k2_struct_0 @ sk_C) = (k1_xboole_0))),
% 0.46/0.64      inference('clc', [status(thm)], ['132', '133'])).
% 0.46/0.64  thf('135', plain,
% 0.46/0.64      (![X10 : $i]:
% 0.46/0.64         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.64  thf(fc2_struct_0, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.64       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.46/0.64  thf('136', plain,
% 0.46/0.64      (![X14 : $i]:
% 0.46/0.64         (~ (v1_xboole_0 @ (u1_struct_0 @ X14))
% 0.46/0.64          | ~ (l1_struct_0 @ X14)
% 0.46/0.64          | (v2_struct_0 @ X14))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.46/0.64  thf('137', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.46/0.64          | ~ (l1_struct_0 @ X0)
% 0.46/0.64          | (v2_struct_0 @ X0)
% 0.46/0.64          | ~ (l1_struct_0 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['135', '136'])).
% 0.46/0.64  thf('138', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v2_struct_0 @ X0)
% 0.46/0.64          | ~ (l1_struct_0 @ X0)
% 0.46/0.64          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['137'])).
% 0.46/0.64  thf('139', plain,
% 0.46/0.64      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.46/0.64        | ~ (l1_struct_0 @ sk_C)
% 0.46/0.64        | (v2_struct_0 @ sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['134', '138'])).
% 0.46/0.64  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.46/0.64  thf('140', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.64      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.64  thf('141', plain, ((l1_pre_topc @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('142', plain,
% 0.46/0.64      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.64  thf('143', plain, ((l1_struct_0 @ sk_C)),
% 0.46/0.64      inference('sup-', [status(thm)], ['141', '142'])).
% 0.46/0.64  thf('144', plain, ((v2_struct_0 @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['139', '140', '143'])).
% 0.46/0.64  thf('145', plain, ($false), inference('demod', [status(thm)], ['0', '144'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.46/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
