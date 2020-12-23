%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.17RrHZ5eJK

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:40 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :  304 (3590 expanded)
%              Number of leaves         :   40 (1065 expanded)
%              Depth                    :   49
%              Number of atoms          : 4401 (92677 expanded)
%              Number of equality atoms :   65 (1694 expanded)
%              Maximal formula depth    :   23 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k4_tmap_1_type,type,(
    k4_tmap_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t96_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
             => ( ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_hidden @ D @ ( u1_struct_0 @ B ) )
                     => ( D
                        = ( k1_funct_1 @ C @ D ) ) ) )
               => ( r2_funct_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k4_tmap_1 @ A @ B ) @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
               => ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_hidden @ D @ ( u1_struct_0 @ B ) )
                       => ( D
                          = ( k1_funct_1 @ C @ D ) ) ) )
                 => ( r2_funct_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k4_tmap_1 @ A @ B ) @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t96_tmap_1])).

thf('0',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_pre_topc @ B @ A ) )
     => ( ( v1_funct_1 @ ( k4_tmap_1 @ A @ B ) )
        & ( v1_funct_2 @ ( k4_tmap_1 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ ( k4_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X33 @ X32 )
      | ( m1_subset_1 @ ( k4_tmap_1 @ X32 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X32 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_tmap_1])).

thf('3',plain,
    ( ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_funct_2 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( v1_funct_2 @ X7 @ X8 @ X9 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_funct_2 @ X10 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ( X7 = X10 )
      | ~ ( r2_funct_2 @ X8 @ X9 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,
    ( ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_C
      = ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X33 @ X32 )
      | ( v1_funct_1 @ ( k4_tmap_1 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_tmap_1])).

thf('18',plain,
    ( ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X33 @ X32 )
      | ( v1_funct_2 @ ( k4_tmap_1 @ X32 @ X33 ) @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_tmap_1])).

thf('26',plain,
    ( ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_C
      = ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['15','23','31'])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('33',plain,(
    ! [X34: $i] :
      ( ( m1_pre_topc @ X34 @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('34',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t59_tmap_1,axiom,(
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
                & ( m1_pre_topc @ C @ B ) )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) )
                     => ( ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                           => ( ( r2_hidden @ F @ ( u1_struct_0 @ C ) )
                             => ( ( k3_funct_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ D @ F )
                                = ( k1_funct_1 @ E @ F ) ) ) )
                       => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) )).

thf('36',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( v2_struct_0 @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X37 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X37 ) ) ) )
      | ( r2_hidden @ ( sk_F @ X38 @ X36 @ X39 @ X35 @ X37 ) @ ( u1_struct_0 @ X39 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X37 ) @ ( k2_tmap_1 @ X35 @ X37 @ X36 @ X39 ) @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X37 ) ) ) )
      | ~ ( v1_funct_2 @ X38 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X37 ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_pre_topc @ X39 @ X35 )
      | ( v2_struct_0 @ X39 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t59_tmap_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_F @ X1 @ sk_C @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('43',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( l1_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('44',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('48',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('49',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_F @ X1 @ sk_C @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['37','38','39','40','41','46','52'])).

thf('54',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tmap_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) )
        & ( l1_struct_0 @ D ) )
     => ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) )
        & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('56',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ~ ( v1_funct_2 @ X28 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( l1_struct_0 @ X30 )
      | ~ ( l1_struct_0 @ X29 )
      | ~ ( l1_struct_0 @ X31 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ X29 @ X30 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['44','45'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('59',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('60',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('63',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['57','60','63','64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ~ ( v1_funct_2 @ X28 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( l1_struct_0 @ X30 )
      | ~ ( l1_struct_0 @ X29 )
      | ~ ( l1_struct_0 @ X31 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X29 @ X30 @ X28 @ X31 ) @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['58','59'])).

thf('71',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['61','62'])).

thf('72',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['69','70','71','72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ~ ( v1_funct_2 @ X28 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( l1_struct_0 @ X30 )
      | ~ ( l1_struct_0 @ X29 )
      | ~ ( l1_struct_0 @ X31 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X29 @ X30 @ X28 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X30 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['58','59'])).

thf('79',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['61','62'])).

thf('80',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['77','78','79','80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('84',plain,
    ( ~ ( l1_struct_0 @ sk_B_1 )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_C
      = ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['58','59'])).

thf('86',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_C
      = ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X34: $i] :
      ( ( m1_pre_topc @ X34 @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('88',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tmap_1,axiom,(
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
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                 => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ D @ ( k3_tmap_1 @ A @ B @ C @ C @ D ) ) ) ) ) ) )).

thf('89',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( v2_struct_0 @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X40 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X40 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X40 ) @ X41 @ ( k3_tmap_1 @ X43 @ X40 @ X42 @ X42 @ X41 ) )
      | ~ ( m1_pre_topc @ X42 @ X43 )
      | ( v2_struct_0 @ X42 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 )
      | ( v2_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t74_tmap_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_pre_topc @ sk_B_1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_C ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_pre_topc @ sk_B_1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91','92','93','94'])).

thf('96',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( v2_pre_topc @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['87','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['44','45'])).

thf('98',plain,(
    ! [X34: $i] :
      ( ( m1_pre_topc @ X34 @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('99',plain,(
    ! [X34: $i] :
      ( ( m1_pre_topc @ X34 @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('100',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ! [D: $i] :
                  ( ( m1_pre_topc @ D @ A )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( m1_pre_topc @ D @ C )
                       => ( ( k3_tmap_1 @ A @ B @ C @ D @ E )
                          = ( k2_partfun1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) )).

thf('101',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( m1_pre_topc @ X24 @ X25 )
      | ~ ( m1_pre_topc @ X24 @ X26 )
      | ( ( k3_tmap_1 @ X25 @ X23 @ X26 @ X24 @ X27 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X23 ) @ X27 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( v1_funct_2 @ X27 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_B_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_tmap_1 @ X0 @ sk_A @ sk_B_1 @ X1 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_B_1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_B_1 @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_A @ sk_B_1 @ X1 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_B_1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['102','103','104','105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ( ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['99','107'])).

thf('109',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['44','45'])).

thf('110',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['44','45'])).

thf('111',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ( ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['108','109','110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['98','113'])).

thf('115',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['44','45'])).

thf('116',plain,(
    ! [X34: $i] :
      ( ( m1_pre_topc @ X34 @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('117',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tmap_1,axiom,(
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
             => ! [D: $i] :
                  ( ( m1_pre_topc @ D @ A )
                 => ( ( k2_tmap_1 @ A @ B @ C @ D )
                    = ( k2_partfun1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( u1_struct_0 @ D ) ) ) ) ) ) ) )).

thf('118',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_pre_topc @ X20 @ X21 )
      | ( ( k2_tmap_1 @ X21 @ X19 @ X22 @ X20 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X19 ) @ X22 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v1_funct_2 @ X22 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('121',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['44','45'])).

thf('122',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['119','120','121','122','123','124','125'])).

thf('127',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['116','126'])).

thf('128',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['44','45'])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['129','130'])).

thf('132',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_C )
      = ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['114','115','133'])).

thf('135',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_C )
      = ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['134','135'])).

thf('137',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_C )
    = ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) ),
    inference(clc,[status(thm)],['136','137'])).

thf('139',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['44','45'])).

thf('140',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('141',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['96','97','138','139','140'])).

thf('142',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['142','143'])).

thf('145',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) ),
    inference(clc,[status(thm)],['144','145'])).

thf('147',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_C
      = ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['86','146'])).

thf('148',plain,
    ( ~ ( l1_struct_0 @ sk_B_1 )
    | ( sk_C
      = ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['74','147'])).

thf('149',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['58','59'])).

thf('150',plain,
    ( ( sk_C
      = ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,
    ( ~ ( l1_struct_0 @ sk_B_1 )
    | ( sk_C
      = ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['66','150'])).

thf('152',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['58','59'])).

thf('153',plain,
    ( sk_C
    = ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('155',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('156',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','153','154','155'])).

thf('157',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','157'])).

thf('159',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['44','45'])).

thf('160',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['158','159'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('162',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X34: $i] :
      ( ( m1_pre_topc @ X34 @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('164',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    ! [X34: $i] :
      ( ( m1_pre_topc @ X34 @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('166',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('167',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( v2_struct_0 @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X37 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X37 ) ) ) )
      | ( m1_subset_1 @ ( sk_F @ X38 @ X36 @ X39 @ X35 @ X37 ) @ ( u1_struct_0 @ X35 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X37 ) @ ( k2_tmap_1 @ X35 @ X37 @ X36 @ X39 ) @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X37 ) ) ) )
      | ~ ( v1_funct_2 @ X38 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X37 ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_pre_topc @ X39 @ X35 )
      | ( v2_struct_0 @ X39 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t59_tmap_1])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( m1_subset_1 @ ( sk_F @ X1 @ sk_C @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['44','45'])).

thf('175',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( m1_subset_1 @ ( sk_F @ X1 @ sk_C @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['169','170','171','172','173','174','175'])).

thf('177',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['166','176'])).

thf('178',plain,
    ( sk_C
    = ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('179',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('180',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('181',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['177','178','179','180'])).

thf('182',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['181'])).

thf('183',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['165','182'])).

thf('184',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['44','45'])).

thf('185',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['183','184'])).

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

thf('186',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( m1_pre_topc @ X16 @ X17 )
      | ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_pre_topc])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['187'])).

thf('189',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['164','188'])).

thf('190',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['189','190'])).

thf('192',plain,
    ( ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['191'])).

thf('193',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('194',plain,(
    ! [X50: $i] :
      ( ~ ( r2_hidden @ X50 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( X50
        = ( k1_funct_1 @ sk_C @ X50 ) )
      | ~ ( m1_subset_1 @ X50 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['192','195'])).

thf('197',plain,
    ( ( ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['196'])).

thf('198',plain,
    ( ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['191'])).

thf('199',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['158','159'])).

thf(t95_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_hidden @ C @ ( u1_struct_0 @ B ) )
               => ( ( k1_funct_1 @ ( k4_tmap_1 @ A @ B ) @ C )
                  = C ) ) ) ) ) )).

thf('200',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( v2_struct_0 @ X47 )
      | ~ ( m1_pre_topc @ X47 @ X48 )
      | ~ ( r2_hidden @ X49 @ ( u1_struct_0 @ X47 ) )
      | ( ( k1_funct_1 @ ( k4_tmap_1 @ X48 @ X47 ) @ X49 )
        = X49 )
      | ~ ( m1_subset_1 @ X49 @ ( u1_struct_0 @ X48 ) )
      | ~ ( l1_pre_topc @ X48 )
      | ~ ( v2_pre_topc @ X48 )
      | ( v2_struct_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t95_tmap_1])).

thf('201',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k1_funct_1 @ ( k4_tmap_1 @ X0 @ sk_B_1 ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) )
        = ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) )
      | ~ ( m1_pre_topc @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_B_1 @ X0 )
      | ( ( k1_funct_1 @ ( k4_tmap_1 @ X0 @ sk_B_1 ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) )
        = ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['201'])).

thf('203',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) )
      = ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['198','202'])).

thf('204',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) )
      = ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['203','204','205','206'])).

thf('208',plain,
    ( ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) )
      = ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['207'])).

thf('209',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['183','184'])).

thf('210',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( ( k3_funct_2 @ A @ B @ C @ D )
        = ( k1_funct_1 @ C @ D ) ) ) )).

thf('211',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ~ ( v1_funct_2 @ X3 @ X4 @ X5 )
      | ~ ( v1_funct_1 @ X3 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X6 @ X4 )
      | ( ( k3_funct_2 @ X4 @ X5 @ X3 @ X6 )
        = ( k1_funct_1 @ X3 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('212',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['212','213','214'])).

thf('216',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['209','215'])).

thf('217',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( v2_struct_0 @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X37 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X37 ) ) ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X37 ) @ X36 @ ( sk_F @ X38 @ X36 @ X39 @ X35 @ X37 ) )
       != ( k1_funct_1 @ X38 @ ( sk_F @ X38 @ X36 @ X39 @ X35 @ X37 ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X37 ) @ ( k2_tmap_1 @ X35 @ X37 @ X36 @ X39 ) @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X37 ) ) ) )
      | ~ ( v1_funct_2 @ X38 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X37 ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_pre_topc @ X39 @ X35 )
      | ( v2_struct_0 @ X39 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t59_tmap_1])).

thf('218',plain,
    ( ( ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) )
     != ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( v2_pre_topc @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['216','217'])).

thf('219',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('222',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('223',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('224',plain,
    ( sk_C
    = ( k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1 ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('225',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['44','45'])).

thf('229',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('230',plain,
    ( ( ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) )
     != ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['218','219','220','221','222','223','224','225','226','227','228','229'])).

thf('231',plain,
    ( ~ ( m1_pre_topc @ sk_B_1 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) )
     != ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['230'])).

thf('232',plain,
    ( ( ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) )
     != ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['208','231'])).

thf('233',plain,
    ( ~ ( m1_pre_topc @ sk_B_1 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) )
     != ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['232'])).

thf('234',plain,
    ( ( ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A )
     != ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['197','233'])).

thf('235',plain,
    ( ~ ( m1_pre_topc @ sk_B_1 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['234'])).

thf('236',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['163','235'])).

thf('237',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['44','45'])).

thf('238',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['236','237'])).

thf('239',plain,
    ( ( sk_C
      = ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['15','23','31'])).

thf('240',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_C
      = ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['238','239'])).

thf('241',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['240','241'])).

thf('243',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( v1_funct_2 @ X7 @ X8 @ X9 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_funct_2 @ X10 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ( r2_funct_2 @ X8 @ X9 @ X7 @ X10 )
      | ( X7 != X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('245',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_funct_2 @ X8 @ X9 @ X10 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_funct_2 @ X10 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(simplify,[status(thm)],['244'])).

thf('246',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['243','245'])).

thf('247',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['246','247','248'])).

thf('250',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['242','249'])).

thf('251',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['250','251'])).

thf('253',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['252','253'])).

thf('255',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['162','254'])).

thf('256',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['255','256'])).

thf('258',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['257','258'])).

thf('260',plain,
    ( sk_C
    = ( k4_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['32','259'])).

thf('261',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['246','247','248'])).

thf('262',plain,(
    $false ),
    inference(demod,[status(thm)],['0','260','261'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.17RrHZ5eJK
% 0.14/0.37  % Computer   : n013.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 19:22:40 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 1.06/1.29  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.06/1.29  % Solved by: fo/fo7.sh
% 1.06/1.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.06/1.29  % done 1070 iterations in 0.800s
% 1.06/1.29  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.06/1.29  % SZS output start Refutation
% 1.06/1.29  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i > $i).
% 1.06/1.29  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.06/1.29  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 1.06/1.29  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.06/1.29  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.06/1.29  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 1.06/1.29  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.06/1.29  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 1.06/1.29  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.06/1.29  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.06/1.29  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.06/1.29  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.06/1.29  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.06/1.29  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.06/1.29  thf(sk_C_type, type, sk_C: $i).
% 1.06/1.29  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.06/1.29  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.06/1.29  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 1.06/1.29  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.06/1.29  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 1.06/1.29  thf(k4_tmap_1_type, type, k4_tmap_1: $i > $i > $i).
% 1.06/1.29  thf(sk_A_type, type, sk_A: $i).
% 1.06/1.29  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.06/1.29  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.06/1.29  thf(t96_tmap_1, conjecture,
% 1.06/1.29    (![A:$i]:
% 1.06/1.29     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.29       ( ![B:$i]:
% 1.06/1.29         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.06/1.29           ( ![C:$i]:
% 1.06/1.29             ( ( ( v1_funct_1 @ C ) & 
% 1.06/1.29                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 1.06/1.29                 ( m1_subset_1 @
% 1.06/1.29                   C @ 
% 1.06/1.29                   ( k1_zfmisc_1 @
% 1.06/1.29                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 1.06/1.29               ( ( ![D:$i]:
% 1.06/1.29                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 1.06/1.29                     ( ( r2_hidden @ D @ ( u1_struct_0 @ B ) ) =>
% 1.06/1.29                       ( ( D ) = ( k1_funct_1 @ C @ D ) ) ) ) ) =>
% 1.06/1.29                 ( r2_funct_2 @
% 1.06/1.29                   ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.06/1.29                   ( k4_tmap_1 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 1.06/1.29  thf(zf_stmt_0, negated_conjecture,
% 1.06/1.29    (~( ![A:$i]:
% 1.06/1.29        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.06/1.29            ( l1_pre_topc @ A ) ) =>
% 1.06/1.29          ( ![B:$i]:
% 1.06/1.29            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.06/1.29              ( ![C:$i]:
% 1.06/1.29                ( ( ( v1_funct_1 @ C ) & 
% 1.06/1.29                    ( v1_funct_2 @
% 1.06/1.29                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 1.06/1.29                    ( m1_subset_1 @
% 1.06/1.29                      C @ 
% 1.06/1.29                      ( k1_zfmisc_1 @
% 1.06/1.29                        ( k2_zfmisc_1 @
% 1.06/1.29                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 1.06/1.29                  ( ( ![D:$i]:
% 1.06/1.29                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 1.06/1.29                        ( ( r2_hidden @ D @ ( u1_struct_0 @ B ) ) =>
% 1.06/1.29                          ( ( D ) = ( k1_funct_1 @ C @ D ) ) ) ) ) =>
% 1.06/1.29                    ( r2_funct_2 @
% 1.06/1.29                      ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.06/1.29                      ( k4_tmap_1 @ A @ B ) @ C ) ) ) ) ) ) ) )),
% 1.06/1.29    inference('cnf.neg', [status(esa)], [t96_tmap_1])).
% 1.06/1.29  thf('0', plain,
% 1.06/1.29      (~ (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.29          (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('1', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf(dt_k4_tmap_1, axiom,
% 1.06/1.29    (![A:$i,B:$i]:
% 1.06/1.29     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.06/1.29         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.06/1.29       ( ( v1_funct_1 @ ( k4_tmap_1 @ A @ B ) ) & 
% 1.06/1.29         ( v1_funct_2 @
% 1.06/1.29           ( k4_tmap_1 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 1.06/1.29         ( m1_subset_1 @
% 1.06/1.29           ( k4_tmap_1 @ A @ B ) @ 
% 1.06/1.29           ( k1_zfmisc_1 @
% 1.06/1.29             ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 1.06/1.29  thf('2', plain,
% 1.06/1.29      (![X32 : $i, X33 : $i]:
% 1.06/1.29         (~ (l1_pre_topc @ X32)
% 1.06/1.29          | ~ (v2_pre_topc @ X32)
% 1.06/1.29          | (v2_struct_0 @ X32)
% 1.06/1.29          | ~ (m1_pre_topc @ X33 @ X32)
% 1.06/1.29          | (m1_subset_1 @ (k4_tmap_1 @ X32 @ X33) @ 
% 1.06/1.29             (k1_zfmisc_1 @ 
% 1.06/1.29              (k2_zfmisc_1 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X32)))))),
% 1.06/1.29      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 1.06/1.29  thf('3', plain,
% 1.06/1.29      (((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 1.06/1.29         (k1_zfmisc_1 @ 
% 1.06/1.29          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 1.06/1.29        | (v2_struct_0 @ sk_A)
% 1.06/1.29        | ~ (v2_pre_topc @ sk_A)
% 1.06/1.29        | ~ (l1_pre_topc @ sk_A))),
% 1.06/1.29      inference('sup-', [status(thm)], ['1', '2'])).
% 1.06/1.29  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('6', plain,
% 1.06/1.29      (((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 1.06/1.29         (k1_zfmisc_1 @ 
% 1.06/1.29          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 1.06/1.29        | (v2_struct_0 @ sk_A))),
% 1.06/1.29      inference('demod', [status(thm)], ['3', '4', '5'])).
% 1.06/1.29  thf('7', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('8', plain,
% 1.06/1.29      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 1.06/1.29        (k1_zfmisc_1 @ 
% 1.06/1.29         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 1.06/1.29      inference('clc', [status(thm)], ['6', '7'])).
% 1.06/1.29  thf('9', plain,
% 1.06/1.29      ((m1_subset_1 @ sk_C @ 
% 1.06/1.29        (k1_zfmisc_1 @ 
% 1.06/1.29         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf(redefinition_r2_funct_2, axiom,
% 1.06/1.29    (![A:$i,B:$i,C:$i,D:$i]:
% 1.06/1.29     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.06/1.29         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.06/1.29         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.06/1.29         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.06/1.29       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.06/1.29  thf('10', plain,
% 1.06/1.29      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.06/1.29         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 1.06/1.29          | ~ (v1_funct_2 @ X7 @ X8 @ X9)
% 1.06/1.29          | ~ (v1_funct_1 @ X7)
% 1.06/1.29          | ~ (v1_funct_1 @ X10)
% 1.06/1.29          | ~ (v1_funct_2 @ X10 @ X8 @ X9)
% 1.06/1.29          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 1.06/1.29          | ((X7) = (X10))
% 1.06/1.29          | ~ (r2_funct_2 @ X8 @ X9 @ X7 @ X10))),
% 1.06/1.29      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 1.06/1.29  thf('11', plain,
% 1.06/1.29      (![X0 : $i]:
% 1.06/1.29         (~ (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.29             sk_C @ X0)
% 1.06/1.29          | ((sk_C) = (X0))
% 1.06/1.29          | ~ (m1_subset_1 @ X0 @ 
% 1.06/1.29               (k1_zfmisc_1 @ 
% 1.06/1.29                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 1.06/1.29          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 1.06/1.29          | ~ (v1_funct_1 @ X0)
% 1.06/1.29          | ~ (v1_funct_1 @ sk_C)
% 1.06/1.29          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ 
% 1.06/1.29               (u1_struct_0 @ sk_A)))),
% 1.06/1.29      inference('sup-', [status(thm)], ['9', '10'])).
% 1.06/1.29  thf('12', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('13', plain,
% 1.06/1.29      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('14', plain,
% 1.06/1.29      (![X0 : $i]:
% 1.06/1.29         (~ (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.29             sk_C @ X0)
% 1.06/1.29          | ((sk_C) = (X0))
% 1.06/1.29          | ~ (m1_subset_1 @ X0 @ 
% 1.06/1.29               (k1_zfmisc_1 @ 
% 1.06/1.29                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 1.06/1.29          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 1.06/1.29          | ~ (v1_funct_1 @ X0))),
% 1.06/1.29      inference('demod', [status(thm)], ['11', '12', '13'])).
% 1.06/1.29  thf('15', plain,
% 1.06/1.29      ((~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.29        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 1.06/1.29             (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 1.06/1.29        | ((sk_C) = (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.29        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.29             sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1)))),
% 1.06/1.29      inference('sup-', [status(thm)], ['8', '14'])).
% 1.06/1.29  thf('16', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('17', plain,
% 1.06/1.29      (![X32 : $i, X33 : $i]:
% 1.06/1.29         (~ (l1_pre_topc @ X32)
% 1.06/1.29          | ~ (v2_pre_topc @ X32)
% 1.06/1.29          | (v2_struct_0 @ X32)
% 1.06/1.29          | ~ (m1_pre_topc @ X33 @ X32)
% 1.06/1.29          | (v1_funct_1 @ (k4_tmap_1 @ X32 @ X33)))),
% 1.06/1.29      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 1.06/1.29  thf('18', plain,
% 1.06/1.29      (((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.29        | (v2_struct_0 @ sk_A)
% 1.06/1.29        | ~ (v2_pre_topc @ sk_A)
% 1.06/1.29        | ~ (l1_pre_topc @ sk_A))),
% 1.06/1.29      inference('sup-', [status(thm)], ['16', '17'])).
% 1.06/1.29  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('21', plain,
% 1.06/1.29      (((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 1.06/1.29      inference('demod', [status(thm)], ['18', '19', '20'])).
% 1.06/1.29  thf('22', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('23', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))),
% 1.06/1.29      inference('clc', [status(thm)], ['21', '22'])).
% 1.06/1.29  thf('24', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('25', plain,
% 1.06/1.29      (![X32 : $i, X33 : $i]:
% 1.06/1.29         (~ (l1_pre_topc @ X32)
% 1.06/1.29          | ~ (v2_pre_topc @ X32)
% 1.06/1.29          | (v2_struct_0 @ X32)
% 1.06/1.29          | ~ (m1_pre_topc @ X33 @ X32)
% 1.06/1.29          | (v1_funct_2 @ (k4_tmap_1 @ X32 @ X33) @ (u1_struct_0 @ X33) @ 
% 1.06/1.29             (u1_struct_0 @ X32)))),
% 1.06/1.29      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 1.06/1.29  thf('26', plain,
% 1.06/1.29      (((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.06/1.29         (u1_struct_0 @ sk_A))
% 1.06/1.29        | (v2_struct_0 @ sk_A)
% 1.06/1.29        | ~ (v2_pre_topc @ sk_A)
% 1.06/1.29        | ~ (l1_pre_topc @ sk_A))),
% 1.06/1.29      inference('sup-', [status(thm)], ['24', '25'])).
% 1.06/1.29  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('29', plain,
% 1.06/1.29      (((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.06/1.29         (u1_struct_0 @ sk_A))
% 1.06/1.29        | (v2_struct_0 @ sk_A))),
% 1.06/1.29      inference('demod', [status(thm)], ['26', '27', '28'])).
% 1.06/1.29  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('31', plain,
% 1.06/1.29      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.06/1.29        (u1_struct_0 @ sk_A))),
% 1.06/1.29      inference('clc', [status(thm)], ['29', '30'])).
% 1.06/1.29  thf('32', plain,
% 1.06/1.29      ((((sk_C) = (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.29        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.29             sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1)))),
% 1.06/1.29      inference('demod', [status(thm)], ['15', '23', '31'])).
% 1.06/1.29  thf(t2_tsep_1, axiom,
% 1.06/1.29    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 1.06/1.29  thf('33', plain,
% 1.06/1.29      (![X34 : $i]: ((m1_pre_topc @ X34 @ X34) | ~ (l1_pre_topc @ X34))),
% 1.06/1.29      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.06/1.29  thf('34', plain,
% 1.06/1.29      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 1.06/1.29        (k1_zfmisc_1 @ 
% 1.06/1.29         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 1.06/1.29      inference('clc', [status(thm)], ['6', '7'])).
% 1.06/1.29  thf('35', plain,
% 1.06/1.29      ((m1_subset_1 @ sk_C @ 
% 1.06/1.29        (k1_zfmisc_1 @ 
% 1.06/1.29         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf(t59_tmap_1, axiom,
% 1.06/1.29    (![A:$i]:
% 1.06/1.29     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.29       ( ![B:$i]:
% 1.06/1.29         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.06/1.29             ( l1_pre_topc @ B ) ) =>
% 1.06/1.29           ( ![C:$i]:
% 1.06/1.29             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 1.06/1.29               ( ![D:$i]:
% 1.06/1.29                 ( ( ( v1_funct_1 @ D ) & 
% 1.06/1.29                     ( v1_funct_2 @
% 1.06/1.29                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 1.06/1.29                     ( m1_subset_1 @
% 1.06/1.29                       D @ 
% 1.06/1.29                       ( k1_zfmisc_1 @
% 1.06/1.29                         ( k2_zfmisc_1 @
% 1.06/1.29                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 1.06/1.29                   ( ![E:$i]:
% 1.06/1.29                     ( ( ( v1_funct_1 @ E ) & 
% 1.06/1.29                         ( v1_funct_2 @
% 1.06/1.29                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) & 
% 1.06/1.29                         ( m1_subset_1 @
% 1.06/1.29                           E @ 
% 1.06/1.29                           ( k1_zfmisc_1 @
% 1.06/1.29                             ( k2_zfmisc_1 @
% 1.06/1.29                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 1.06/1.29                       ( ( ![F:$i]:
% 1.06/1.29                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 1.06/1.29                             ( ( r2_hidden @ F @ ( u1_struct_0 @ C ) ) =>
% 1.06/1.29                               ( ( k3_funct_2 @
% 1.06/1.29                                   ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.06/1.29                                   D @ F ) =
% 1.06/1.29                                 ( k1_funct_1 @ E @ F ) ) ) ) ) =>
% 1.06/1.29                         ( r2_funct_2 @
% 1.06/1.29                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 1.06/1.29                           ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ))).
% 1.06/1.29  thf('36', plain,
% 1.06/1.29      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 1.06/1.29         ((v2_struct_0 @ X35)
% 1.06/1.29          | ~ (v2_pre_topc @ X35)
% 1.06/1.29          | ~ (l1_pre_topc @ X35)
% 1.06/1.29          | ~ (v1_funct_1 @ X36)
% 1.06/1.29          | ~ (v1_funct_2 @ X36 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X37))
% 1.06/1.29          | ~ (m1_subset_1 @ X36 @ 
% 1.06/1.29               (k1_zfmisc_1 @ 
% 1.06/1.29                (k2_zfmisc_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X37))))
% 1.06/1.29          | (r2_hidden @ (sk_F @ X38 @ X36 @ X39 @ X35 @ X37) @ 
% 1.06/1.29             (u1_struct_0 @ X39))
% 1.06/1.29          | (r2_funct_2 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X37) @ 
% 1.06/1.29             (k2_tmap_1 @ X35 @ X37 @ X36 @ X39) @ X38)
% 1.06/1.29          | ~ (m1_subset_1 @ X38 @ 
% 1.06/1.29               (k1_zfmisc_1 @ 
% 1.06/1.29                (k2_zfmisc_1 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X37))))
% 1.06/1.29          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X37))
% 1.06/1.29          | ~ (v1_funct_1 @ X38)
% 1.06/1.29          | ~ (m1_pre_topc @ X39 @ X35)
% 1.06/1.29          | (v2_struct_0 @ X39)
% 1.06/1.29          | ~ (l1_pre_topc @ X37)
% 1.06/1.29          | ~ (v2_pre_topc @ X37)
% 1.06/1.29          | (v2_struct_0 @ X37))),
% 1.06/1.29      inference('cnf', [status(esa)], [t59_tmap_1])).
% 1.06/1.29  thf('37', plain,
% 1.06/1.29      (![X0 : $i, X1 : $i]:
% 1.06/1.29         ((v2_struct_0 @ sk_A)
% 1.06/1.29          | ~ (v2_pre_topc @ sk_A)
% 1.06/1.29          | ~ (l1_pre_topc @ sk_A)
% 1.06/1.29          | (v2_struct_0 @ X0)
% 1.06/1.29          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 1.06/1.29          | ~ (v1_funct_1 @ X1)
% 1.06/1.29          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.06/1.29          | ~ (m1_subset_1 @ X1 @ 
% 1.06/1.29               (k1_zfmisc_1 @ 
% 1.06/1.29                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 1.06/1.29          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.29             (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ X1)
% 1.06/1.29          | (r2_hidden @ (sk_F @ X1 @ sk_C @ X0 @ sk_B_1 @ sk_A) @ 
% 1.06/1.29             (u1_struct_0 @ X0))
% 1.06/1.29          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ 
% 1.06/1.29               (u1_struct_0 @ sk_A))
% 1.06/1.29          | ~ (v1_funct_1 @ sk_C)
% 1.06/1.29          | ~ (l1_pre_topc @ sk_B_1)
% 1.06/1.29          | ~ (v2_pre_topc @ sk_B_1)
% 1.06/1.29          | (v2_struct_0 @ sk_B_1))),
% 1.06/1.29      inference('sup-', [status(thm)], ['35', '36'])).
% 1.06/1.29  thf('38', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('40', plain,
% 1.06/1.29      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('41', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('42', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf(dt_m1_pre_topc, axiom,
% 1.06/1.29    (![A:$i]:
% 1.06/1.29     ( ( l1_pre_topc @ A ) =>
% 1.06/1.29       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.06/1.29  thf('43', plain,
% 1.06/1.29      (![X14 : $i, X15 : $i]:
% 1.06/1.29         (~ (m1_pre_topc @ X14 @ X15)
% 1.06/1.29          | (l1_pre_topc @ X14)
% 1.06/1.29          | ~ (l1_pre_topc @ X15))),
% 1.06/1.29      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.06/1.29  thf('44', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B_1))),
% 1.06/1.29      inference('sup-', [status(thm)], ['42', '43'])).
% 1.06/1.29  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('46', plain, ((l1_pre_topc @ sk_B_1)),
% 1.06/1.29      inference('demod', [status(thm)], ['44', '45'])).
% 1.06/1.29  thf('47', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf(cc1_pre_topc, axiom,
% 1.06/1.29    (![A:$i]:
% 1.06/1.29     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.29       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 1.06/1.29  thf('48', plain,
% 1.06/1.29      (![X11 : $i, X12 : $i]:
% 1.06/1.29         (~ (m1_pre_topc @ X11 @ X12)
% 1.06/1.29          | (v2_pre_topc @ X11)
% 1.06/1.29          | ~ (l1_pre_topc @ X12)
% 1.06/1.29          | ~ (v2_pre_topc @ X12))),
% 1.06/1.29      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 1.06/1.29  thf('49', plain,
% 1.06/1.29      ((~ (v2_pre_topc @ sk_A)
% 1.06/1.29        | ~ (l1_pre_topc @ sk_A)
% 1.06/1.29        | (v2_pre_topc @ sk_B_1))),
% 1.06/1.29      inference('sup-', [status(thm)], ['47', '48'])).
% 1.06/1.29  thf('50', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('52', plain, ((v2_pre_topc @ sk_B_1)),
% 1.06/1.29      inference('demod', [status(thm)], ['49', '50', '51'])).
% 1.06/1.29  thf('53', plain,
% 1.06/1.29      (![X0 : $i, X1 : $i]:
% 1.06/1.29         ((v2_struct_0 @ sk_A)
% 1.06/1.29          | (v2_struct_0 @ X0)
% 1.06/1.29          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 1.06/1.29          | ~ (v1_funct_1 @ X1)
% 1.06/1.29          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.06/1.29          | ~ (m1_subset_1 @ X1 @ 
% 1.06/1.29               (k1_zfmisc_1 @ 
% 1.06/1.29                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 1.06/1.29          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.29             (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ X1)
% 1.06/1.29          | (r2_hidden @ (sk_F @ X1 @ sk_C @ X0 @ sk_B_1 @ sk_A) @ 
% 1.06/1.29             (u1_struct_0 @ X0))
% 1.06/1.29          | (v2_struct_0 @ sk_B_1))),
% 1.06/1.29      inference('demod', [status(thm)],
% 1.06/1.29                ['37', '38', '39', '40', '41', '46', '52'])).
% 1.06/1.29  thf('54', plain,
% 1.06/1.29      (((v2_struct_0 @ sk_B_1)
% 1.06/1.29        | (r2_hidden @ 
% 1.06/1.29           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 1.06/1.29           (u1_struct_0 @ sk_B_1))
% 1.06/1.29        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.29           (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1) @ 
% 1.06/1.29           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.29        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 1.06/1.29             (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 1.06/1.29        | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.29        | ~ (m1_pre_topc @ sk_B_1 @ sk_B_1)
% 1.06/1.29        | (v2_struct_0 @ sk_B_1)
% 1.06/1.29        | (v2_struct_0 @ sk_A))),
% 1.06/1.29      inference('sup-', [status(thm)], ['34', '53'])).
% 1.06/1.29  thf('55', plain,
% 1.06/1.29      ((m1_subset_1 @ sk_C @ 
% 1.06/1.29        (k1_zfmisc_1 @ 
% 1.06/1.29         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf(dt_k2_tmap_1, axiom,
% 1.06/1.29    (![A:$i,B:$i,C:$i,D:$i]:
% 1.06/1.29     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) & ( v1_funct_1 @ C ) & 
% 1.06/1.29         ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.06/1.29         ( m1_subset_1 @
% 1.06/1.29           C @ 
% 1.06/1.29           ( k1_zfmisc_1 @
% 1.06/1.29             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 1.06/1.29         ( l1_struct_0 @ D ) ) =>
% 1.06/1.29       ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 1.06/1.29         ( v1_funct_2 @
% 1.06/1.29           ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ 
% 1.06/1.29           ( u1_struct_0 @ B ) ) & 
% 1.06/1.29         ( m1_subset_1 @
% 1.06/1.29           ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 1.06/1.29           ( k1_zfmisc_1 @
% 1.06/1.29             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 1.06/1.29  thf('56', plain,
% 1.06/1.29      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.06/1.29         (~ (m1_subset_1 @ X28 @ 
% 1.06/1.29             (k1_zfmisc_1 @ 
% 1.06/1.29              (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X30))))
% 1.06/1.29          | ~ (v1_funct_2 @ X28 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X30))
% 1.06/1.29          | ~ (v1_funct_1 @ X28)
% 1.06/1.29          | ~ (l1_struct_0 @ X30)
% 1.06/1.29          | ~ (l1_struct_0 @ X29)
% 1.06/1.29          | ~ (l1_struct_0 @ X31)
% 1.06/1.29          | (v1_funct_1 @ (k2_tmap_1 @ X29 @ X30 @ X28 @ X31)))),
% 1.06/1.29      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 1.06/1.29  thf('57', plain,
% 1.06/1.29      (![X0 : $i]:
% 1.06/1.29         ((v1_funct_1 @ (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0))
% 1.06/1.29          | ~ (l1_struct_0 @ X0)
% 1.06/1.29          | ~ (l1_struct_0 @ sk_B_1)
% 1.06/1.29          | ~ (l1_struct_0 @ sk_A)
% 1.06/1.29          | ~ (v1_funct_1 @ sk_C)
% 1.06/1.29          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ 
% 1.06/1.29               (u1_struct_0 @ sk_A)))),
% 1.06/1.29      inference('sup-', [status(thm)], ['55', '56'])).
% 1.06/1.29  thf('58', plain, ((l1_pre_topc @ sk_B_1)),
% 1.06/1.29      inference('demod', [status(thm)], ['44', '45'])).
% 1.06/1.29  thf(dt_l1_pre_topc, axiom,
% 1.06/1.29    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.06/1.29  thf('59', plain,
% 1.06/1.29      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 1.06/1.29      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.06/1.29  thf('60', plain, ((l1_struct_0 @ sk_B_1)),
% 1.06/1.29      inference('sup-', [status(thm)], ['58', '59'])).
% 1.06/1.29  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('62', plain,
% 1.06/1.29      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 1.06/1.29      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.06/1.29  thf('63', plain, ((l1_struct_0 @ sk_A)),
% 1.06/1.29      inference('sup-', [status(thm)], ['61', '62'])).
% 1.06/1.29  thf('64', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('65', plain,
% 1.06/1.29      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('66', plain,
% 1.06/1.29      (![X0 : $i]:
% 1.06/1.29         ((v1_funct_1 @ (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0))
% 1.06/1.29          | ~ (l1_struct_0 @ X0))),
% 1.06/1.29      inference('demod', [status(thm)], ['57', '60', '63', '64', '65'])).
% 1.06/1.29  thf('67', plain,
% 1.06/1.29      ((m1_subset_1 @ sk_C @ 
% 1.06/1.29        (k1_zfmisc_1 @ 
% 1.06/1.29         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('68', plain,
% 1.06/1.29      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.06/1.29         (~ (m1_subset_1 @ X28 @ 
% 1.06/1.29             (k1_zfmisc_1 @ 
% 1.06/1.29              (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X30))))
% 1.06/1.29          | ~ (v1_funct_2 @ X28 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X30))
% 1.06/1.29          | ~ (v1_funct_1 @ X28)
% 1.06/1.29          | ~ (l1_struct_0 @ X30)
% 1.06/1.29          | ~ (l1_struct_0 @ X29)
% 1.06/1.29          | ~ (l1_struct_0 @ X31)
% 1.06/1.29          | (v1_funct_2 @ (k2_tmap_1 @ X29 @ X30 @ X28 @ X31) @ 
% 1.06/1.29             (u1_struct_0 @ X31) @ (u1_struct_0 @ X30)))),
% 1.06/1.29      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 1.06/1.29  thf('69', plain,
% 1.06/1.29      (![X0 : $i]:
% 1.06/1.29         ((v1_funct_2 @ (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 1.06/1.29           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.06/1.29          | ~ (l1_struct_0 @ X0)
% 1.06/1.29          | ~ (l1_struct_0 @ sk_B_1)
% 1.06/1.29          | ~ (l1_struct_0 @ sk_A)
% 1.06/1.29          | ~ (v1_funct_1 @ sk_C)
% 1.06/1.29          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ 
% 1.06/1.29               (u1_struct_0 @ sk_A)))),
% 1.06/1.29      inference('sup-', [status(thm)], ['67', '68'])).
% 1.06/1.29  thf('70', plain, ((l1_struct_0 @ sk_B_1)),
% 1.06/1.29      inference('sup-', [status(thm)], ['58', '59'])).
% 1.06/1.29  thf('71', plain, ((l1_struct_0 @ sk_A)),
% 1.06/1.29      inference('sup-', [status(thm)], ['61', '62'])).
% 1.06/1.29  thf('72', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('73', plain,
% 1.06/1.29      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('74', plain,
% 1.06/1.29      (![X0 : $i]:
% 1.06/1.29         ((v1_funct_2 @ (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 1.06/1.29           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.06/1.29          | ~ (l1_struct_0 @ X0))),
% 1.06/1.29      inference('demod', [status(thm)], ['69', '70', '71', '72', '73'])).
% 1.06/1.29  thf('75', plain,
% 1.06/1.29      ((m1_subset_1 @ sk_C @ 
% 1.06/1.29        (k1_zfmisc_1 @ 
% 1.06/1.29         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('76', plain,
% 1.06/1.29      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.06/1.29         (~ (m1_subset_1 @ X28 @ 
% 1.06/1.29             (k1_zfmisc_1 @ 
% 1.06/1.29              (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X30))))
% 1.06/1.29          | ~ (v1_funct_2 @ X28 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X30))
% 1.06/1.29          | ~ (v1_funct_1 @ X28)
% 1.06/1.29          | ~ (l1_struct_0 @ X30)
% 1.06/1.29          | ~ (l1_struct_0 @ X29)
% 1.06/1.29          | ~ (l1_struct_0 @ X31)
% 1.06/1.29          | (m1_subset_1 @ (k2_tmap_1 @ X29 @ X30 @ X28 @ X31) @ 
% 1.06/1.29             (k1_zfmisc_1 @ 
% 1.06/1.29              (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30)))))),
% 1.06/1.29      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 1.06/1.29  thf('77', plain,
% 1.06/1.29      (![X0 : $i]:
% 1.06/1.29         ((m1_subset_1 @ (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 1.06/1.29           (k1_zfmisc_1 @ 
% 1.06/1.29            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 1.06/1.29          | ~ (l1_struct_0 @ X0)
% 1.06/1.29          | ~ (l1_struct_0 @ sk_B_1)
% 1.06/1.29          | ~ (l1_struct_0 @ sk_A)
% 1.06/1.29          | ~ (v1_funct_1 @ sk_C)
% 1.06/1.29          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ 
% 1.06/1.29               (u1_struct_0 @ sk_A)))),
% 1.06/1.29      inference('sup-', [status(thm)], ['75', '76'])).
% 1.06/1.29  thf('78', plain, ((l1_struct_0 @ sk_B_1)),
% 1.06/1.29      inference('sup-', [status(thm)], ['58', '59'])).
% 1.06/1.29  thf('79', plain, ((l1_struct_0 @ sk_A)),
% 1.06/1.29      inference('sup-', [status(thm)], ['61', '62'])).
% 1.06/1.29  thf('80', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('81', plain,
% 1.06/1.29      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('82', plain,
% 1.06/1.29      (![X0 : $i]:
% 1.06/1.29         ((m1_subset_1 @ (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 1.06/1.29           (k1_zfmisc_1 @ 
% 1.06/1.29            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 1.06/1.29          | ~ (l1_struct_0 @ X0))),
% 1.06/1.29      inference('demod', [status(thm)], ['77', '78', '79', '80', '81'])).
% 1.06/1.29  thf('83', plain,
% 1.06/1.29      (![X0 : $i]:
% 1.06/1.29         (~ (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.29             sk_C @ X0)
% 1.06/1.29          | ((sk_C) = (X0))
% 1.06/1.29          | ~ (m1_subset_1 @ X0 @ 
% 1.06/1.29               (k1_zfmisc_1 @ 
% 1.06/1.29                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 1.06/1.29          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 1.06/1.29          | ~ (v1_funct_1 @ X0))),
% 1.06/1.29      inference('demod', [status(thm)], ['11', '12', '13'])).
% 1.06/1.29  thf('84', plain,
% 1.06/1.29      ((~ (l1_struct_0 @ sk_B_1)
% 1.06/1.29        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1))
% 1.06/1.29        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1) @ 
% 1.06/1.29             (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 1.06/1.29        | ((sk_C) = (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1))
% 1.06/1.29        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.29             sk_C @ (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1)))),
% 1.06/1.29      inference('sup-', [status(thm)], ['82', '83'])).
% 1.06/1.29  thf('85', plain, ((l1_struct_0 @ sk_B_1)),
% 1.06/1.29      inference('sup-', [status(thm)], ['58', '59'])).
% 1.06/1.29  thf('86', plain,
% 1.06/1.29      ((~ (v1_funct_1 @ (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1))
% 1.06/1.29        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1) @ 
% 1.06/1.29             (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 1.06/1.29        | ((sk_C) = (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1))
% 1.06/1.29        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.29             sk_C @ (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1)))),
% 1.06/1.29      inference('demod', [status(thm)], ['84', '85'])).
% 1.06/1.29  thf('87', plain,
% 1.06/1.29      (![X34 : $i]: ((m1_pre_topc @ X34 @ X34) | ~ (l1_pre_topc @ X34))),
% 1.06/1.29      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.06/1.29  thf('88', plain,
% 1.06/1.29      ((m1_subset_1 @ sk_C @ 
% 1.06/1.29        (k1_zfmisc_1 @ 
% 1.06/1.29         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf(t74_tmap_1, axiom,
% 1.06/1.29    (![A:$i]:
% 1.06/1.29     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.29       ( ![B:$i]:
% 1.06/1.29         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.06/1.29             ( l1_pre_topc @ B ) ) =>
% 1.06/1.29           ( ![C:$i]:
% 1.06/1.29             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.06/1.29               ( ![D:$i]:
% 1.06/1.29                 ( ( ( v1_funct_1 @ D ) & 
% 1.06/1.29                     ( v1_funct_2 @
% 1.06/1.29                       D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.06/1.29                     ( m1_subset_1 @
% 1.06/1.29                       D @ 
% 1.06/1.29                       ( k1_zfmisc_1 @
% 1.06/1.29                         ( k2_zfmisc_1 @
% 1.06/1.29                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.06/1.29                   ( r2_funct_2 @
% 1.06/1.29                     ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ D @ 
% 1.06/1.29                     ( k3_tmap_1 @ A @ B @ C @ C @ D ) ) ) ) ) ) ) ) ))).
% 1.06/1.29  thf('89', plain,
% 1.06/1.29      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 1.06/1.29         ((v2_struct_0 @ X40)
% 1.06/1.29          | ~ (v2_pre_topc @ X40)
% 1.06/1.29          | ~ (l1_pre_topc @ X40)
% 1.06/1.29          | ~ (v1_funct_1 @ X41)
% 1.06/1.29          | ~ (v1_funct_2 @ X41 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X40))
% 1.06/1.29          | ~ (m1_subset_1 @ X41 @ 
% 1.06/1.29               (k1_zfmisc_1 @ 
% 1.06/1.29                (k2_zfmisc_1 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X40))))
% 1.06/1.29          | (r2_funct_2 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X40) @ X41 @ 
% 1.06/1.29             (k3_tmap_1 @ X43 @ X40 @ X42 @ X42 @ X41))
% 1.06/1.29          | ~ (m1_pre_topc @ X42 @ X43)
% 1.06/1.29          | (v2_struct_0 @ X42)
% 1.06/1.29          | ~ (l1_pre_topc @ X43)
% 1.06/1.29          | ~ (v2_pre_topc @ X43)
% 1.06/1.29          | (v2_struct_0 @ X43))),
% 1.06/1.29      inference('cnf', [status(esa)], [t74_tmap_1])).
% 1.06/1.29  thf('90', plain,
% 1.06/1.29      (![X0 : $i]:
% 1.06/1.29         ((v2_struct_0 @ X0)
% 1.06/1.29          | ~ (v2_pre_topc @ X0)
% 1.06/1.29          | ~ (l1_pre_topc @ X0)
% 1.06/1.29          | (v2_struct_0 @ sk_B_1)
% 1.06/1.29          | ~ (m1_pre_topc @ sk_B_1 @ X0)
% 1.06/1.29          | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.29             sk_C @ (k3_tmap_1 @ X0 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_C))
% 1.06/1.29          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ 
% 1.06/1.29               (u1_struct_0 @ sk_A))
% 1.06/1.29          | ~ (v1_funct_1 @ sk_C)
% 1.06/1.29          | ~ (l1_pre_topc @ sk_A)
% 1.06/1.29          | ~ (v2_pre_topc @ sk_A)
% 1.06/1.29          | (v2_struct_0 @ sk_A))),
% 1.06/1.29      inference('sup-', [status(thm)], ['88', '89'])).
% 1.06/1.29  thf('91', plain,
% 1.06/1.29      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('92', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('94', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('95', plain,
% 1.06/1.29      (![X0 : $i]:
% 1.06/1.29         ((v2_struct_0 @ X0)
% 1.06/1.29          | ~ (v2_pre_topc @ X0)
% 1.06/1.29          | ~ (l1_pre_topc @ X0)
% 1.06/1.29          | (v2_struct_0 @ sk_B_1)
% 1.06/1.29          | ~ (m1_pre_topc @ sk_B_1 @ X0)
% 1.06/1.29          | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.29             sk_C @ (k3_tmap_1 @ X0 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_C))
% 1.06/1.29          | (v2_struct_0 @ sk_A))),
% 1.06/1.29      inference('demod', [status(thm)], ['90', '91', '92', '93', '94'])).
% 1.06/1.29  thf('96', plain,
% 1.06/1.29      ((~ (l1_pre_topc @ sk_B_1)
% 1.06/1.29        | (v2_struct_0 @ sk_A)
% 1.06/1.29        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.29           (k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_C))
% 1.06/1.29        | (v2_struct_0 @ sk_B_1)
% 1.06/1.29        | ~ (l1_pre_topc @ sk_B_1)
% 1.06/1.29        | ~ (v2_pre_topc @ sk_B_1)
% 1.06/1.29        | (v2_struct_0 @ sk_B_1))),
% 1.06/1.29      inference('sup-', [status(thm)], ['87', '95'])).
% 1.06/1.29  thf('97', plain, ((l1_pre_topc @ sk_B_1)),
% 1.06/1.29      inference('demod', [status(thm)], ['44', '45'])).
% 1.06/1.29  thf('98', plain,
% 1.06/1.29      (![X34 : $i]: ((m1_pre_topc @ X34 @ X34) | ~ (l1_pre_topc @ X34))),
% 1.06/1.29      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.06/1.29  thf('99', plain,
% 1.06/1.29      (![X34 : $i]: ((m1_pre_topc @ X34 @ X34) | ~ (l1_pre_topc @ X34))),
% 1.06/1.29      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.06/1.29  thf('100', plain,
% 1.06/1.29      ((m1_subset_1 @ sk_C @ 
% 1.06/1.29        (k1_zfmisc_1 @ 
% 1.06/1.29         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf(d5_tmap_1, axiom,
% 1.06/1.29    (![A:$i]:
% 1.06/1.29     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.29       ( ![B:$i]:
% 1.06/1.29         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.06/1.29             ( l1_pre_topc @ B ) ) =>
% 1.06/1.29           ( ![C:$i]:
% 1.06/1.29             ( ( m1_pre_topc @ C @ A ) =>
% 1.06/1.29               ( ![D:$i]:
% 1.06/1.29                 ( ( m1_pre_topc @ D @ A ) =>
% 1.06/1.29                   ( ![E:$i]:
% 1.06/1.29                     ( ( ( v1_funct_1 @ E ) & 
% 1.06/1.29                         ( v1_funct_2 @
% 1.06/1.29                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.06/1.29                         ( m1_subset_1 @
% 1.06/1.29                           E @ 
% 1.06/1.29                           ( k1_zfmisc_1 @
% 1.06/1.29                             ( k2_zfmisc_1 @
% 1.06/1.29                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.06/1.29                       ( ( m1_pre_topc @ D @ C ) =>
% 1.06/1.29                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 1.06/1.29                           ( k2_partfun1 @
% 1.06/1.29                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 1.06/1.29                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.06/1.29  thf('101', plain,
% 1.06/1.29      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.06/1.29         ((v2_struct_0 @ X23)
% 1.06/1.29          | ~ (v2_pre_topc @ X23)
% 1.06/1.29          | ~ (l1_pre_topc @ X23)
% 1.06/1.29          | ~ (m1_pre_topc @ X24 @ X25)
% 1.06/1.29          | ~ (m1_pre_topc @ X24 @ X26)
% 1.06/1.29          | ((k3_tmap_1 @ X25 @ X23 @ X26 @ X24 @ X27)
% 1.06/1.29              = (k2_partfun1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X23) @ 
% 1.06/1.29                 X27 @ (u1_struct_0 @ X24)))
% 1.06/1.29          | ~ (m1_subset_1 @ X27 @ 
% 1.06/1.29               (k1_zfmisc_1 @ 
% 1.06/1.29                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X23))))
% 1.06/1.29          | ~ (v1_funct_2 @ X27 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X23))
% 1.06/1.29          | ~ (v1_funct_1 @ X27)
% 1.06/1.29          | ~ (m1_pre_topc @ X26 @ X25)
% 1.06/1.29          | ~ (l1_pre_topc @ X25)
% 1.06/1.29          | ~ (v2_pre_topc @ X25)
% 1.06/1.29          | (v2_struct_0 @ X25))),
% 1.06/1.29      inference('cnf', [status(esa)], [d5_tmap_1])).
% 1.06/1.29  thf('102', plain,
% 1.06/1.29      (![X0 : $i, X1 : $i]:
% 1.06/1.29         ((v2_struct_0 @ X0)
% 1.06/1.29          | ~ (v2_pre_topc @ X0)
% 1.06/1.29          | ~ (l1_pre_topc @ X0)
% 1.06/1.29          | ~ (m1_pre_topc @ sk_B_1 @ X0)
% 1.06/1.29          | ~ (v1_funct_1 @ sk_C)
% 1.06/1.29          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ 
% 1.06/1.29               (u1_struct_0 @ sk_A))
% 1.06/1.29          | ((k3_tmap_1 @ X0 @ sk_A @ sk_B_1 @ X1 @ sk_C)
% 1.06/1.29              = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.29                 sk_C @ (u1_struct_0 @ X1)))
% 1.06/1.29          | ~ (m1_pre_topc @ X1 @ sk_B_1)
% 1.06/1.29          | ~ (m1_pre_topc @ X1 @ X0)
% 1.06/1.29          | ~ (l1_pre_topc @ sk_A)
% 1.06/1.29          | ~ (v2_pre_topc @ sk_A)
% 1.06/1.29          | (v2_struct_0 @ sk_A))),
% 1.06/1.29      inference('sup-', [status(thm)], ['100', '101'])).
% 1.06/1.29  thf('103', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('104', plain,
% 1.06/1.29      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('106', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('107', plain,
% 1.06/1.29      (![X0 : $i, X1 : $i]:
% 1.06/1.29         ((v2_struct_0 @ X0)
% 1.06/1.29          | ~ (v2_pre_topc @ X0)
% 1.06/1.29          | ~ (l1_pre_topc @ X0)
% 1.06/1.29          | ~ (m1_pre_topc @ sk_B_1 @ X0)
% 1.06/1.29          | ((k3_tmap_1 @ X0 @ sk_A @ sk_B_1 @ X1 @ sk_C)
% 1.06/1.29              = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.29                 sk_C @ (u1_struct_0 @ X1)))
% 1.06/1.29          | ~ (m1_pre_topc @ X1 @ sk_B_1)
% 1.06/1.29          | ~ (m1_pre_topc @ X1 @ X0)
% 1.06/1.29          | (v2_struct_0 @ sk_A))),
% 1.06/1.29      inference('demod', [status(thm)], ['102', '103', '104', '105', '106'])).
% 1.06/1.29  thf('108', plain,
% 1.06/1.29      (![X0 : $i]:
% 1.06/1.29         (~ (l1_pre_topc @ sk_B_1)
% 1.06/1.29          | (v2_struct_0 @ sk_A)
% 1.06/1.29          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 1.06/1.29          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 1.06/1.29          | ((k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ sk_C)
% 1.06/1.29              = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.29                 sk_C @ (u1_struct_0 @ X0)))
% 1.06/1.29          | ~ (l1_pre_topc @ sk_B_1)
% 1.06/1.29          | ~ (v2_pre_topc @ sk_B_1)
% 1.06/1.29          | (v2_struct_0 @ sk_B_1))),
% 1.06/1.29      inference('sup-', [status(thm)], ['99', '107'])).
% 1.06/1.29  thf('109', plain, ((l1_pre_topc @ sk_B_1)),
% 1.06/1.29      inference('demod', [status(thm)], ['44', '45'])).
% 1.06/1.29  thf('110', plain, ((l1_pre_topc @ sk_B_1)),
% 1.06/1.29      inference('demod', [status(thm)], ['44', '45'])).
% 1.06/1.29  thf('111', plain, ((v2_pre_topc @ sk_B_1)),
% 1.06/1.29      inference('demod', [status(thm)], ['49', '50', '51'])).
% 1.06/1.29  thf('112', plain,
% 1.06/1.29      (![X0 : $i]:
% 1.06/1.29         ((v2_struct_0 @ sk_A)
% 1.06/1.29          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 1.06/1.29          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 1.06/1.29          | ((k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ sk_C)
% 1.06/1.29              = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.29                 sk_C @ (u1_struct_0 @ X0)))
% 1.06/1.29          | (v2_struct_0 @ sk_B_1))),
% 1.06/1.29      inference('demod', [status(thm)], ['108', '109', '110', '111'])).
% 1.06/1.29  thf('113', plain,
% 1.06/1.29      (![X0 : $i]:
% 1.06/1.29         ((v2_struct_0 @ sk_B_1)
% 1.06/1.29          | ((k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ X0 @ sk_C)
% 1.06/1.29              = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.29                 sk_C @ (u1_struct_0 @ X0)))
% 1.06/1.29          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 1.06/1.29          | (v2_struct_0 @ sk_A))),
% 1.06/1.29      inference('simplify', [status(thm)], ['112'])).
% 1.06/1.29  thf('114', plain,
% 1.06/1.29      ((~ (l1_pre_topc @ sk_B_1)
% 1.06/1.29        | (v2_struct_0 @ sk_A)
% 1.06/1.29        | ((k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_C)
% 1.06/1.29            = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.29               sk_C @ (u1_struct_0 @ sk_B_1)))
% 1.06/1.29        | (v2_struct_0 @ sk_B_1))),
% 1.06/1.29      inference('sup-', [status(thm)], ['98', '113'])).
% 1.06/1.29  thf('115', plain, ((l1_pre_topc @ sk_B_1)),
% 1.06/1.29      inference('demod', [status(thm)], ['44', '45'])).
% 1.06/1.29  thf('116', plain,
% 1.06/1.29      (![X34 : $i]: ((m1_pre_topc @ X34 @ X34) | ~ (l1_pre_topc @ X34))),
% 1.06/1.29      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.06/1.29  thf('117', plain,
% 1.06/1.29      ((m1_subset_1 @ sk_C @ 
% 1.06/1.29        (k1_zfmisc_1 @ 
% 1.06/1.29         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf(d4_tmap_1, axiom,
% 1.06/1.29    (![A:$i]:
% 1.06/1.29     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.29       ( ![B:$i]:
% 1.06/1.29         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.06/1.29             ( l1_pre_topc @ B ) ) =>
% 1.06/1.29           ( ![C:$i]:
% 1.06/1.29             ( ( ( v1_funct_1 @ C ) & 
% 1.06/1.29                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.06/1.29                 ( m1_subset_1 @
% 1.06/1.29                   C @ 
% 1.06/1.29                   ( k1_zfmisc_1 @
% 1.06/1.29                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.06/1.29               ( ![D:$i]:
% 1.06/1.29                 ( ( m1_pre_topc @ D @ A ) =>
% 1.06/1.29                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 1.06/1.29                     ( k2_partfun1 @
% 1.06/1.29                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 1.06/1.29                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 1.06/1.29  thf('118', plain,
% 1.06/1.29      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.06/1.29         ((v2_struct_0 @ X19)
% 1.06/1.29          | ~ (v2_pre_topc @ X19)
% 1.06/1.29          | ~ (l1_pre_topc @ X19)
% 1.06/1.29          | ~ (m1_pre_topc @ X20 @ X21)
% 1.06/1.29          | ((k2_tmap_1 @ X21 @ X19 @ X22 @ X20)
% 1.06/1.29              = (k2_partfun1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X19) @ 
% 1.06/1.29                 X22 @ (u1_struct_0 @ X20)))
% 1.06/1.29          | ~ (m1_subset_1 @ X22 @ 
% 1.06/1.29               (k1_zfmisc_1 @ 
% 1.06/1.29                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X19))))
% 1.06/1.29          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X19))
% 1.06/1.29          | ~ (v1_funct_1 @ X22)
% 1.06/1.29          | ~ (l1_pre_topc @ X21)
% 1.06/1.29          | ~ (v2_pre_topc @ X21)
% 1.06/1.29          | (v2_struct_0 @ X21))),
% 1.06/1.29      inference('cnf', [status(esa)], [d4_tmap_1])).
% 1.06/1.29  thf('119', plain,
% 1.06/1.29      (![X0 : $i]:
% 1.06/1.29         ((v2_struct_0 @ sk_B_1)
% 1.06/1.29          | ~ (v2_pre_topc @ sk_B_1)
% 1.06/1.29          | ~ (l1_pre_topc @ sk_B_1)
% 1.06/1.29          | ~ (v1_funct_1 @ sk_C)
% 1.06/1.29          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ 
% 1.06/1.29               (u1_struct_0 @ sk_A))
% 1.06/1.29          | ((k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0)
% 1.06/1.29              = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.29                 sk_C @ (u1_struct_0 @ X0)))
% 1.06/1.29          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 1.06/1.29          | ~ (l1_pre_topc @ sk_A)
% 1.06/1.29          | ~ (v2_pre_topc @ sk_A)
% 1.06/1.29          | (v2_struct_0 @ sk_A))),
% 1.06/1.29      inference('sup-', [status(thm)], ['117', '118'])).
% 1.06/1.29  thf('120', plain, ((v2_pre_topc @ sk_B_1)),
% 1.06/1.29      inference('demod', [status(thm)], ['49', '50', '51'])).
% 1.06/1.29  thf('121', plain, ((l1_pre_topc @ sk_B_1)),
% 1.06/1.29      inference('demod', [status(thm)], ['44', '45'])).
% 1.06/1.29  thf('122', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('123', plain,
% 1.06/1.29      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('124', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('125', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.29  thf('126', plain,
% 1.06/1.29      (![X0 : $i]:
% 1.06/1.29         ((v2_struct_0 @ sk_B_1)
% 1.06/1.29          | ((k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0)
% 1.06/1.29              = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.30                 sk_C @ (u1_struct_0 @ X0)))
% 1.06/1.30          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 1.06/1.30          | (v2_struct_0 @ sk_A))),
% 1.06/1.30      inference('demod', [status(thm)],
% 1.06/1.30                ['119', '120', '121', '122', '123', '124', '125'])).
% 1.06/1.30  thf('127', plain,
% 1.06/1.30      ((~ (l1_pre_topc @ sk_B_1)
% 1.06/1.30        | (v2_struct_0 @ sk_A)
% 1.06/1.30        | ((k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1)
% 1.06/1.30            = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.30               sk_C @ (u1_struct_0 @ sk_B_1)))
% 1.06/1.30        | (v2_struct_0 @ sk_B_1))),
% 1.06/1.30      inference('sup-', [status(thm)], ['116', '126'])).
% 1.06/1.30  thf('128', plain, ((l1_pre_topc @ sk_B_1)),
% 1.06/1.30      inference('demod', [status(thm)], ['44', '45'])).
% 1.06/1.30  thf('129', plain,
% 1.06/1.30      (((v2_struct_0 @ sk_A)
% 1.06/1.30        | ((k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1)
% 1.06/1.30            = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.30               sk_C @ (u1_struct_0 @ sk_B_1)))
% 1.06/1.30        | (v2_struct_0 @ sk_B_1))),
% 1.06/1.30      inference('demod', [status(thm)], ['127', '128'])).
% 1.06/1.30  thf('130', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('131', plain,
% 1.06/1.30      (((v2_struct_0 @ sk_B_1)
% 1.06/1.30        | ((k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1)
% 1.06/1.30            = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.30               sk_C @ (u1_struct_0 @ sk_B_1))))),
% 1.06/1.30      inference('clc', [status(thm)], ['129', '130'])).
% 1.06/1.30  thf('132', plain, (~ (v2_struct_0 @ sk_B_1)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('133', plain,
% 1.06/1.30      (((k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1)
% 1.06/1.30         = (k2_partfun1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.30            sk_C @ (u1_struct_0 @ sk_B_1)))),
% 1.06/1.30      inference('clc', [status(thm)], ['131', '132'])).
% 1.06/1.30  thf('134', plain,
% 1.06/1.30      (((v2_struct_0 @ sk_A)
% 1.06/1.30        | ((k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_C)
% 1.06/1.30            = (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_B_1))),
% 1.06/1.30      inference('demod', [status(thm)], ['114', '115', '133'])).
% 1.06/1.30  thf('135', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('136', plain,
% 1.06/1.30      (((v2_struct_0 @ sk_B_1)
% 1.06/1.30        | ((k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_C)
% 1.06/1.30            = (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1)))),
% 1.06/1.30      inference('clc', [status(thm)], ['134', '135'])).
% 1.06/1.30  thf('137', plain, (~ (v2_struct_0 @ sk_B_1)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('138', plain,
% 1.06/1.30      (((k3_tmap_1 @ sk_B_1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_C)
% 1.06/1.30         = (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1))),
% 1.06/1.30      inference('clc', [status(thm)], ['136', '137'])).
% 1.06/1.30  thf('139', plain, ((l1_pre_topc @ sk_B_1)),
% 1.06/1.30      inference('demod', [status(thm)], ['44', '45'])).
% 1.06/1.30  thf('140', plain, ((v2_pre_topc @ sk_B_1)),
% 1.06/1.30      inference('demod', [status(thm)], ['49', '50', '51'])).
% 1.06/1.30  thf('141', plain,
% 1.06/1.30      (((v2_struct_0 @ sk_A)
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (v2_struct_0 @ sk_B_1))),
% 1.06/1.30      inference('demod', [status(thm)], ['96', '97', '138', '139', '140'])).
% 1.06/1.30  thf('142', plain,
% 1.06/1.30      (((v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_A))),
% 1.06/1.30      inference('simplify', [status(thm)], ['141'])).
% 1.06/1.30  thf('143', plain, (~ (v2_struct_0 @ sk_B_1)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('144', plain,
% 1.06/1.30      (((v2_struct_0 @ sk_A)
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1)))),
% 1.06/1.30      inference('clc', [status(thm)], ['142', '143'])).
% 1.06/1.30  thf('145', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('146', plain,
% 1.06/1.30      ((r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30        (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1))),
% 1.06/1.30      inference('clc', [status(thm)], ['144', '145'])).
% 1.06/1.30  thf('147', plain,
% 1.06/1.30      ((~ (v1_funct_1 @ (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1))
% 1.06/1.30        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1) @ 
% 1.06/1.30             (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 1.06/1.30        | ((sk_C) = (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1)))),
% 1.06/1.30      inference('demod', [status(thm)], ['86', '146'])).
% 1.06/1.30  thf('148', plain,
% 1.06/1.30      ((~ (l1_struct_0 @ sk_B_1)
% 1.06/1.30        | ((sk_C) = (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1))
% 1.06/1.30        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1)))),
% 1.06/1.30      inference('sup-', [status(thm)], ['74', '147'])).
% 1.06/1.30  thf('149', plain, ((l1_struct_0 @ sk_B_1)),
% 1.06/1.30      inference('sup-', [status(thm)], ['58', '59'])).
% 1.06/1.30  thf('150', plain,
% 1.06/1.30      ((((sk_C) = (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1))
% 1.06/1.30        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1)))),
% 1.06/1.30      inference('demod', [status(thm)], ['148', '149'])).
% 1.06/1.30  thf('151', plain,
% 1.06/1.30      ((~ (l1_struct_0 @ sk_B_1)
% 1.06/1.30        | ((sk_C) = (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1)))),
% 1.06/1.30      inference('sup-', [status(thm)], ['66', '150'])).
% 1.06/1.30  thf('152', plain, ((l1_struct_0 @ sk_B_1)),
% 1.06/1.30      inference('sup-', [status(thm)], ['58', '59'])).
% 1.06/1.30  thf('153', plain, (((sk_C) = (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1))),
% 1.06/1.30      inference('demod', [status(thm)], ['151', '152'])).
% 1.06/1.30  thf('154', plain,
% 1.06/1.30      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.06/1.30        (u1_struct_0 @ sk_A))),
% 1.06/1.30      inference('clc', [status(thm)], ['29', '30'])).
% 1.06/1.30  thf('155', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))),
% 1.06/1.30      inference('clc', [status(thm)], ['21', '22'])).
% 1.06/1.30  thf('156', plain,
% 1.06/1.30      (((v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (r2_hidden @ 
% 1.06/1.30           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 1.06/1.30           (u1_struct_0 @ sk_B_1))
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | ~ (m1_pre_topc @ sk_B_1 @ sk_B_1)
% 1.06/1.30        | (v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (v2_struct_0 @ sk_A))),
% 1.06/1.30      inference('demod', [status(thm)], ['54', '153', '154', '155'])).
% 1.06/1.30  thf('157', plain,
% 1.06/1.30      (((v2_struct_0 @ sk_A)
% 1.06/1.30        | ~ (m1_pre_topc @ sk_B_1 @ sk_B_1)
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | (r2_hidden @ 
% 1.06/1.30           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 1.06/1.30           (u1_struct_0 @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_B_1))),
% 1.06/1.30      inference('simplify', [status(thm)], ['156'])).
% 1.06/1.30  thf('158', plain,
% 1.06/1.30      ((~ (l1_pre_topc @ sk_B_1)
% 1.06/1.30        | (v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (r2_hidden @ 
% 1.06/1.30           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 1.06/1.30           (u1_struct_0 @ sk_B_1))
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_A))),
% 1.06/1.30      inference('sup-', [status(thm)], ['33', '157'])).
% 1.06/1.30  thf('159', plain, ((l1_pre_topc @ sk_B_1)),
% 1.06/1.30      inference('demod', [status(thm)], ['44', '45'])).
% 1.06/1.30  thf('160', plain,
% 1.06/1.30      (((v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (r2_hidden @ 
% 1.06/1.30           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 1.06/1.30           (u1_struct_0 @ sk_B_1))
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_A))),
% 1.06/1.30      inference('demod', [status(thm)], ['158', '159'])).
% 1.06/1.30  thf(d1_xboole_0, axiom,
% 1.06/1.30    (![A:$i]:
% 1.06/1.30     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.06/1.30  thf('161', plain,
% 1.06/1.30      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.06/1.30      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.06/1.30  thf('162', plain,
% 1.06/1.30      (((v2_struct_0 @ sk_A)
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_B_1)
% 1.06/1.30        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 1.06/1.30      inference('sup-', [status(thm)], ['160', '161'])).
% 1.06/1.30  thf('163', plain,
% 1.06/1.30      (![X34 : $i]: ((m1_pre_topc @ X34 @ X34) | ~ (l1_pre_topc @ X34))),
% 1.06/1.30      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.06/1.30  thf('164', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('165', plain,
% 1.06/1.30      (![X34 : $i]: ((m1_pre_topc @ X34 @ X34) | ~ (l1_pre_topc @ X34))),
% 1.06/1.30      inference('cnf', [status(esa)], [t2_tsep_1])).
% 1.06/1.30  thf('166', plain,
% 1.06/1.30      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 1.06/1.30        (k1_zfmisc_1 @ 
% 1.06/1.30         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 1.06/1.30      inference('clc', [status(thm)], ['6', '7'])).
% 1.06/1.30  thf('167', plain,
% 1.06/1.30      ((m1_subset_1 @ sk_C @ 
% 1.06/1.30        (k1_zfmisc_1 @ 
% 1.06/1.30         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('168', plain,
% 1.06/1.30      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 1.06/1.30         ((v2_struct_0 @ X35)
% 1.06/1.30          | ~ (v2_pre_topc @ X35)
% 1.06/1.30          | ~ (l1_pre_topc @ X35)
% 1.06/1.30          | ~ (v1_funct_1 @ X36)
% 1.06/1.30          | ~ (v1_funct_2 @ X36 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X37))
% 1.06/1.30          | ~ (m1_subset_1 @ X36 @ 
% 1.06/1.30               (k1_zfmisc_1 @ 
% 1.06/1.30                (k2_zfmisc_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X37))))
% 1.06/1.30          | (m1_subset_1 @ (sk_F @ X38 @ X36 @ X39 @ X35 @ X37) @ 
% 1.06/1.30             (u1_struct_0 @ X35))
% 1.06/1.30          | (r2_funct_2 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X37) @ 
% 1.06/1.30             (k2_tmap_1 @ X35 @ X37 @ X36 @ X39) @ X38)
% 1.06/1.30          | ~ (m1_subset_1 @ X38 @ 
% 1.06/1.30               (k1_zfmisc_1 @ 
% 1.06/1.30                (k2_zfmisc_1 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X37))))
% 1.06/1.30          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X37))
% 1.06/1.30          | ~ (v1_funct_1 @ X38)
% 1.06/1.30          | ~ (m1_pre_topc @ X39 @ X35)
% 1.06/1.30          | (v2_struct_0 @ X39)
% 1.06/1.30          | ~ (l1_pre_topc @ X37)
% 1.06/1.30          | ~ (v2_pre_topc @ X37)
% 1.06/1.30          | (v2_struct_0 @ X37))),
% 1.06/1.30      inference('cnf', [status(esa)], [t59_tmap_1])).
% 1.06/1.30  thf('169', plain,
% 1.06/1.30      (![X0 : $i, X1 : $i]:
% 1.06/1.30         ((v2_struct_0 @ sk_A)
% 1.06/1.30          | ~ (v2_pre_topc @ sk_A)
% 1.06/1.30          | ~ (l1_pre_topc @ sk_A)
% 1.06/1.30          | (v2_struct_0 @ X0)
% 1.06/1.30          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 1.06/1.30          | ~ (v1_funct_1 @ X1)
% 1.06/1.30          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.06/1.30          | ~ (m1_subset_1 @ X1 @ 
% 1.06/1.30               (k1_zfmisc_1 @ 
% 1.06/1.30                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 1.06/1.30          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.30             (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ X1)
% 1.06/1.30          | (m1_subset_1 @ (sk_F @ X1 @ sk_C @ X0 @ sk_B_1 @ sk_A) @ 
% 1.06/1.30             (u1_struct_0 @ sk_B_1))
% 1.06/1.30          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ 
% 1.06/1.30               (u1_struct_0 @ sk_A))
% 1.06/1.30          | ~ (v1_funct_1 @ sk_C)
% 1.06/1.30          | ~ (l1_pre_topc @ sk_B_1)
% 1.06/1.30          | ~ (v2_pre_topc @ sk_B_1)
% 1.06/1.30          | (v2_struct_0 @ sk_B_1))),
% 1.06/1.30      inference('sup-', [status(thm)], ['167', '168'])).
% 1.06/1.30  thf('170', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('171', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('172', plain,
% 1.06/1.30      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('173', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('174', plain, ((l1_pre_topc @ sk_B_1)),
% 1.06/1.30      inference('demod', [status(thm)], ['44', '45'])).
% 1.06/1.30  thf('175', plain, ((v2_pre_topc @ sk_B_1)),
% 1.06/1.30      inference('demod', [status(thm)], ['49', '50', '51'])).
% 1.06/1.30  thf('176', plain,
% 1.06/1.30      (![X0 : $i, X1 : $i]:
% 1.06/1.30         ((v2_struct_0 @ sk_A)
% 1.06/1.30          | (v2_struct_0 @ X0)
% 1.06/1.30          | ~ (m1_pre_topc @ X0 @ sk_B_1)
% 1.06/1.30          | ~ (v1_funct_1 @ X1)
% 1.06/1.30          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 1.06/1.30          | ~ (m1_subset_1 @ X1 @ 
% 1.06/1.30               (k1_zfmisc_1 @ 
% 1.06/1.30                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 1.06/1.30          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.30             (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ X1)
% 1.06/1.30          | (m1_subset_1 @ (sk_F @ X1 @ sk_C @ X0 @ sk_B_1 @ sk_A) @ 
% 1.06/1.30             (u1_struct_0 @ sk_B_1))
% 1.06/1.30          | (v2_struct_0 @ sk_B_1))),
% 1.06/1.30      inference('demod', [status(thm)],
% 1.06/1.30                ['169', '170', '171', '172', '173', '174', '175'])).
% 1.06/1.30  thf('177', plain,
% 1.06/1.30      (((v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (m1_subset_1 @ 
% 1.06/1.30           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 1.06/1.30           (u1_struct_0 @ sk_B_1))
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.30           (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1) @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 1.06/1.30             (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 1.06/1.30        | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | ~ (m1_pre_topc @ sk_B_1 @ sk_B_1)
% 1.06/1.30        | (v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (v2_struct_0 @ sk_A))),
% 1.06/1.30      inference('sup-', [status(thm)], ['166', '176'])).
% 1.06/1.30  thf('178', plain, (((sk_C) = (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1))),
% 1.06/1.30      inference('demod', [status(thm)], ['151', '152'])).
% 1.06/1.30  thf('179', plain,
% 1.06/1.30      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.06/1.30        (u1_struct_0 @ sk_A))),
% 1.06/1.30      inference('clc', [status(thm)], ['29', '30'])).
% 1.06/1.30  thf('180', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))),
% 1.06/1.30      inference('clc', [status(thm)], ['21', '22'])).
% 1.06/1.30  thf('181', plain,
% 1.06/1.30      (((v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (m1_subset_1 @ 
% 1.06/1.30           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 1.06/1.30           (u1_struct_0 @ sk_B_1))
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | ~ (m1_pre_topc @ sk_B_1 @ sk_B_1)
% 1.06/1.30        | (v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (v2_struct_0 @ sk_A))),
% 1.06/1.30      inference('demod', [status(thm)], ['177', '178', '179', '180'])).
% 1.06/1.30  thf('182', plain,
% 1.06/1.30      (((v2_struct_0 @ sk_A)
% 1.06/1.30        | ~ (m1_pre_topc @ sk_B_1 @ sk_B_1)
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | (m1_subset_1 @ 
% 1.06/1.30           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 1.06/1.30           (u1_struct_0 @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_B_1))),
% 1.06/1.30      inference('simplify', [status(thm)], ['181'])).
% 1.06/1.30  thf('183', plain,
% 1.06/1.30      ((~ (l1_pre_topc @ sk_B_1)
% 1.06/1.30        | (v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (m1_subset_1 @ 
% 1.06/1.30           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 1.06/1.30           (u1_struct_0 @ sk_B_1))
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_A))),
% 1.06/1.30      inference('sup-', [status(thm)], ['165', '182'])).
% 1.06/1.30  thf('184', plain, ((l1_pre_topc @ sk_B_1)),
% 1.06/1.30      inference('demod', [status(thm)], ['44', '45'])).
% 1.06/1.30  thf('185', plain,
% 1.06/1.30      (((v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (m1_subset_1 @ 
% 1.06/1.30           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 1.06/1.30           (u1_struct_0 @ sk_B_1))
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_A))),
% 1.06/1.30      inference('demod', [status(thm)], ['183', '184'])).
% 1.06/1.30  thf(t55_pre_topc, axiom,
% 1.06/1.30    (![A:$i]:
% 1.06/1.30     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.30       ( ![B:$i]:
% 1.06/1.30         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.06/1.30           ( ![C:$i]:
% 1.06/1.30             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 1.06/1.30               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 1.06/1.30  thf('186', plain,
% 1.06/1.30      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.06/1.30         ((v2_struct_0 @ X16)
% 1.06/1.30          | ~ (m1_pre_topc @ X16 @ X17)
% 1.06/1.30          | (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 1.06/1.30          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X16))
% 1.06/1.30          | ~ (l1_pre_topc @ X17)
% 1.06/1.30          | (v2_struct_0 @ X17))),
% 1.06/1.30      inference('cnf', [status(esa)], [t55_pre_topc])).
% 1.06/1.30  thf('187', plain,
% 1.06/1.30      (![X0 : $i]:
% 1.06/1.30         ((v2_struct_0 @ sk_A)
% 1.06/1.30          | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.30             sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30          | (v2_struct_0 @ sk_B_1)
% 1.06/1.30          | (v2_struct_0 @ X0)
% 1.06/1.30          | ~ (l1_pre_topc @ X0)
% 1.06/1.30          | (m1_subset_1 @ 
% 1.06/1.30             (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 1.06/1.30              sk_A) @ 
% 1.06/1.30             (u1_struct_0 @ X0))
% 1.06/1.30          | ~ (m1_pre_topc @ sk_B_1 @ X0)
% 1.06/1.30          | (v2_struct_0 @ sk_B_1))),
% 1.06/1.30      inference('sup-', [status(thm)], ['185', '186'])).
% 1.06/1.30  thf('188', plain,
% 1.06/1.30      (![X0 : $i]:
% 1.06/1.30         (~ (m1_pre_topc @ sk_B_1 @ X0)
% 1.06/1.30          | (m1_subset_1 @ 
% 1.06/1.30             (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 1.06/1.30              sk_A) @ 
% 1.06/1.30             (u1_struct_0 @ X0))
% 1.06/1.30          | ~ (l1_pre_topc @ X0)
% 1.06/1.30          | (v2_struct_0 @ X0)
% 1.06/1.30          | (v2_struct_0 @ sk_B_1)
% 1.06/1.30          | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.30             sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30          | (v2_struct_0 @ sk_A))),
% 1.06/1.30      inference('simplify', [status(thm)], ['187'])).
% 1.06/1.30  thf('189', plain,
% 1.06/1.30      (((v2_struct_0 @ sk_A)
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (v2_struct_0 @ sk_A)
% 1.06/1.30        | ~ (l1_pre_topc @ sk_A)
% 1.06/1.30        | (m1_subset_1 @ 
% 1.06/1.30           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 1.06/1.30           (u1_struct_0 @ sk_A)))),
% 1.06/1.30      inference('sup-', [status(thm)], ['164', '188'])).
% 1.06/1.30  thf('190', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('191', plain,
% 1.06/1.30      (((v2_struct_0 @ sk_A)
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (v2_struct_0 @ sk_A)
% 1.06/1.30        | (m1_subset_1 @ 
% 1.06/1.30           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 1.06/1.30           (u1_struct_0 @ sk_A)))),
% 1.06/1.30      inference('demod', [status(thm)], ['189', '190'])).
% 1.06/1.30  thf('192', plain,
% 1.06/1.30      (((m1_subset_1 @ 
% 1.06/1.30         (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 1.06/1.30         (u1_struct_0 @ sk_A))
% 1.06/1.30        | (v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_A))),
% 1.06/1.30      inference('simplify', [status(thm)], ['191'])).
% 1.06/1.30  thf('193', plain,
% 1.06/1.30      (((v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (r2_hidden @ 
% 1.06/1.30           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 1.06/1.30           (u1_struct_0 @ sk_B_1))
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_A))),
% 1.06/1.30      inference('demod', [status(thm)], ['158', '159'])).
% 1.06/1.30  thf('194', plain,
% 1.06/1.30      (![X50 : $i]:
% 1.06/1.30         (~ (r2_hidden @ X50 @ (u1_struct_0 @ sk_B_1))
% 1.06/1.30          | ((X50) = (k1_funct_1 @ sk_C @ X50))
% 1.06/1.30          | ~ (m1_subset_1 @ X50 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('195', plain,
% 1.06/1.30      (((v2_struct_0 @ sk_A)
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_B_1)
% 1.06/1.30        | ~ (m1_subset_1 @ 
% 1.06/1.30             (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 1.06/1.30              sk_A) @ 
% 1.06/1.30             (u1_struct_0 @ sk_A))
% 1.06/1.30        | ((sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A)
% 1.06/1.30            = (k1_funct_1 @ sk_C @ 
% 1.06/1.30               (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 1.06/1.30                sk_A))))),
% 1.06/1.30      inference('sup-', [status(thm)], ['193', '194'])).
% 1.06/1.30  thf('196', plain,
% 1.06/1.30      (((v2_struct_0 @ sk_A)
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_B_1)
% 1.06/1.30        | ((sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A)
% 1.06/1.30            = (k1_funct_1 @ sk_C @ 
% 1.06/1.30               (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 1.06/1.30                sk_A)))
% 1.06/1.30        | (v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_A))),
% 1.06/1.30      inference('sup-', [status(thm)], ['192', '195'])).
% 1.06/1.30  thf('197', plain,
% 1.06/1.30      ((((sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A)
% 1.06/1.30          = (k1_funct_1 @ sk_C @ 
% 1.06/1.30             (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 1.06/1.30              sk_A)))
% 1.06/1.30        | (v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_A))),
% 1.06/1.30      inference('simplify', [status(thm)], ['196'])).
% 1.06/1.30  thf('198', plain,
% 1.06/1.30      (((m1_subset_1 @ 
% 1.06/1.30         (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 1.06/1.30         (u1_struct_0 @ sk_A))
% 1.06/1.30        | (v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_A))),
% 1.06/1.30      inference('simplify', [status(thm)], ['191'])).
% 1.06/1.30  thf('199', plain,
% 1.06/1.30      (((v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (r2_hidden @ 
% 1.06/1.30           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 1.06/1.30           (u1_struct_0 @ sk_B_1))
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_A))),
% 1.06/1.30      inference('demod', [status(thm)], ['158', '159'])).
% 1.06/1.30  thf(t95_tmap_1, axiom,
% 1.06/1.30    (![A:$i]:
% 1.06/1.30     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.30       ( ![B:$i]:
% 1.06/1.30         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.06/1.30           ( ![C:$i]:
% 1.06/1.30             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.06/1.30               ( ( r2_hidden @ C @ ( u1_struct_0 @ B ) ) =>
% 1.06/1.30                 ( ( k1_funct_1 @ ( k4_tmap_1 @ A @ B ) @ C ) = ( C ) ) ) ) ) ) ) ))).
% 1.06/1.30  thf('200', plain,
% 1.06/1.30      (![X47 : $i, X48 : $i, X49 : $i]:
% 1.06/1.30         ((v2_struct_0 @ X47)
% 1.06/1.30          | ~ (m1_pre_topc @ X47 @ X48)
% 1.06/1.30          | ~ (r2_hidden @ X49 @ (u1_struct_0 @ X47))
% 1.06/1.30          | ((k1_funct_1 @ (k4_tmap_1 @ X48 @ X47) @ X49) = (X49))
% 1.06/1.30          | ~ (m1_subset_1 @ X49 @ (u1_struct_0 @ X48))
% 1.06/1.30          | ~ (l1_pre_topc @ X48)
% 1.06/1.30          | ~ (v2_pre_topc @ X48)
% 1.06/1.30          | (v2_struct_0 @ X48))),
% 1.06/1.30      inference('cnf', [status(esa)], [t95_tmap_1])).
% 1.06/1.30  thf('201', plain,
% 1.06/1.30      (![X0 : $i]:
% 1.06/1.30         ((v2_struct_0 @ sk_A)
% 1.06/1.30          | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.30             sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30          | (v2_struct_0 @ sk_B_1)
% 1.06/1.30          | (v2_struct_0 @ X0)
% 1.06/1.30          | ~ (v2_pre_topc @ X0)
% 1.06/1.30          | ~ (l1_pre_topc @ X0)
% 1.06/1.30          | ~ (m1_subset_1 @ 
% 1.06/1.30               (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 1.06/1.30                sk_A) @ 
% 1.06/1.30               (u1_struct_0 @ X0))
% 1.06/1.30          | ((k1_funct_1 @ (k4_tmap_1 @ X0 @ sk_B_1) @ 
% 1.06/1.30              (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 1.06/1.30               sk_A))
% 1.06/1.30              = (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 1.06/1.30                 sk_A))
% 1.06/1.30          | ~ (m1_pre_topc @ sk_B_1 @ X0)
% 1.06/1.30          | (v2_struct_0 @ sk_B_1))),
% 1.06/1.30      inference('sup-', [status(thm)], ['199', '200'])).
% 1.06/1.30  thf('202', plain,
% 1.06/1.30      (![X0 : $i]:
% 1.06/1.30         (~ (m1_pre_topc @ sk_B_1 @ X0)
% 1.06/1.30          | ((k1_funct_1 @ (k4_tmap_1 @ X0 @ sk_B_1) @ 
% 1.06/1.30              (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 1.06/1.30               sk_A))
% 1.06/1.30              = (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 1.06/1.30                 sk_A))
% 1.06/1.30          | ~ (m1_subset_1 @ 
% 1.06/1.30               (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 1.06/1.30                sk_A) @ 
% 1.06/1.30               (u1_struct_0 @ X0))
% 1.06/1.30          | ~ (l1_pre_topc @ X0)
% 1.06/1.30          | ~ (v2_pre_topc @ X0)
% 1.06/1.30          | (v2_struct_0 @ X0)
% 1.06/1.30          | (v2_struct_0 @ sk_B_1)
% 1.06/1.30          | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.30             sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30          | (v2_struct_0 @ sk_A))),
% 1.06/1.30      inference('simplify', [status(thm)], ['201'])).
% 1.06/1.30  thf('203', plain,
% 1.06/1.30      (((v2_struct_0 @ sk_A)
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (v2_struct_0 @ sk_A)
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (v2_struct_0 @ sk_A)
% 1.06/1.30        | ~ (v2_pre_topc @ sk_A)
% 1.06/1.30        | ~ (l1_pre_topc @ sk_A)
% 1.06/1.30        | ((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 1.06/1.30            (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A))
% 1.06/1.30            = (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 1.06/1.30               sk_A))
% 1.06/1.30        | ~ (m1_pre_topc @ sk_B_1 @ sk_A))),
% 1.06/1.30      inference('sup-', [status(thm)], ['198', '202'])).
% 1.06/1.30  thf('204', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('205', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('206', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('207', plain,
% 1.06/1.30      (((v2_struct_0 @ sk_A)
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (v2_struct_0 @ sk_A)
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (v2_struct_0 @ sk_A)
% 1.06/1.30        | ((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 1.06/1.30            (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A))
% 1.06/1.30            = (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 1.06/1.30               sk_A)))),
% 1.06/1.30      inference('demod', [status(thm)], ['203', '204', '205', '206'])).
% 1.06/1.30  thf('208', plain,
% 1.06/1.30      ((((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 1.06/1.30          (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A))
% 1.06/1.30          = (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A))
% 1.06/1.30        | (v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_A))),
% 1.06/1.30      inference('simplify', [status(thm)], ['207'])).
% 1.06/1.30  thf('209', plain,
% 1.06/1.30      (((v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (m1_subset_1 @ 
% 1.06/1.30           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A) @ 
% 1.06/1.30           (u1_struct_0 @ sk_B_1))
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_A))),
% 1.06/1.30      inference('demod', [status(thm)], ['183', '184'])).
% 1.06/1.30  thf('210', plain,
% 1.06/1.30      ((m1_subset_1 @ sk_C @ 
% 1.06/1.30        (k1_zfmisc_1 @ 
% 1.06/1.30         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf(redefinition_k3_funct_2, axiom,
% 1.06/1.30    (![A:$i,B:$i,C:$i,D:$i]:
% 1.06/1.30     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 1.06/1.30         ( v1_funct_2 @ C @ A @ B ) & 
% 1.06/1.30         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.06/1.30         ( m1_subset_1 @ D @ A ) ) =>
% 1.06/1.30       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 1.06/1.30  thf('211', plain,
% 1.06/1.30      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.06/1.30         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 1.06/1.30          | ~ (v1_funct_2 @ X3 @ X4 @ X5)
% 1.06/1.30          | ~ (v1_funct_1 @ X3)
% 1.06/1.30          | (v1_xboole_0 @ X4)
% 1.06/1.30          | ~ (m1_subset_1 @ X6 @ X4)
% 1.06/1.30          | ((k3_funct_2 @ X4 @ X5 @ X3 @ X6) = (k1_funct_1 @ X3 @ X6)))),
% 1.06/1.30      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 1.06/1.30  thf('212', plain,
% 1.06/1.30      (![X0 : $i]:
% 1.06/1.30         (((k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.30            sk_C @ X0) = (k1_funct_1 @ sk_C @ X0))
% 1.06/1.30          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 1.06/1.30          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 1.06/1.30          | ~ (v1_funct_1 @ sk_C)
% 1.06/1.30          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ 
% 1.06/1.30               (u1_struct_0 @ sk_A)))),
% 1.06/1.30      inference('sup-', [status(thm)], ['210', '211'])).
% 1.06/1.30  thf('213', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('214', plain,
% 1.06/1.30      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('215', plain,
% 1.06/1.30      (![X0 : $i]:
% 1.06/1.30         (((k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.30            sk_C @ X0) = (k1_funct_1 @ sk_C @ X0))
% 1.06/1.30          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 1.06/1.30          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 1.06/1.30      inference('demod', [status(thm)], ['212', '213', '214'])).
% 1.06/1.30  thf('216', plain,
% 1.06/1.30      (((v2_struct_0 @ sk_A)
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 1.06/1.30        | ((k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.30            sk_C @ 
% 1.06/1.30            (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A))
% 1.06/1.30            = (k1_funct_1 @ sk_C @ 
% 1.06/1.30               (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 1.06/1.30                sk_A))))),
% 1.06/1.30      inference('sup-', [status(thm)], ['209', '215'])).
% 1.06/1.30  thf('217', plain,
% 1.06/1.30      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 1.06/1.30         ((v2_struct_0 @ X35)
% 1.06/1.30          | ~ (v2_pre_topc @ X35)
% 1.06/1.30          | ~ (l1_pre_topc @ X35)
% 1.06/1.30          | ~ (v1_funct_1 @ X36)
% 1.06/1.30          | ~ (v1_funct_2 @ X36 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X37))
% 1.06/1.30          | ~ (m1_subset_1 @ X36 @ 
% 1.06/1.30               (k1_zfmisc_1 @ 
% 1.06/1.30                (k2_zfmisc_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X37))))
% 1.06/1.30          | ((k3_funct_2 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X37) @ X36 @ 
% 1.06/1.30              (sk_F @ X38 @ X36 @ X39 @ X35 @ X37))
% 1.06/1.30              != (k1_funct_1 @ X38 @ (sk_F @ X38 @ X36 @ X39 @ X35 @ X37)))
% 1.06/1.30          | (r2_funct_2 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X37) @ 
% 1.06/1.30             (k2_tmap_1 @ X35 @ X37 @ X36 @ X39) @ X38)
% 1.06/1.30          | ~ (m1_subset_1 @ X38 @ 
% 1.06/1.30               (k1_zfmisc_1 @ 
% 1.06/1.30                (k2_zfmisc_1 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X37))))
% 1.06/1.30          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X37))
% 1.06/1.30          | ~ (v1_funct_1 @ X38)
% 1.06/1.30          | ~ (m1_pre_topc @ X39 @ X35)
% 1.06/1.30          | (v2_struct_0 @ X39)
% 1.06/1.30          | ~ (l1_pre_topc @ X37)
% 1.06/1.30          | ~ (v2_pre_topc @ X37)
% 1.06/1.30          | (v2_struct_0 @ X37))),
% 1.06/1.30      inference('cnf', [status(esa)], [t59_tmap_1])).
% 1.06/1.30  thf('218', plain,
% 1.06/1.30      ((((k1_funct_1 @ sk_C @ 
% 1.06/1.30          (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A))
% 1.06/1.30          != (k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 1.06/1.30              (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 1.06/1.30               sk_A)))
% 1.06/1.30        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_A)
% 1.06/1.30        | (v2_struct_0 @ sk_A)
% 1.06/1.30        | ~ (v2_pre_topc @ sk_A)
% 1.06/1.30        | ~ (l1_pre_topc @ sk_A)
% 1.06/1.30        | (v2_struct_0 @ sk_B_1)
% 1.06/1.30        | ~ (m1_pre_topc @ sk_B_1 @ sk_B_1)
% 1.06/1.30        | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 1.06/1.30             (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 1.06/1.30        | ~ (m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 1.06/1.30             (k1_zfmisc_1 @ 
% 1.06/1.30              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.30           (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1) @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | ~ (m1_subset_1 @ sk_C @ 
% 1.06/1.30             (k1_zfmisc_1 @ 
% 1.06/1.30              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 1.06/1.30        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 1.06/1.30        | ~ (v1_funct_1 @ sk_C)
% 1.06/1.30        | ~ (l1_pre_topc @ sk_B_1)
% 1.06/1.30        | ~ (v2_pre_topc @ sk_B_1)
% 1.06/1.30        | (v2_struct_0 @ sk_B_1))),
% 1.06/1.30      inference('sup-', [status(thm)], ['216', '217'])).
% 1.06/1.30  thf('219', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('220', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('221', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1))),
% 1.06/1.30      inference('clc', [status(thm)], ['21', '22'])).
% 1.06/1.30  thf('222', plain,
% 1.06/1.30      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.06/1.30        (u1_struct_0 @ sk_A))),
% 1.06/1.30      inference('clc', [status(thm)], ['29', '30'])).
% 1.06/1.30  thf('223', plain,
% 1.06/1.30      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 1.06/1.30        (k1_zfmisc_1 @ 
% 1.06/1.30         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 1.06/1.30      inference('clc', [status(thm)], ['6', '7'])).
% 1.06/1.30  thf('224', plain, (((sk_C) = (k2_tmap_1 @ sk_B_1 @ sk_A @ sk_C @ sk_B_1))),
% 1.06/1.30      inference('demod', [status(thm)], ['151', '152'])).
% 1.06/1.30  thf('225', plain,
% 1.06/1.30      ((m1_subset_1 @ sk_C @ 
% 1.06/1.30        (k1_zfmisc_1 @ 
% 1.06/1.30         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('226', plain,
% 1.06/1.30      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('227', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('228', plain, ((l1_pre_topc @ sk_B_1)),
% 1.06/1.30      inference('demod', [status(thm)], ['44', '45'])).
% 1.06/1.30  thf('229', plain, ((v2_pre_topc @ sk_B_1)),
% 1.06/1.30      inference('demod', [status(thm)], ['49', '50', '51'])).
% 1.06/1.30  thf('230', plain,
% 1.06/1.30      ((((k1_funct_1 @ sk_C @ 
% 1.06/1.30          (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A))
% 1.06/1.30          != (k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 1.06/1.30              (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 1.06/1.30               sk_A)))
% 1.06/1.30        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_A)
% 1.06/1.30        | (v2_struct_0 @ sk_A)
% 1.06/1.30        | (v2_struct_0 @ sk_B_1)
% 1.06/1.30        | ~ (m1_pre_topc @ sk_B_1 @ sk_B_1)
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_B_1))),
% 1.06/1.30      inference('demod', [status(thm)],
% 1.06/1.30                ['218', '219', '220', '221', '222', '223', '224', '225', 
% 1.06/1.30                 '226', '227', '228', '229'])).
% 1.06/1.30  thf('231', plain,
% 1.06/1.30      ((~ (m1_pre_topc @ sk_B_1 @ sk_B_1)
% 1.06/1.30        | (v2_struct_0 @ sk_A)
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 1.06/1.30        | ((k1_funct_1 @ sk_C @ 
% 1.06/1.30            (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A))
% 1.06/1.30            != (k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B_1) @ 
% 1.06/1.30                (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 1.06/1.30                 sk_A))))),
% 1.06/1.30      inference('simplify', [status(thm)], ['230'])).
% 1.06/1.30  thf('232', plain,
% 1.06/1.30      ((((k1_funct_1 @ sk_C @ 
% 1.06/1.30          (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A))
% 1.06/1.30          != (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 1.06/1.30              sk_A))
% 1.06/1.30        | (v2_struct_0 @ sk_A)
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_A)
% 1.06/1.30        | ~ (m1_pre_topc @ sk_B_1 @ sk_B_1))),
% 1.06/1.30      inference('sup-', [status(thm)], ['208', '231'])).
% 1.06/1.30  thf('233', plain,
% 1.06/1.30      ((~ (m1_pre_topc @ sk_B_1 @ sk_B_1)
% 1.06/1.30        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_A)
% 1.06/1.30        | ((k1_funct_1 @ sk_C @ 
% 1.06/1.30            (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A))
% 1.06/1.30            != (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 1.06/1.30                sk_A)))),
% 1.06/1.30      inference('simplify', [status(thm)], ['232'])).
% 1.06/1.30  thf('234', plain,
% 1.06/1.30      ((((sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ sk_A)
% 1.06/1.30          != (sk_F @ (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C @ sk_B_1 @ sk_B_1 @ 
% 1.06/1.30              sk_A))
% 1.06/1.30        | (v2_struct_0 @ sk_A)
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (v2_struct_0 @ sk_A)
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 1.06/1.30        | ~ (m1_pre_topc @ sk_B_1 @ sk_B_1))),
% 1.06/1.30      inference('sup-', [status(thm)], ['197', '233'])).
% 1.06/1.30  thf('235', plain,
% 1.06/1.30      ((~ (m1_pre_topc @ sk_B_1 @ sk_B_1)
% 1.06/1.30        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_A))),
% 1.06/1.30      inference('simplify', [status(thm)], ['234'])).
% 1.06/1.30  thf('236', plain,
% 1.06/1.30      ((~ (l1_pre_topc @ sk_B_1)
% 1.06/1.30        | (v2_struct_0 @ sk_A)
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 1.06/1.30      inference('sup-', [status(thm)], ['163', '235'])).
% 1.06/1.30  thf('237', plain, ((l1_pre_topc @ sk_B_1)),
% 1.06/1.30      inference('demod', [status(thm)], ['44', '45'])).
% 1.06/1.30  thf('238', plain,
% 1.06/1.30      (((v2_struct_0 @ sk_A)
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 1.06/1.30      inference('demod', [status(thm)], ['236', '237'])).
% 1.06/1.30  thf('239', plain,
% 1.06/1.30      ((((sk_C) = (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.30             sk_C @ (k4_tmap_1 @ sk_A @ sk_B_1)))),
% 1.06/1.30      inference('demod', [status(thm)], ['15', '23', '31'])).
% 1.06/1.30  thf('240', plain,
% 1.06/1.30      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (v2_struct_0 @ sk_A)
% 1.06/1.30        | ((sk_C) = (k4_tmap_1 @ sk_A @ sk_B_1)))),
% 1.06/1.30      inference('sup-', [status(thm)], ['238', '239'])).
% 1.06/1.30  thf('241', plain,
% 1.06/1.30      (~ (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.30          (k4_tmap_1 @ sk_A @ sk_B_1) @ sk_C)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('242', plain,
% 1.06/1.30      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           sk_C)
% 1.06/1.30        | (v2_struct_0 @ sk_A)
% 1.06/1.30        | (v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 1.06/1.30      inference('sup-', [status(thm)], ['240', '241'])).
% 1.06/1.30  thf('243', plain,
% 1.06/1.30      ((m1_subset_1 @ sk_C @ 
% 1.06/1.30        (k1_zfmisc_1 @ 
% 1.06/1.30         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('244', plain,
% 1.06/1.30      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.06/1.30         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 1.06/1.30          | ~ (v1_funct_2 @ X7 @ X8 @ X9)
% 1.06/1.30          | ~ (v1_funct_1 @ X7)
% 1.06/1.30          | ~ (v1_funct_1 @ X10)
% 1.06/1.30          | ~ (v1_funct_2 @ X10 @ X8 @ X9)
% 1.06/1.30          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 1.06/1.30          | (r2_funct_2 @ X8 @ X9 @ X7 @ X10)
% 1.06/1.30          | ((X7) != (X10)))),
% 1.06/1.30      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 1.06/1.30  thf('245', plain,
% 1.06/1.30      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.06/1.30         ((r2_funct_2 @ X8 @ X9 @ X10 @ X10)
% 1.06/1.30          | ~ (v1_funct_1 @ X10)
% 1.06/1.30          | ~ (v1_funct_2 @ X10 @ X8 @ X9)
% 1.06/1.30          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 1.06/1.30      inference('simplify', [status(thm)], ['244'])).
% 1.06/1.30  thf('246', plain,
% 1.06/1.30      ((~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 1.06/1.30        | ~ (v1_funct_1 @ sk_C)
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           sk_C))),
% 1.06/1.30      inference('sup-', [status(thm)], ['243', '245'])).
% 1.06/1.30  thf('247', plain,
% 1.06/1.30      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('248', plain, ((v1_funct_1 @ sk_C)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('249', plain,
% 1.06/1.30      ((r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30        sk_C)),
% 1.06/1.30      inference('demod', [status(thm)], ['246', '247', '248'])).
% 1.06/1.30  thf('250', plain,
% 1.06/1.30      (((v2_struct_0 @ sk_A)
% 1.06/1.30        | (v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 1.06/1.30      inference('demod', [status(thm)], ['242', '249'])).
% 1.06/1.30  thf('251', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('252', plain,
% 1.06/1.30      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1)) | (v2_struct_0 @ sk_B_1))),
% 1.06/1.30      inference('clc', [status(thm)], ['250', '251'])).
% 1.06/1.30  thf('253', plain, (~ (v2_struct_0 @ sk_B_1)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('254', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 1.06/1.30      inference('clc', [status(thm)], ['252', '253'])).
% 1.06/1.30  thf('255', plain,
% 1.06/1.30      (((v2_struct_0 @ sk_A)
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1))
% 1.06/1.30        | (v2_struct_0 @ sk_B_1))),
% 1.06/1.30      inference('demod', [status(thm)], ['162', '254'])).
% 1.06/1.30  thf('256', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('257', plain,
% 1.06/1.30      (((v2_struct_0 @ sk_B_1)
% 1.06/1.30        | (r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30           (k4_tmap_1 @ sk_A @ sk_B_1)))),
% 1.06/1.30      inference('clc', [status(thm)], ['255', '256'])).
% 1.06/1.30  thf('258', plain, (~ (v2_struct_0 @ sk_B_1)),
% 1.06/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.30  thf('259', plain,
% 1.06/1.30      ((r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30        (k4_tmap_1 @ sk_A @ sk_B_1))),
% 1.06/1.30      inference('clc', [status(thm)], ['257', '258'])).
% 1.06/1.30  thf('260', plain, (((sk_C) = (k4_tmap_1 @ sk_A @ sk_B_1))),
% 1.06/1.30      inference('demod', [status(thm)], ['32', '259'])).
% 1.06/1.30  thf('261', plain,
% 1.06/1.30      ((r2_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.06/1.30        sk_C)),
% 1.06/1.30      inference('demod', [status(thm)], ['246', '247', '248'])).
% 1.06/1.30  thf('262', plain, ($false),
% 1.06/1.30      inference('demod', [status(thm)], ['0', '260', '261'])).
% 1.06/1.30  
% 1.06/1.30  % SZS output end Refutation
% 1.06/1.30  
% 1.06/1.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
