%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SyQ47syTsr

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:42 EST 2020

% Result     : Theorem 6.69s
% Output     : Refutation 6.69s
% Verified   : 
% Statistics : Number of formulae       :  358 (21512 expanded)
%              Number of leaves         :   36 (6250 expanded)
%              Depth                    :   45
%              Number of atoms          : 5764 (590338 expanded)
%              Number of equality atoms :   87 (11587 expanded)
%              Maximal formula depth    :   25 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k4_tmap_1_type,type,(
    k4_tmap_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
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
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ( m1_subset_1 @ ( k4_tmap_1 @ X25 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_tmap_1])).

thf('3',plain,
    ( ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
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
    ( ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ( X0 = X3 )
      | ~ ( r2_funct_2 @ X1 @ X2 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,
    ( ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_C
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ( v1_funct_1 @ ( k4_tmap_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_tmap_1])).

thf('18',plain,
    ( ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
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
    ( ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ( v1_funct_2 @ ( k4_tmap_1 @ X25 @ X26 ) @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_tmap_1])).

thf('26',plain,
    ( ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
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
    ( ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_C
      = ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','23','31'])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('33',plain,(
    ! [X27: $i] :
      ( ( m1_pre_topc @ X27 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('34',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X27: $i] :
      ( ( m1_pre_topc @ X27 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('36',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('37',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_tmap_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( v2_pre_topc @ B )
        & ( l1_pre_topc @ B )
        & ( m1_pre_topc @ C @ A )
        & ( m1_pre_topc @ D @ A )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
     => ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) )
        & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('40',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X21 @ X23 @ X22 @ X20 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X23 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['41','42','43','44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['38','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','53'])).

thf('55',plain,(
    ! [X27: $i] :
      ( ( m1_pre_topc @ X27 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('56',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('58',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_pre_topc @ X16 @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X18 )
      | ( ( k3_tmap_1 @ X17 @ X15 @ X18 @ X16 @ X19 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X15 ) @ X19 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( v1_funct_2 @ X19 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( m1_pre_topc @ X18 @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ X1 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_B )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ X1 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_B )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60','61','62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['55','69'])).

thf('71',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('72',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( l1_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('73',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X27: $i] :
      ( ( m1_pre_topc @ X27 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('78',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('79',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_pre_topc @ X12 @ X13 )
      | ( ( k2_tmap_1 @ X13 @ X11 @ X14 @ X12 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) @ X14 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('82',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( v2_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('83',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['73','74'])).

thf('88',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','86','87','88','89','90','91'])).

thf('93',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['77','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['73','74'])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C )
      = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['70','75','76','99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C )
    = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['54','102'])).

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

thf('104',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ( m1_subset_1 @ ( sk_F @ X31 @ X29 @ X32 @ X28 @ X30 ) @ ( u1_struct_0 @ X28 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X30 ) @ ( k2_tmap_1 @ X28 @ X30 @ X29 @ X32 ) @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_pre_topc @ X32 @ X28 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t59_tmap_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ X0 ) @ X1 )
      | ( m1_subset_1 @ ( sk_F @ X1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X21 @ X23 @ X22 @ X20 @ X24 ) @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['112','113','114','115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['109','117'])).

thf('119',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['118','119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['108','124'])).

thf('126',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C )
    = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('127',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X27: $i] :
      ( ( m1_pre_topc @ X27 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('129',plain,(
    ! [X27: $i] :
      ( ( m1_pre_topc @ X27 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('130',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X21 @ X23 @ X22 @ X20 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['132','133','134','135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['129','137'])).

thf('139',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['73','74'])).

thf('140',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['73','74'])).

thf('141',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['138','139','140','141'])).

thf('143',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['128','142'])).

thf('144',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['73','74'])).

thf('145',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['145','146'])).

thf('148',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X27: $i] :
      ( ( m1_pre_topc @ X27 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('151',plain,(
    ! [X27: $i] :
      ( ( m1_pre_topc @ X27 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ X1 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_B )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60','61','62','63'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['73','74'])).

thf('155',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['73','74'])).

thf('156',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['153','154','155','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['150','158'])).

thf('160',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['73','74'])).

thf('161',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('162',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C )
      = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['159','160','161'])).

thf('163',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C )
      = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ) ),
    inference(clc,[status(thm)],['162','163'])).

thf('165',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C )
    = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ),
    inference(clc,[status(thm)],['164','165'])).

thf('167',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['149','166'])).

thf('168',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['73','74'])).

thf('169',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ X0 ) @ X1 )
      | ( m1_subset_1 @ ( sk_F @ X1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['105','106','107','127','167','168','169'])).

thf('171',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['54','102'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('173',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_C
      = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['149','166'])).

thf('175',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('176',plain,
    ( ( sk_C
      = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['173','174','175'])).

thf('177',plain,(
    ! [X27: $i] :
      ( ( m1_pre_topc @ X27 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('178',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('179',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( v2_struct_0 @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X39 ) @ X40 @ ( k3_tmap_1 @ X42 @ X39 @ X41 @ X41 @ X40 ) )
      | ~ ( m1_pre_topc @ X41 @ X42 )
      | ( v2_struct_0 @ X41 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v2_pre_topc @ X42 )
      | ( v2_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t74_tmap_1])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ sk_C ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['180','181','182','183','184'])).

thf('186',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['177','185'])).

thf('187',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['73','74'])).

thf('188',plain,
    ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C )
    = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ),
    inference(clc,[status(thm)],['164','165'])).

thf('189',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['73','74'])).

thf('190',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('191',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['186','187','188','189','190'])).

thf('192',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['191'])).

thf('193',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ) ),
    inference(clc,[status(thm)],['192','193'])).

thf('195',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ),
    inference(clc,[status(thm)],['194','195'])).

thf('197',plain,
    ( sk_C
    = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['176','196'])).

thf('198',plain,
    ( sk_C
    = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['176','196'])).

thf('199',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( m1_subset_1 @ ( sk_F @ X1 @ sk_C @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['170','197','198'])).

thf('200',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','199'])).

thf('201',plain,
    ( sk_C
    = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['176','196'])).

thf('202',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('203',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('204',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['200','201','202','203'])).

thf('205',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['204'])).

thf('206',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','205'])).

thf('207',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['73','74'])).

thf('208',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['206','207'])).

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

thf('209',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( m1_pre_topc @ X8 @ X9 )
      | ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_pre_topc])).

thf('210',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['208','209'])).

thf('211',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['210'])).

thf('212',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','211'])).

thf('213',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['212','213'])).

thf('215',plain,
    ( ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['214'])).

thf('216',plain,(
    ! [X27: $i] :
      ( ( m1_pre_topc @ X27 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('217',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('218',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['54','102'])).

thf('219',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ( r2_hidden @ ( sk_F @ X31 @ X29 @ X32 @ X28 @ X30 ) @ ( u1_struct_0 @ X32 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X30 ) @ ( k2_tmap_1 @ X28 @ X30 @ X29 @ X32 ) @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_pre_topc @ X32 @ X28 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t59_tmap_1])).

thf('220',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_F @ X1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['218','219'])).

thf('221',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('224',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['149','166'])).

thf('225',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['73','74'])).

thf('226',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('227',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_F @ X1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['220','221','222','223','224','225','226'])).

thf('228',plain,
    ( sk_C
    = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['176','196'])).

thf('229',plain,
    ( sk_C
    = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['176','196'])).

thf('230',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_F @ X1 @ sk_C @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['227','228','229'])).

thf('231',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['217','230'])).

thf('232',plain,
    ( sk_C
    = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['176','196'])).

thf('233',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('234',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('235',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['231','232','233','234'])).

thf('236',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['235'])).

thf('237',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['216','236'])).

thf('238',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['73','74'])).

thf('239',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['237','238'])).

thf('240',plain,(
    ! [X49: $i] :
      ( ~ ( r2_hidden @ X49 @ ( u1_struct_0 @ sk_B ) )
      | ( X49
        = ( k1_funct_1 @ sk_C @ X49 ) )
      | ~ ( m1_subset_1 @ X49 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['239','240'])).

thf('242',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['215','241'])).

thf('243',plain,
    ( ( ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['242'])).

thf('244',plain,
    ( ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['214'])).

thf('245',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['237','238'])).

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

thf('246',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( v2_struct_0 @ X46 )
      | ~ ( m1_pre_topc @ X46 @ X47 )
      | ~ ( r2_hidden @ X48 @ ( u1_struct_0 @ X46 ) )
      | ( ( k1_funct_1 @ ( k4_tmap_1 @ X47 @ X46 ) @ X48 )
        = X48 )
      | ~ ( m1_subset_1 @ X48 @ ( u1_struct_0 @ X47 ) )
      | ~ ( l1_pre_topc @ X47 )
      | ~ ( v2_pre_topc @ X47 )
      | ( v2_struct_0 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t95_tmap_1])).

thf('247',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k1_funct_1 @ ( k4_tmap_1 @ X0 @ sk_B ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
        = ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['245','246'])).

thf('248',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( ( k1_funct_1 @ ( k4_tmap_1 @ X0 @ sk_B ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
        = ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['247'])).

thf('249',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
      = ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['244','248'])).

thf('250',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
      = ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['249','250','251','252'])).

thf('254',plain,
    ( ( ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
      = ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['253'])).

thf('255',plain,(
    ! [X27: $i] :
      ( ( m1_pre_topc @ X27 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('256',plain,(
    ! [X27: $i] :
      ( ( m1_pre_topc @ X27 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('257',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['237','238'])).

thf('258',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['206','207'])).

thf('259',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['54','102'])).

thf(t72_tmap_1,axiom,(
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
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( m1_pre_topc @ C @ D )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                           => ( ( r2_hidden @ F @ ( u1_struct_0 @ C ) )
                             => ( ( k3_funct_2 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ E @ F )
                                = ( k1_funct_1 @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) )).

thf('260',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( v2_struct_0 @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ( v2_struct_0 @ X34 )
      | ~ ( m1_pre_topc @ X34 @ X35 )
      | ~ ( m1_pre_topc @ X36 @ X34 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X34 ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) @ X38 @ X37 )
        = ( k1_funct_1 @ ( k3_tmap_1 @ X35 @ X33 @ X34 @ X36 @ X38 ) @ X37 ) )
      | ~ ( r2_hidden @ X37 @ ( u1_struct_0 @ X36 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( v1_funct_2 @ X38 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_pre_topc @ X36 @ X35 )
      | ( v2_struct_0 @ X36 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t72_tmap_1])).

thf('261',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ X2 )
        = ( k1_funct_1 @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ X1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ) @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ X1 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['259','260'])).

thf('262',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['149','166'])).

thf('263',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('264',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('266',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ X2 )
        = ( k1_funct_1 @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ X1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ) @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ X1 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['261','262','263','264','265'])).

thf('267',plain,
    ( sk_C
    = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['176','196'])).

thf('268',plain,
    ( sk_C
    = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['176','196'])).

thf('269',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ X2 )
        = ( k1_funct_1 @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ X1 @ sk_C ) @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ X1 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['266','267','268'])).

thf('270',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_B )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
        = ( k1_funct_1 @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ X1 @ sk_C ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['258','269'])).

thf('271',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( r2_hidden @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ X1 ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
        = ( k1_funct_1 @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ X1 @ sk_C ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['270'])).

thf('272',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ sk_B )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
        = ( k1_funct_1 @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['257','271'])).

thf('273',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
        = ( k1_funct_1 @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) )
      | ~ ( m1_pre_topc @ sk_B @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['272'])).

thf('274',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
        = ( k1_funct_1 @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['256','273'])).

thf('275',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['73','74'])).

thf('276',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
        = ( k1_funct_1 @ ( k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['274','275'])).

thf('277',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
      = ( k1_funct_1 @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['255','276'])).

thf('278',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['73','74'])).

thf('279',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('280',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['73','74'])).

thf('281',plain,
    ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C )
    = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ),
    inference(clc,[status(thm)],['164','165'])).

thf('282',plain,
    ( sk_C
    = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['176','196'])).

thf('283',plain,
    ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['281','282'])).

thf('284',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['277','278','279','280','283'])).

thf('285',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
      = ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['284'])).

thf('286',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X30 ) @ X29 @ ( sk_F @ X31 @ X29 @ X32 @ X28 @ X30 ) )
       != ( k1_funct_1 @ X31 @ ( sk_F @ X31 @ X29 @ X32 @ X28 @ X30 ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X30 ) @ ( k2_tmap_1 @ X28 @ X30 @ X29 @ X32 ) @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_pre_topc @ X32 @ X28 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t59_tmap_1])).

thf('287',plain,
    ( ( ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
     != ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ~ ( v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['285','286'])).

thf('288',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('289',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('290',plain,(
    v1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('291',plain,(
    v1_funct_2 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('292',plain,(
    m1_subset_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('293',plain,
    ( sk_C
    = ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['176','196'])).

thf('294',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('295',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('296',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('297',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['73','74'])).

thf('298',plain,(
    v2_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('299',plain,
    ( ( ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
     != ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['287','288','289','290','291','292','293','294','295','296','297','298'])).

thf('300',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
     != ( k1_funct_1 @ ( k4_tmap_1 @ sk_A @ sk_B ) @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['299'])).

thf('301',plain,
    ( ( ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
     != ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['254','300'])).

thf('302',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_funct_1 @ sk_C @ ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
     != ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['301'])).

thf('303',plain,
    ( ( ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A )
     != ( sk_F @ ( k4_tmap_1 @ sk_A @ sk_B ) @ sk_C @ sk_B @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['243','302'])).

thf('304',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['303'])).

thf('305',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','304'])).

thf('306',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['73','74'])).

thf('307',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['305','306'])).

thf('308',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('309',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['307','308'])).

thf('310',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('311',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['309','310'])).

thf('312',plain,
    ( sk_C
    = ( k4_tmap_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['32','311'])).

thf('313',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('314',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ( r2_funct_2 @ X1 @ X2 @ X0 @ X3 )
      | ( X0 != X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('315',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( r2_funct_2 @ X1 @ X2 @ X3 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['314'])).

thf('316',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['313','315'])).

thf('317',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('318',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('319',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['316','317','318'])).

thf('320',plain,(
    $false ),
    inference(demod,[status(thm)],['0','312','319'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SyQ47syTsr
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:56:41 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 6.69/6.85  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.69/6.85  % Solved by: fo/fo7.sh
% 6.69/6.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.69/6.85  % done 8367 iterations in 6.377s
% 6.69/6.85  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.69/6.85  % SZS output start Refutation
% 6.69/6.85  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 6.69/6.85  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 6.69/6.85  thf(k4_tmap_1_type, type, k4_tmap_1: $i > $i > $i).
% 6.69/6.85  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 6.69/6.85  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 6.69/6.85  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.69/6.85  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.69/6.85  thf(sk_A_type, type, sk_A: $i).
% 6.69/6.85  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 6.69/6.85  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 6.69/6.85  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 6.69/6.85  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 6.69/6.85  thf(sk_B_type, type, sk_B: $i).
% 6.69/6.85  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i > $i).
% 6.69/6.85  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 6.69/6.85  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 6.69/6.85  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 6.69/6.85  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.69/6.85  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.69/6.85  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 6.69/6.85  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 6.69/6.85  thf(sk_C_type, type, sk_C: $i).
% 6.69/6.85  thf(t96_tmap_1, conjecture,
% 6.69/6.85    (![A:$i]:
% 6.69/6.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.69/6.85       ( ![B:$i]:
% 6.69/6.85         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 6.69/6.85           ( ![C:$i]:
% 6.69/6.85             ( ( ( v1_funct_1 @ C ) & 
% 6.69/6.85                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 6.69/6.85                 ( m1_subset_1 @
% 6.69/6.85                   C @ 
% 6.69/6.85                   ( k1_zfmisc_1 @
% 6.69/6.85                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 6.69/6.85               ( ( ![D:$i]:
% 6.69/6.85                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 6.69/6.85                     ( ( r2_hidden @ D @ ( u1_struct_0 @ B ) ) =>
% 6.69/6.85                       ( ( D ) = ( k1_funct_1 @ C @ D ) ) ) ) ) =>
% 6.69/6.85                 ( r2_funct_2 @
% 6.69/6.85                   ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 6.69/6.85                   ( k4_tmap_1 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 6.69/6.85  thf(zf_stmt_0, negated_conjecture,
% 6.69/6.85    (~( ![A:$i]:
% 6.69/6.85        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 6.69/6.85            ( l1_pre_topc @ A ) ) =>
% 6.69/6.85          ( ![B:$i]:
% 6.69/6.85            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 6.69/6.85              ( ![C:$i]:
% 6.69/6.85                ( ( ( v1_funct_1 @ C ) & 
% 6.69/6.85                    ( v1_funct_2 @
% 6.69/6.85                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 6.69/6.85                    ( m1_subset_1 @
% 6.69/6.85                      C @ 
% 6.69/6.85                      ( k1_zfmisc_1 @
% 6.69/6.85                        ( k2_zfmisc_1 @
% 6.69/6.85                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 6.69/6.85                  ( ( ![D:$i]:
% 6.69/6.85                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 6.69/6.85                        ( ( r2_hidden @ D @ ( u1_struct_0 @ B ) ) =>
% 6.69/6.85                          ( ( D ) = ( k1_funct_1 @ C @ D ) ) ) ) ) =>
% 6.69/6.85                    ( r2_funct_2 @
% 6.69/6.85                      ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 6.69/6.85                      ( k4_tmap_1 @ A @ B ) @ C ) ) ) ) ) ) ) )),
% 6.69/6.85    inference('cnf.neg', [status(esa)], [t96_tmap_1])).
% 6.69/6.85  thf('0', plain,
% 6.69/6.85      (~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.69/6.85          (k4_tmap_1 @ sk_A @ sk_B) @ sk_C)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('1', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf(dt_k4_tmap_1, axiom,
% 6.69/6.85    (![A:$i,B:$i]:
% 6.69/6.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 6.69/6.85         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 6.69/6.85       ( ( v1_funct_1 @ ( k4_tmap_1 @ A @ B ) ) & 
% 6.69/6.85         ( v1_funct_2 @
% 6.69/6.85           ( k4_tmap_1 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 6.69/6.85         ( m1_subset_1 @
% 6.69/6.85           ( k4_tmap_1 @ A @ B ) @ 
% 6.69/6.85           ( k1_zfmisc_1 @
% 6.69/6.85             ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 6.69/6.85  thf('2', plain,
% 6.69/6.85      (![X25 : $i, X26 : $i]:
% 6.69/6.85         (~ (l1_pre_topc @ X25)
% 6.69/6.85          | ~ (v2_pre_topc @ X25)
% 6.69/6.85          | (v2_struct_0 @ X25)
% 6.69/6.85          | ~ (m1_pre_topc @ X26 @ X25)
% 6.69/6.85          | (m1_subset_1 @ (k4_tmap_1 @ X25 @ X26) @ 
% 6.69/6.85             (k1_zfmisc_1 @ 
% 6.69/6.85              (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25)))))),
% 6.69/6.85      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 6.69/6.85  thf('3', plain,
% 6.69/6.85      (((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 6.69/6.85         (k1_zfmisc_1 @ 
% 6.69/6.85          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 6.69/6.85        | (v2_struct_0 @ sk_A)
% 6.69/6.85        | ~ (v2_pre_topc @ sk_A)
% 6.69/6.85        | ~ (l1_pre_topc @ sk_A))),
% 6.69/6.85      inference('sup-', [status(thm)], ['1', '2'])).
% 6.69/6.85  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('6', plain,
% 6.69/6.85      (((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 6.69/6.85         (k1_zfmisc_1 @ 
% 6.69/6.85          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 6.69/6.85        | (v2_struct_0 @ sk_A))),
% 6.69/6.85      inference('demod', [status(thm)], ['3', '4', '5'])).
% 6.69/6.85  thf('7', plain, (~ (v2_struct_0 @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('8', plain,
% 6.69/6.85      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 6.69/6.85        (k1_zfmisc_1 @ 
% 6.69/6.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 6.69/6.85      inference('clc', [status(thm)], ['6', '7'])).
% 6.69/6.85  thf('9', plain,
% 6.69/6.85      ((m1_subset_1 @ sk_C @ 
% 6.69/6.85        (k1_zfmisc_1 @ 
% 6.69/6.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf(redefinition_r2_funct_2, axiom,
% 6.69/6.85    (![A:$i,B:$i,C:$i,D:$i]:
% 6.69/6.85     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.69/6.85         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.69/6.85         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 6.69/6.85         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.69/6.85       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 6.69/6.85  thf('10', plain,
% 6.69/6.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.69/6.85         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 6.69/6.85          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 6.69/6.85          | ~ (v1_funct_1 @ X0)
% 6.69/6.85          | ~ (v1_funct_1 @ X3)
% 6.69/6.85          | ~ (v1_funct_2 @ X3 @ X1 @ X2)
% 6.69/6.85          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 6.69/6.85          | ((X0) = (X3))
% 6.69/6.85          | ~ (r2_funct_2 @ X1 @ X2 @ X0 @ X3))),
% 6.69/6.85      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 6.69/6.85  thf('11', plain,
% 6.69/6.85      (![X0 : $i]:
% 6.69/6.85         (~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.85             X0)
% 6.69/6.85          | ((sk_C) = (X0))
% 6.69/6.85          | ~ (m1_subset_1 @ X0 @ 
% 6.69/6.85               (k1_zfmisc_1 @ 
% 6.69/6.85                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 6.69/6.85          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 6.69/6.85          | ~ (v1_funct_1 @ X0)
% 6.69/6.85          | ~ (v1_funct_1 @ sk_C)
% 6.69/6.85          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 6.69/6.85      inference('sup-', [status(thm)], ['9', '10'])).
% 6.69/6.85  thf('12', plain, ((v1_funct_1 @ sk_C)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('13', plain,
% 6.69/6.85      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('14', plain,
% 6.69/6.85      (![X0 : $i]:
% 6.69/6.85         (~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.85             X0)
% 6.69/6.85          | ((sk_C) = (X0))
% 6.69/6.85          | ~ (m1_subset_1 @ X0 @ 
% 6.69/6.85               (k1_zfmisc_1 @ 
% 6.69/6.85                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 6.69/6.85          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 6.69/6.85          | ~ (v1_funct_1 @ X0))),
% 6.69/6.85      inference('demod', [status(thm)], ['11', '12', '13'])).
% 6.69/6.85  thf('15', plain,
% 6.69/6.85      ((~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.85        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 6.69/6.85             (u1_struct_0 @ sk_A))
% 6.69/6.85        | ((sk_C) = (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.85        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.85             (k4_tmap_1 @ sk_A @ sk_B)))),
% 6.69/6.85      inference('sup-', [status(thm)], ['8', '14'])).
% 6.69/6.85  thf('16', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('17', plain,
% 6.69/6.85      (![X25 : $i, X26 : $i]:
% 6.69/6.85         (~ (l1_pre_topc @ X25)
% 6.69/6.85          | ~ (v2_pre_topc @ X25)
% 6.69/6.85          | (v2_struct_0 @ X25)
% 6.69/6.85          | ~ (m1_pre_topc @ X26 @ X25)
% 6.69/6.85          | (v1_funct_1 @ (k4_tmap_1 @ X25 @ X26)))),
% 6.69/6.85      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 6.69/6.85  thf('18', plain,
% 6.69/6.85      (((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.85        | (v2_struct_0 @ sk_A)
% 6.69/6.85        | ~ (v2_pre_topc @ sk_A)
% 6.69/6.85        | ~ (l1_pre_topc @ sk_A))),
% 6.69/6.85      inference('sup-', [status(thm)], ['16', '17'])).
% 6.69/6.85  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('21', plain,
% 6.69/6.85      (((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 6.69/6.85      inference('demod', [status(thm)], ['18', '19', '20'])).
% 6.69/6.85  thf('22', plain, (~ (v2_struct_0 @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('23', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 6.69/6.85      inference('clc', [status(thm)], ['21', '22'])).
% 6.69/6.85  thf('24', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('25', plain,
% 6.69/6.85      (![X25 : $i, X26 : $i]:
% 6.69/6.85         (~ (l1_pre_topc @ X25)
% 6.69/6.85          | ~ (v2_pre_topc @ X25)
% 6.69/6.85          | (v2_struct_0 @ X25)
% 6.69/6.85          | ~ (m1_pre_topc @ X26 @ X25)
% 6.69/6.85          | (v1_funct_2 @ (k4_tmap_1 @ X25 @ X26) @ (u1_struct_0 @ X26) @ 
% 6.69/6.85             (u1_struct_0 @ X25)))),
% 6.69/6.85      inference('cnf', [status(esa)], [dt_k4_tmap_1])).
% 6.69/6.85  thf('26', plain,
% 6.69/6.85      (((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 6.69/6.85         (u1_struct_0 @ sk_A))
% 6.69/6.85        | (v2_struct_0 @ sk_A)
% 6.69/6.85        | ~ (v2_pre_topc @ sk_A)
% 6.69/6.85        | ~ (l1_pre_topc @ sk_A))),
% 6.69/6.85      inference('sup-', [status(thm)], ['24', '25'])).
% 6.69/6.85  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('29', plain,
% 6.69/6.85      (((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 6.69/6.85         (u1_struct_0 @ sk_A))
% 6.69/6.85        | (v2_struct_0 @ sk_A))),
% 6.69/6.85      inference('demod', [status(thm)], ['26', '27', '28'])).
% 6.69/6.85  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('31', plain,
% 6.69/6.85      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 6.69/6.85        (u1_struct_0 @ sk_A))),
% 6.69/6.85      inference('clc', [status(thm)], ['29', '30'])).
% 6.69/6.85  thf('32', plain,
% 6.69/6.85      ((((sk_C) = (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.85        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.85             (k4_tmap_1 @ sk_A @ sk_B)))),
% 6.69/6.85      inference('demod', [status(thm)], ['15', '23', '31'])).
% 6.69/6.85  thf(t2_tsep_1, axiom,
% 6.69/6.85    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 6.69/6.85  thf('33', plain,
% 6.69/6.85      (![X27 : $i]: ((m1_pre_topc @ X27 @ X27) | ~ (l1_pre_topc @ X27))),
% 6.69/6.85      inference('cnf', [status(esa)], [t2_tsep_1])).
% 6.69/6.85  thf('34', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('35', plain,
% 6.69/6.85      (![X27 : $i]: ((m1_pre_topc @ X27 @ X27) | ~ (l1_pre_topc @ X27))),
% 6.69/6.85      inference('cnf', [status(esa)], [t2_tsep_1])).
% 6.69/6.85  thf('36', plain,
% 6.69/6.85      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 6.69/6.85        (k1_zfmisc_1 @ 
% 6.69/6.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 6.69/6.85      inference('clc', [status(thm)], ['6', '7'])).
% 6.69/6.85  thf('37', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('38', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('39', plain,
% 6.69/6.85      ((m1_subset_1 @ sk_C @ 
% 6.69/6.85        (k1_zfmisc_1 @ 
% 6.69/6.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf(dt_k3_tmap_1, axiom,
% 6.69/6.85    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 6.69/6.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 6.69/6.85         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 6.69/6.85         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & ( m1_pre_topc @ C @ A ) & 
% 6.69/6.85         ( m1_pre_topc @ D @ A ) & ( v1_funct_1 @ E ) & 
% 6.69/6.85         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 6.69/6.85         ( m1_subset_1 @
% 6.69/6.85           E @ 
% 6.69/6.85           ( k1_zfmisc_1 @
% 6.69/6.85             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 6.69/6.85       ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) ) & 
% 6.69/6.85         ( v1_funct_2 @
% 6.69/6.85           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ 
% 6.69/6.85           ( u1_struct_0 @ B ) ) & 
% 6.69/6.85         ( m1_subset_1 @
% 6.69/6.85           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 6.69/6.85           ( k1_zfmisc_1 @
% 6.69/6.85             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 6.69/6.85  thf('40', plain,
% 6.69/6.85      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 6.69/6.85         (~ (m1_pre_topc @ X20 @ X21)
% 6.69/6.85          | ~ (m1_pre_topc @ X22 @ X21)
% 6.69/6.85          | ~ (l1_pre_topc @ X23)
% 6.69/6.85          | ~ (v2_pre_topc @ X23)
% 6.69/6.85          | (v2_struct_0 @ X23)
% 6.69/6.85          | ~ (l1_pre_topc @ X21)
% 6.69/6.85          | ~ (v2_pre_topc @ X21)
% 6.69/6.85          | (v2_struct_0 @ X21)
% 6.69/6.85          | ~ (v1_funct_1 @ X24)
% 6.69/6.85          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))
% 6.69/6.85          | ~ (m1_subset_1 @ X24 @ 
% 6.69/6.85               (k1_zfmisc_1 @ 
% 6.69/6.85                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))))
% 6.69/6.85          | (m1_subset_1 @ (k3_tmap_1 @ X21 @ X23 @ X22 @ X20 @ X24) @ 
% 6.69/6.85             (k1_zfmisc_1 @ 
% 6.69/6.85              (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X23)))))),
% 6.69/6.85      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 6.69/6.85  thf('41', plain,
% 6.69/6.85      (![X0 : $i, X1 : $i]:
% 6.69/6.85         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 6.69/6.85           (k1_zfmisc_1 @ 
% 6.69/6.85            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 6.69/6.85          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 6.69/6.85          | ~ (v1_funct_1 @ sk_C)
% 6.69/6.85          | (v2_struct_0 @ X1)
% 6.69/6.85          | ~ (v2_pre_topc @ X1)
% 6.69/6.85          | ~ (l1_pre_topc @ X1)
% 6.69/6.85          | (v2_struct_0 @ sk_A)
% 6.69/6.85          | ~ (v2_pre_topc @ sk_A)
% 6.69/6.85          | ~ (l1_pre_topc @ sk_A)
% 6.69/6.85          | ~ (m1_pre_topc @ sk_B @ X1)
% 6.69/6.85          | ~ (m1_pre_topc @ X0 @ X1))),
% 6.69/6.85      inference('sup-', [status(thm)], ['39', '40'])).
% 6.69/6.85  thf('42', plain,
% 6.69/6.85      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('43', plain, ((v1_funct_1 @ sk_C)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('44', plain, ((v2_pre_topc @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('46', plain,
% 6.69/6.85      (![X0 : $i, X1 : $i]:
% 6.69/6.85         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 6.69/6.85           (k1_zfmisc_1 @ 
% 6.69/6.85            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 6.69/6.85          | (v2_struct_0 @ X1)
% 6.69/6.85          | ~ (v2_pre_topc @ X1)
% 6.69/6.85          | ~ (l1_pre_topc @ X1)
% 6.69/6.85          | (v2_struct_0 @ sk_A)
% 6.69/6.85          | ~ (m1_pre_topc @ sk_B @ X1)
% 6.69/6.85          | ~ (m1_pre_topc @ X0 @ X1))),
% 6.69/6.85      inference('demod', [status(thm)], ['41', '42', '43', '44', '45'])).
% 6.69/6.85  thf('47', plain,
% 6.69/6.85      (![X0 : $i]:
% 6.69/6.85         (~ (m1_pre_topc @ X0 @ sk_A)
% 6.69/6.85          | (v2_struct_0 @ sk_A)
% 6.69/6.85          | ~ (l1_pre_topc @ sk_A)
% 6.69/6.85          | ~ (v2_pre_topc @ sk_A)
% 6.69/6.85          | (v2_struct_0 @ sk_A)
% 6.69/6.85          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 6.69/6.85             (k1_zfmisc_1 @ 
% 6.69/6.85              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))))),
% 6.69/6.85      inference('sup-', [status(thm)], ['38', '46'])).
% 6.69/6.85  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('50', plain,
% 6.69/6.85      (![X0 : $i]:
% 6.69/6.85         (~ (m1_pre_topc @ X0 @ sk_A)
% 6.69/6.85          | (v2_struct_0 @ sk_A)
% 6.69/6.85          | (v2_struct_0 @ sk_A)
% 6.69/6.85          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 6.69/6.85             (k1_zfmisc_1 @ 
% 6.69/6.85              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))))),
% 6.69/6.85      inference('demod', [status(thm)], ['47', '48', '49'])).
% 6.69/6.85  thf('51', plain,
% 6.69/6.85      (![X0 : $i]:
% 6.69/6.85         ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 6.69/6.85           (k1_zfmisc_1 @ 
% 6.69/6.85            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 6.69/6.85          | (v2_struct_0 @ sk_A)
% 6.69/6.85          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 6.69/6.85      inference('simplify', [status(thm)], ['50'])).
% 6.69/6.85  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('53', plain,
% 6.69/6.85      (![X0 : $i]:
% 6.69/6.85         (~ (m1_pre_topc @ X0 @ sk_A)
% 6.69/6.85          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 6.69/6.85             (k1_zfmisc_1 @ 
% 6.69/6.85              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))))),
% 6.69/6.85      inference('clc', [status(thm)], ['51', '52'])).
% 6.69/6.85  thf('54', plain,
% 6.69/6.85      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 6.69/6.85        (k1_zfmisc_1 @ 
% 6.69/6.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 6.69/6.85      inference('sup-', [status(thm)], ['37', '53'])).
% 6.69/6.85  thf('55', plain,
% 6.69/6.85      (![X27 : $i]: ((m1_pre_topc @ X27 @ X27) | ~ (l1_pre_topc @ X27))),
% 6.69/6.85      inference('cnf', [status(esa)], [t2_tsep_1])).
% 6.69/6.85  thf('56', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('57', plain,
% 6.69/6.85      ((m1_subset_1 @ sk_C @ 
% 6.69/6.85        (k1_zfmisc_1 @ 
% 6.69/6.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf(d5_tmap_1, axiom,
% 6.69/6.85    (![A:$i]:
% 6.69/6.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.69/6.85       ( ![B:$i]:
% 6.69/6.85         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 6.69/6.85             ( l1_pre_topc @ B ) ) =>
% 6.69/6.85           ( ![C:$i]:
% 6.69/6.85             ( ( m1_pre_topc @ C @ A ) =>
% 6.69/6.85               ( ![D:$i]:
% 6.69/6.85                 ( ( m1_pre_topc @ D @ A ) =>
% 6.69/6.85                   ( ![E:$i]:
% 6.69/6.85                     ( ( ( v1_funct_1 @ E ) & 
% 6.69/6.85                         ( v1_funct_2 @
% 6.69/6.85                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 6.69/6.85                         ( m1_subset_1 @
% 6.69/6.85                           E @ 
% 6.69/6.85                           ( k1_zfmisc_1 @
% 6.69/6.85                             ( k2_zfmisc_1 @
% 6.69/6.85                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 6.69/6.85                       ( ( m1_pre_topc @ D @ C ) =>
% 6.69/6.85                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 6.69/6.85                           ( k2_partfun1 @
% 6.69/6.85                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 6.69/6.85                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 6.69/6.85  thf('58', plain,
% 6.69/6.85      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 6.69/6.85         ((v2_struct_0 @ X15)
% 6.69/6.85          | ~ (v2_pre_topc @ X15)
% 6.69/6.85          | ~ (l1_pre_topc @ X15)
% 6.69/6.85          | ~ (m1_pre_topc @ X16 @ X17)
% 6.69/6.85          | ~ (m1_pre_topc @ X16 @ X18)
% 6.69/6.85          | ((k3_tmap_1 @ X17 @ X15 @ X18 @ X16 @ X19)
% 6.69/6.85              = (k2_partfun1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X15) @ 
% 6.69/6.85                 X19 @ (u1_struct_0 @ X16)))
% 6.69/6.85          | ~ (m1_subset_1 @ X19 @ 
% 6.69/6.85               (k1_zfmisc_1 @ 
% 6.69/6.85                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X15))))
% 6.69/6.85          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X15))
% 6.69/6.85          | ~ (v1_funct_1 @ X19)
% 6.69/6.85          | ~ (m1_pre_topc @ X18 @ X17)
% 6.69/6.85          | ~ (l1_pre_topc @ X17)
% 6.69/6.85          | ~ (v2_pre_topc @ X17)
% 6.69/6.85          | (v2_struct_0 @ X17))),
% 6.69/6.85      inference('cnf', [status(esa)], [d5_tmap_1])).
% 6.69/6.85  thf('59', plain,
% 6.69/6.85      (![X0 : $i, X1 : $i]:
% 6.69/6.85         ((v2_struct_0 @ X0)
% 6.69/6.85          | ~ (v2_pre_topc @ X0)
% 6.69/6.85          | ~ (l1_pre_topc @ X0)
% 6.69/6.85          | ~ (m1_pre_topc @ sk_B @ X0)
% 6.69/6.85          | ~ (v1_funct_1 @ sk_C)
% 6.69/6.85          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 6.69/6.85          | ((k3_tmap_1 @ X0 @ sk_A @ sk_B @ X1 @ sk_C)
% 6.69/6.85              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.69/6.85                 sk_C @ (u1_struct_0 @ X1)))
% 6.69/6.85          | ~ (m1_pre_topc @ X1 @ sk_B)
% 6.69/6.85          | ~ (m1_pre_topc @ X1 @ X0)
% 6.69/6.85          | ~ (l1_pre_topc @ sk_A)
% 6.69/6.85          | ~ (v2_pre_topc @ sk_A)
% 6.69/6.85          | (v2_struct_0 @ sk_A))),
% 6.69/6.85      inference('sup-', [status(thm)], ['57', '58'])).
% 6.69/6.85  thf('60', plain, ((v1_funct_1 @ sk_C)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('61', plain,
% 6.69/6.85      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('63', plain, ((v2_pre_topc @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('64', plain,
% 6.69/6.85      (![X0 : $i, X1 : $i]:
% 6.69/6.85         ((v2_struct_0 @ X0)
% 6.69/6.85          | ~ (v2_pre_topc @ X0)
% 6.69/6.85          | ~ (l1_pre_topc @ X0)
% 6.69/6.85          | ~ (m1_pre_topc @ sk_B @ X0)
% 6.69/6.85          | ((k3_tmap_1 @ X0 @ sk_A @ sk_B @ X1 @ sk_C)
% 6.69/6.85              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.69/6.85                 sk_C @ (u1_struct_0 @ X1)))
% 6.69/6.85          | ~ (m1_pre_topc @ X1 @ sk_B)
% 6.69/6.85          | ~ (m1_pre_topc @ X1 @ X0)
% 6.69/6.85          | (v2_struct_0 @ sk_A))),
% 6.69/6.85      inference('demod', [status(thm)], ['59', '60', '61', '62', '63'])).
% 6.69/6.85  thf('65', plain,
% 6.69/6.85      (![X0 : $i]:
% 6.69/6.85         ((v2_struct_0 @ sk_A)
% 6.69/6.85          | ~ (m1_pre_topc @ X0 @ sk_A)
% 6.69/6.85          | ~ (m1_pre_topc @ X0 @ sk_B)
% 6.69/6.85          | ((k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C)
% 6.69/6.85              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.69/6.85                 sk_C @ (u1_struct_0 @ X0)))
% 6.69/6.85          | ~ (l1_pre_topc @ sk_A)
% 6.69/6.85          | ~ (v2_pre_topc @ sk_A)
% 6.69/6.85          | (v2_struct_0 @ sk_A))),
% 6.69/6.85      inference('sup-', [status(thm)], ['56', '64'])).
% 6.69/6.85  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('67', plain, ((v2_pre_topc @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('68', plain,
% 6.69/6.85      (![X0 : $i]:
% 6.69/6.85         ((v2_struct_0 @ sk_A)
% 6.69/6.85          | ~ (m1_pre_topc @ X0 @ sk_A)
% 6.69/6.85          | ~ (m1_pre_topc @ X0 @ sk_B)
% 6.69/6.85          | ((k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C)
% 6.69/6.85              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.69/6.85                 sk_C @ (u1_struct_0 @ X0)))
% 6.69/6.85          | (v2_struct_0 @ sk_A))),
% 6.69/6.85      inference('demod', [status(thm)], ['65', '66', '67'])).
% 6.69/6.85  thf('69', plain,
% 6.69/6.85      (![X0 : $i]:
% 6.69/6.85         (((k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C)
% 6.69/6.85            = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.69/6.85               sk_C @ (u1_struct_0 @ X0)))
% 6.69/6.85          | ~ (m1_pre_topc @ X0 @ sk_B)
% 6.69/6.85          | ~ (m1_pre_topc @ X0 @ sk_A)
% 6.69/6.85          | (v2_struct_0 @ sk_A))),
% 6.69/6.85      inference('simplify', [status(thm)], ['68'])).
% 6.69/6.85  thf('70', plain,
% 6.69/6.85      ((~ (l1_pre_topc @ sk_B)
% 6.69/6.85        | (v2_struct_0 @ sk_A)
% 6.69/6.85        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 6.69/6.85        | ((k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C)
% 6.69/6.85            = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.69/6.85               sk_C @ (u1_struct_0 @ sk_B))))),
% 6.69/6.85      inference('sup-', [status(thm)], ['55', '69'])).
% 6.69/6.85  thf('71', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf(dt_m1_pre_topc, axiom,
% 6.69/6.85    (![A:$i]:
% 6.69/6.85     ( ( l1_pre_topc @ A ) =>
% 6.69/6.85       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 6.69/6.85  thf('72', plain,
% 6.69/6.85      (![X6 : $i, X7 : $i]:
% 6.69/6.85         (~ (m1_pre_topc @ X6 @ X7) | (l1_pre_topc @ X6) | ~ (l1_pre_topc @ X7))),
% 6.69/6.85      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 6.69/6.85  thf('73', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 6.69/6.85      inference('sup-', [status(thm)], ['71', '72'])).
% 6.69/6.85  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('75', plain, ((l1_pre_topc @ sk_B)),
% 6.69/6.85      inference('demod', [status(thm)], ['73', '74'])).
% 6.69/6.85  thf('76', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('77', plain,
% 6.69/6.85      (![X27 : $i]: ((m1_pre_topc @ X27 @ X27) | ~ (l1_pre_topc @ X27))),
% 6.69/6.85      inference('cnf', [status(esa)], [t2_tsep_1])).
% 6.69/6.85  thf('78', plain,
% 6.69/6.85      ((m1_subset_1 @ sk_C @ 
% 6.69/6.85        (k1_zfmisc_1 @ 
% 6.69/6.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf(d4_tmap_1, axiom,
% 6.69/6.85    (![A:$i]:
% 6.69/6.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.69/6.85       ( ![B:$i]:
% 6.69/6.85         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 6.69/6.85             ( l1_pre_topc @ B ) ) =>
% 6.69/6.85           ( ![C:$i]:
% 6.69/6.85             ( ( ( v1_funct_1 @ C ) & 
% 6.69/6.85                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 6.69/6.85                 ( m1_subset_1 @
% 6.69/6.85                   C @ 
% 6.69/6.85                   ( k1_zfmisc_1 @
% 6.69/6.85                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 6.69/6.85               ( ![D:$i]:
% 6.69/6.85                 ( ( m1_pre_topc @ D @ A ) =>
% 6.69/6.85                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 6.69/6.85                     ( k2_partfun1 @
% 6.69/6.85                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 6.69/6.85                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 6.69/6.85  thf('79', plain,
% 6.69/6.85      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 6.69/6.85         ((v2_struct_0 @ X11)
% 6.69/6.85          | ~ (v2_pre_topc @ X11)
% 6.69/6.85          | ~ (l1_pre_topc @ X11)
% 6.69/6.85          | ~ (m1_pre_topc @ X12 @ X13)
% 6.69/6.85          | ((k2_tmap_1 @ X13 @ X11 @ X14 @ X12)
% 6.69/6.85              = (k2_partfun1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11) @ 
% 6.69/6.85                 X14 @ (u1_struct_0 @ X12)))
% 6.69/6.85          | ~ (m1_subset_1 @ X14 @ 
% 6.69/6.85               (k1_zfmisc_1 @ 
% 6.69/6.85                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))))
% 6.69/6.85          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))
% 6.69/6.85          | ~ (v1_funct_1 @ X14)
% 6.69/6.85          | ~ (l1_pre_topc @ X13)
% 6.69/6.85          | ~ (v2_pre_topc @ X13)
% 6.69/6.85          | (v2_struct_0 @ X13))),
% 6.69/6.85      inference('cnf', [status(esa)], [d4_tmap_1])).
% 6.69/6.85  thf('80', plain,
% 6.69/6.85      (![X0 : $i]:
% 6.69/6.85         ((v2_struct_0 @ sk_B)
% 6.69/6.85          | ~ (v2_pre_topc @ sk_B)
% 6.69/6.85          | ~ (l1_pre_topc @ sk_B)
% 6.69/6.85          | ~ (v1_funct_1 @ sk_C)
% 6.69/6.85          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 6.69/6.85          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0)
% 6.69/6.85              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.69/6.85                 sk_C @ (u1_struct_0 @ X0)))
% 6.69/6.85          | ~ (m1_pre_topc @ X0 @ sk_B)
% 6.69/6.85          | ~ (l1_pre_topc @ sk_A)
% 6.69/6.85          | ~ (v2_pre_topc @ sk_A)
% 6.69/6.85          | (v2_struct_0 @ sk_A))),
% 6.69/6.85      inference('sup-', [status(thm)], ['78', '79'])).
% 6.69/6.85  thf('81', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf(cc1_pre_topc, axiom,
% 6.69/6.85    (![A:$i]:
% 6.69/6.85     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.69/6.85       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 6.69/6.85  thf('82', plain,
% 6.69/6.85      (![X4 : $i, X5 : $i]:
% 6.69/6.85         (~ (m1_pre_topc @ X4 @ X5)
% 6.69/6.85          | (v2_pre_topc @ X4)
% 6.69/6.85          | ~ (l1_pre_topc @ X5)
% 6.69/6.85          | ~ (v2_pre_topc @ X5))),
% 6.69/6.85      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 6.69/6.85  thf('83', plain,
% 6.69/6.85      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_B))),
% 6.69/6.85      inference('sup-', [status(thm)], ['81', '82'])).
% 6.69/6.85  thf('84', plain, ((v2_pre_topc @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('86', plain, ((v2_pre_topc @ sk_B)),
% 6.69/6.85      inference('demod', [status(thm)], ['83', '84', '85'])).
% 6.69/6.85  thf('87', plain, ((l1_pre_topc @ sk_B)),
% 6.69/6.85      inference('demod', [status(thm)], ['73', '74'])).
% 6.69/6.85  thf('88', plain, ((v1_funct_1 @ sk_C)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('89', plain,
% 6.69/6.85      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('91', plain, ((v2_pre_topc @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('92', plain,
% 6.69/6.85      (![X0 : $i]:
% 6.69/6.85         ((v2_struct_0 @ sk_B)
% 6.69/6.85          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0)
% 6.69/6.85              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.69/6.85                 sk_C @ (u1_struct_0 @ X0)))
% 6.69/6.85          | ~ (m1_pre_topc @ X0 @ sk_B)
% 6.69/6.85          | (v2_struct_0 @ sk_A))),
% 6.69/6.85      inference('demod', [status(thm)],
% 6.69/6.85                ['80', '86', '87', '88', '89', '90', '91'])).
% 6.69/6.85  thf('93', plain,
% 6.69/6.85      ((~ (l1_pre_topc @ sk_B)
% 6.69/6.85        | (v2_struct_0 @ sk_A)
% 6.69/6.85        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B)
% 6.69/6.85            = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.69/6.85               sk_C @ (u1_struct_0 @ sk_B)))
% 6.69/6.85        | (v2_struct_0 @ sk_B))),
% 6.69/6.85      inference('sup-', [status(thm)], ['77', '92'])).
% 6.69/6.85  thf('94', plain, ((l1_pre_topc @ sk_B)),
% 6.69/6.85      inference('demod', [status(thm)], ['73', '74'])).
% 6.69/6.85  thf('95', plain,
% 6.69/6.85      (((v2_struct_0 @ sk_A)
% 6.69/6.85        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B)
% 6.69/6.85            = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.69/6.85               sk_C @ (u1_struct_0 @ sk_B)))
% 6.69/6.85        | (v2_struct_0 @ sk_B))),
% 6.69/6.85      inference('demod', [status(thm)], ['93', '94'])).
% 6.69/6.85  thf('96', plain, (~ (v2_struct_0 @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('97', plain,
% 6.69/6.85      (((v2_struct_0 @ sk_B)
% 6.69/6.85        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B)
% 6.69/6.85            = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.69/6.85               sk_C @ (u1_struct_0 @ sk_B))))),
% 6.69/6.85      inference('clc', [status(thm)], ['95', '96'])).
% 6.69/6.85  thf('98', plain, (~ (v2_struct_0 @ sk_B)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('99', plain,
% 6.69/6.85      (((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B)
% 6.69/6.85         = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.85            (u1_struct_0 @ sk_B)))),
% 6.69/6.85      inference('clc', [status(thm)], ['97', '98'])).
% 6.69/6.85  thf('100', plain,
% 6.69/6.85      (((v2_struct_0 @ sk_A)
% 6.69/6.85        | ((k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C)
% 6.69/6.85            = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B)))),
% 6.69/6.85      inference('demod', [status(thm)], ['70', '75', '76', '99'])).
% 6.69/6.85  thf('101', plain, (~ (v2_struct_0 @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('102', plain,
% 6.69/6.85      (((k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C)
% 6.69/6.85         = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))),
% 6.69/6.85      inference('clc', [status(thm)], ['100', '101'])).
% 6.69/6.85  thf('103', plain,
% 6.69/6.85      ((m1_subset_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ 
% 6.69/6.85        (k1_zfmisc_1 @ 
% 6.69/6.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 6.69/6.85      inference('demod', [status(thm)], ['54', '102'])).
% 6.69/6.85  thf(t59_tmap_1, axiom,
% 6.69/6.85    (![A:$i]:
% 6.69/6.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.69/6.85       ( ![B:$i]:
% 6.69/6.85         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 6.69/6.85             ( l1_pre_topc @ B ) ) =>
% 6.69/6.85           ( ![C:$i]:
% 6.69/6.85             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 6.69/6.85               ( ![D:$i]:
% 6.69/6.85                 ( ( ( v1_funct_1 @ D ) & 
% 6.69/6.85                     ( v1_funct_2 @
% 6.69/6.85                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 6.69/6.85                     ( m1_subset_1 @
% 6.69/6.85                       D @ 
% 6.69/6.85                       ( k1_zfmisc_1 @
% 6.69/6.85                         ( k2_zfmisc_1 @
% 6.69/6.85                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 6.69/6.85                   ( ![E:$i]:
% 6.69/6.85                     ( ( ( v1_funct_1 @ E ) & 
% 6.69/6.85                         ( v1_funct_2 @
% 6.69/6.85                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) & 
% 6.69/6.85                         ( m1_subset_1 @
% 6.69/6.85                           E @ 
% 6.69/6.85                           ( k1_zfmisc_1 @
% 6.69/6.85                             ( k2_zfmisc_1 @
% 6.69/6.85                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 6.69/6.85                       ( ( ![F:$i]:
% 6.69/6.85                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 6.69/6.85                             ( ( r2_hidden @ F @ ( u1_struct_0 @ C ) ) =>
% 6.69/6.85                               ( ( k3_funct_2 @
% 6.69/6.85                                   ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 6.69/6.85                                   D @ F ) =
% 6.69/6.85                                 ( k1_funct_1 @ E @ F ) ) ) ) ) =>
% 6.69/6.85                         ( r2_funct_2 @
% 6.69/6.85                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 6.69/6.85                           ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ))).
% 6.69/6.85  thf('104', plain,
% 6.69/6.85      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 6.69/6.85         ((v2_struct_0 @ X28)
% 6.69/6.85          | ~ (v2_pre_topc @ X28)
% 6.69/6.85          | ~ (l1_pre_topc @ X28)
% 6.69/6.85          | ~ (v1_funct_1 @ X29)
% 6.69/6.85          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X30))
% 6.69/6.85          | ~ (m1_subset_1 @ X29 @ 
% 6.69/6.85               (k1_zfmisc_1 @ 
% 6.69/6.85                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X30))))
% 6.69/6.85          | (m1_subset_1 @ (sk_F @ X31 @ X29 @ X32 @ X28 @ X30) @ 
% 6.69/6.85             (u1_struct_0 @ X28))
% 6.69/6.85          | (r2_funct_2 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X30) @ 
% 6.69/6.85             (k2_tmap_1 @ X28 @ X30 @ X29 @ X32) @ X31)
% 6.69/6.85          | ~ (m1_subset_1 @ X31 @ 
% 6.69/6.85               (k1_zfmisc_1 @ 
% 6.69/6.85                (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X30))))
% 6.69/6.85          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X30))
% 6.69/6.85          | ~ (v1_funct_1 @ X31)
% 6.69/6.85          | ~ (m1_pre_topc @ X32 @ X28)
% 6.69/6.85          | (v2_struct_0 @ X32)
% 6.69/6.85          | ~ (l1_pre_topc @ X30)
% 6.69/6.85          | ~ (v2_pre_topc @ X30)
% 6.69/6.85          | (v2_struct_0 @ X30))),
% 6.69/6.85      inference('cnf', [status(esa)], [t59_tmap_1])).
% 6.69/6.85  thf('105', plain,
% 6.69/6.85      (![X0 : $i, X1 : $i]:
% 6.69/6.85         ((v2_struct_0 @ sk_A)
% 6.69/6.85          | ~ (v2_pre_topc @ sk_A)
% 6.69/6.85          | ~ (l1_pre_topc @ sk_A)
% 6.69/6.85          | (v2_struct_0 @ X0)
% 6.69/6.85          | ~ (m1_pre_topc @ X0 @ sk_B)
% 6.69/6.85          | ~ (v1_funct_1 @ X1)
% 6.69/6.85          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 6.69/6.85          | ~ (m1_subset_1 @ X1 @ 
% 6.69/6.85               (k1_zfmisc_1 @ 
% 6.69/6.85                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 6.69/6.85          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 6.69/6.85             (k2_tmap_1 @ sk_B @ sk_A @ 
% 6.69/6.85              (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ X0) @ 
% 6.69/6.85             X1)
% 6.69/6.85          | (m1_subset_1 @ 
% 6.69/6.85             (sk_F @ X1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ X0 @ 
% 6.69/6.85              sk_B @ sk_A) @ 
% 6.69/6.85             (u1_struct_0 @ sk_B))
% 6.69/6.85          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ 
% 6.69/6.85               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 6.69/6.85          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 6.69/6.85          | ~ (l1_pre_topc @ sk_B)
% 6.69/6.85          | ~ (v2_pre_topc @ sk_B)
% 6.69/6.85          | (v2_struct_0 @ sk_B))),
% 6.69/6.85      inference('sup-', [status(thm)], ['103', '104'])).
% 6.69/6.85  thf('106', plain, ((v2_pre_topc @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('107', plain, ((l1_pre_topc @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('108', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('109', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('110', plain,
% 6.69/6.85      ((m1_subset_1 @ sk_C @ 
% 6.69/6.85        (k1_zfmisc_1 @ 
% 6.69/6.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('111', plain,
% 6.69/6.85      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 6.69/6.85         (~ (m1_pre_topc @ X20 @ X21)
% 6.69/6.85          | ~ (m1_pre_topc @ X22 @ X21)
% 6.69/6.85          | ~ (l1_pre_topc @ X23)
% 6.69/6.85          | ~ (v2_pre_topc @ X23)
% 6.69/6.85          | (v2_struct_0 @ X23)
% 6.69/6.85          | ~ (l1_pre_topc @ X21)
% 6.69/6.85          | ~ (v2_pre_topc @ X21)
% 6.69/6.85          | (v2_struct_0 @ X21)
% 6.69/6.85          | ~ (v1_funct_1 @ X24)
% 6.69/6.85          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))
% 6.69/6.85          | ~ (m1_subset_1 @ X24 @ 
% 6.69/6.85               (k1_zfmisc_1 @ 
% 6.69/6.85                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))))
% 6.69/6.85          | (v1_funct_2 @ (k3_tmap_1 @ X21 @ X23 @ X22 @ X20 @ X24) @ 
% 6.69/6.85             (u1_struct_0 @ X20) @ (u1_struct_0 @ X23)))),
% 6.69/6.85      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 6.69/6.85  thf('112', plain,
% 6.69/6.85      (![X0 : $i, X1 : $i]:
% 6.69/6.85         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 6.69/6.85           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 6.69/6.85          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 6.69/6.85          | ~ (v1_funct_1 @ sk_C)
% 6.69/6.85          | (v2_struct_0 @ X1)
% 6.69/6.85          | ~ (v2_pre_topc @ X1)
% 6.69/6.85          | ~ (l1_pre_topc @ X1)
% 6.69/6.85          | (v2_struct_0 @ sk_A)
% 6.69/6.85          | ~ (v2_pre_topc @ sk_A)
% 6.69/6.85          | ~ (l1_pre_topc @ sk_A)
% 6.69/6.85          | ~ (m1_pre_topc @ sk_B @ X1)
% 6.69/6.85          | ~ (m1_pre_topc @ X0 @ X1))),
% 6.69/6.85      inference('sup-', [status(thm)], ['110', '111'])).
% 6.69/6.85  thf('113', plain,
% 6.69/6.85      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('114', plain, ((v1_funct_1 @ sk_C)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('115', plain, ((v2_pre_topc @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('116', plain, ((l1_pre_topc @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('117', plain,
% 6.69/6.85      (![X0 : $i, X1 : $i]:
% 6.69/6.85         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 6.69/6.85           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 6.69/6.85          | (v2_struct_0 @ X1)
% 6.69/6.85          | ~ (v2_pre_topc @ X1)
% 6.69/6.85          | ~ (l1_pre_topc @ X1)
% 6.69/6.85          | (v2_struct_0 @ sk_A)
% 6.69/6.85          | ~ (m1_pre_topc @ sk_B @ X1)
% 6.69/6.85          | ~ (m1_pre_topc @ X0 @ X1))),
% 6.69/6.85      inference('demod', [status(thm)], ['112', '113', '114', '115', '116'])).
% 6.69/6.85  thf('118', plain,
% 6.69/6.85      (![X0 : $i]:
% 6.69/6.85         (~ (m1_pre_topc @ X0 @ sk_A)
% 6.69/6.85          | (v2_struct_0 @ sk_A)
% 6.69/6.85          | ~ (l1_pre_topc @ sk_A)
% 6.69/6.85          | ~ (v2_pre_topc @ sk_A)
% 6.69/6.85          | (v2_struct_0 @ sk_A)
% 6.69/6.85          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 6.69/6.85             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))),
% 6.69/6.85      inference('sup-', [status(thm)], ['109', '117'])).
% 6.69/6.85  thf('119', plain, ((l1_pre_topc @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('120', plain, ((v2_pre_topc @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('121', plain,
% 6.69/6.85      (![X0 : $i]:
% 6.69/6.85         (~ (m1_pre_topc @ X0 @ sk_A)
% 6.69/6.85          | (v2_struct_0 @ sk_A)
% 6.69/6.85          | (v2_struct_0 @ sk_A)
% 6.69/6.85          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 6.69/6.85             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))),
% 6.69/6.85      inference('demod', [status(thm)], ['118', '119', '120'])).
% 6.69/6.85  thf('122', plain,
% 6.69/6.85      (![X0 : $i]:
% 6.69/6.85         ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 6.69/6.85           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 6.69/6.85          | (v2_struct_0 @ sk_A)
% 6.69/6.85          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 6.69/6.85      inference('simplify', [status(thm)], ['121'])).
% 6.69/6.85  thf('123', plain, (~ (v2_struct_0 @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('124', plain,
% 6.69/6.85      (![X0 : $i]:
% 6.69/6.85         (~ (m1_pre_topc @ X0 @ sk_A)
% 6.69/6.85          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ X0 @ sk_C) @ 
% 6.69/6.85             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))),
% 6.69/6.85      inference('clc', [status(thm)], ['122', '123'])).
% 6.69/6.85  thf('125', plain,
% 6.69/6.85      ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 6.69/6.85        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 6.69/6.85      inference('sup-', [status(thm)], ['108', '124'])).
% 6.69/6.85  thf('126', plain,
% 6.69/6.85      (((k3_tmap_1 @ sk_A @ sk_A @ sk_B @ sk_B @ sk_C)
% 6.69/6.85         = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))),
% 6.69/6.85      inference('clc', [status(thm)], ['100', '101'])).
% 6.69/6.85  thf('127', plain,
% 6.69/6.85      ((v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ 
% 6.69/6.85        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 6.69/6.85      inference('demod', [status(thm)], ['125', '126'])).
% 6.69/6.85  thf('128', plain,
% 6.69/6.85      (![X27 : $i]: ((m1_pre_topc @ X27 @ X27) | ~ (l1_pre_topc @ X27))),
% 6.69/6.85      inference('cnf', [status(esa)], [t2_tsep_1])).
% 6.69/6.85  thf('129', plain,
% 6.69/6.85      (![X27 : $i]: ((m1_pre_topc @ X27 @ X27) | ~ (l1_pre_topc @ X27))),
% 6.69/6.85      inference('cnf', [status(esa)], [t2_tsep_1])).
% 6.69/6.85  thf('130', plain,
% 6.69/6.85      ((m1_subset_1 @ sk_C @ 
% 6.69/6.85        (k1_zfmisc_1 @ 
% 6.69/6.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('131', plain,
% 6.69/6.85      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 6.69/6.85         (~ (m1_pre_topc @ X20 @ X21)
% 6.69/6.85          | ~ (m1_pre_topc @ X22 @ X21)
% 6.69/6.85          | ~ (l1_pre_topc @ X23)
% 6.69/6.85          | ~ (v2_pre_topc @ X23)
% 6.69/6.85          | (v2_struct_0 @ X23)
% 6.69/6.85          | ~ (l1_pre_topc @ X21)
% 6.69/6.85          | ~ (v2_pre_topc @ X21)
% 6.69/6.85          | (v2_struct_0 @ X21)
% 6.69/6.85          | ~ (v1_funct_1 @ X24)
% 6.69/6.85          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))
% 6.69/6.85          | ~ (m1_subset_1 @ X24 @ 
% 6.69/6.85               (k1_zfmisc_1 @ 
% 6.69/6.85                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))))
% 6.69/6.85          | (v1_funct_1 @ (k3_tmap_1 @ X21 @ X23 @ X22 @ X20 @ X24)))),
% 6.69/6.85      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 6.69/6.85  thf('132', plain,
% 6.69/6.85      (![X0 : $i, X1 : $i]:
% 6.69/6.85         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C))
% 6.69/6.85          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 6.69/6.85          | ~ (v1_funct_1 @ sk_C)
% 6.69/6.85          | (v2_struct_0 @ X1)
% 6.69/6.85          | ~ (v2_pre_topc @ X1)
% 6.69/6.85          | ~ (l1_pre_topc @ X1)
% 6.69/6.85          | (v2_struct_0 @ sk_A)
% 6.69/6.85          | ~ (v2_pre_topc @ sk_A)
% 6.69/6.85          | ~ (l1_pre_topc @ sk_A)
% 6.69/6.85          | ~ (m1_pre_topc @ sk_B @ X1)
% 6.69/6.85          | ~ (m1_pre_topc @ X0 @ X1))),
% 6.69/6.85      inference('sup-', [status(thm)], ['130', '131'])).
% 6.69/6.85  thf('133', plain,
% 6.69/6.85      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('134', plain, ((v1_funct_1 @ sk_C)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('135', plain, ((v2_pre_topc @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('136', plain, ((l1_pre_topc @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('137', plain,
% 6.69/6.85      (![X0 : $i, X1 : $i]:
% 6.69/6.85         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_A @ sk_B @ X0 @ sk_C))
% 6.69/6.85          | (v2_struct_0 @ X1)
% 6.69/6.85          | ~ (v2_pre_topc @ X1)
% 6.69/6.85          | ~ (l1_pre_topc @ X1)
% 6.69/6.85          | (v2_struct_0 @ sk_A)
% 6.69/6.85          | ~ (m1_pre_topc @ sk_B @ X1)
% 6.69/6.85          | ~ (m1_pre_topc @ X0 @ X1))),
% 6.69/6.85      inference('demod', [status(thm)], ['132', '133', '134', '135', '136'])).
% 6.69/6.85  thf('138', plain,
% 6.69/6.85      (![X0 : $i]:
% 6.69/6.85         (~ (l1_pre_topc @ sk_B)
% 6.69/6.85          | ~ (m1_pre_topc @ X0 @ sk_B)
% 6.69/6.85          | (v2_struct_0 @ sk_A)
% 6.69/6.85          | ~ (l1_pre_topc @ sk_B)
% 6.69/6.85          | ~ (v2_pre_topc @ sk_B)
% 6.69/6.85          | (v2_struct_0 @ sk_B)
% 6.69/6.85          | (v1_funct_1 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C)))),
% 6.69/6.85      inference('sup-', [status(thm)], ['129', '137'])).
% 6.69/6.85  thf('139', plain, ((l1_pre_topc @ sk_B)),
% 6.69/6.85      inference('demod', [status(thm)], ['73', '74'])).
% 6.69/6.85  thf('140', plain, ((l1_pre_topc @ sk_B)),
% 6.69/6.85      inference('demod', [status(thm)], ['73', '74'])).
% 6.69/6.85  thf('141', plain, ((v2_pre_topc @ sk_B)),
% 6.69/6.85      inference('demod', [status(thm)], ['83', '84', '85'])).
% 6.69/6.85  thf('142', plain,
% 6.69/6.85      (![X0 : $i]:
% 6.69/6.85         (~ (m1_pre_topc @ X0 @ sk_B)
% 6.69/6.85          | (v2_struct_0 @ sk_A)
% 6.69/6.85          | (v2_struct_0 @ sk_B)
% 6.69/6.85          | (v1_funct_1 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C)))),
% 6.69/6.85      inference('demod', [status(thm)], ['138', '139', '140', '141'])).
% 6.69/6.85  thf('143', plain,
% 6.69/6.85      ((~ (l1_pre_topc @ sk_B)
% 6.69/6.85        | (v1_funct_1 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C))
% 6.69/6.85        | (v2_struct_0 @ sk_B)
% 6.69/6.85        | (v2_struct_0 @ sk_A))),
% 6.69/6.85      inference('sup-', [status(thm)], ['128', '142'])).
% 6.69/6.85  thf('144', plain, ((l1_pre_topc @ sk_B)),
% 6.69/6.85      inference('demod', [status(thm)], ['73', '74'])).
% 6.69/6.85  thf('145', plain,
% 6.69/6.85      (((v1_funct_1 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C))
% 6.69/6.85        | (v2_struct_0 @ sk_B)
% 6.69/6.85        | (v2_struct_0 @ sk_A))),
% 6.69/6.85      inference('demod', [status(thm)], ['143', '144'])).
% 6.69/6.85  thf('146', plain, (~ (v2_struct_0 @ sk_B)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('147', plain,
% 6.69/6.85      (((v2_struct_0 @ sk_A)
% 6.69/6.85        | (v1_funct_1 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C)))),
% 6.69/6.85      inference('clc', [status(thm)], ['145', '146'])).
% 6.69/6.85  thf('148', plain, (~ (v2_struct_0 @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('149', plain,
% 6.69/6.85      ((v1_funct_1 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C))),
% 6.69/6.85      inference('clc', [status(thm)], ['147', '148'])).
% 6.69/6.85  thf('150', plain,
% 6.69/6.85      (![X27 : $i]: ((m1_pre_topc @ X27 @ X27) | ~ (l1_pre_topc @ X27))),
% 6.69/6.85      inference('cnf', [status(esa)], [t2_tsep_1])).
% 6.69/6.85  thf('151', plain,
% 6.69/6.85      (![X27 : $i]: ((m1_pre_topc @ X27 @ X27) | ~ (l1_pre_topc @ X27))),
% 6.69/6.85      inference('cnf', [status(esa)], [t2_tsep_1])).
% 6.69/6.85  thf('152', plain,
% 6.69/6.85      (![X0 : $i, X1 : $i]:
% 6.69/6.85         ((v2_struct_0 @ X0)
% 6.69/6.85          | ~ (v2_pre_topc @ X0)
% 6.69/6.85          | ~ (l1_pre_topc @ X0)
% 6.69/6.85          | ~ (m1_pre_topc @ sk_B @ X0)
% 6.69/6.85          | ((k3_tmap_1 @ X0 @ sk_A @ sk_B @ X1 @ sk_C)
% 6.69/6.85              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.69/6.85                 sk_C @ (u1_struct_0 @ X1)))
% 6.69/6.85          | ~ (m1_pre_topc @ X1 @ sk_B)
% 6.69/6.85          | ~ (m1_pre_topc @ X1 @ X0)
% 6.69/6.85          | (v2_struct_0 @ sk_A))),
% 6.69/6.85      inference('demod', [status(thm)], ['59', '60', '61', '62', '63'])).
% 6.69/6.85  thf('153', plain,
% 6.69/6.85      (![X0 : $i]:
% 6.69/6.85         (~ (l1_pre_topc @ sk_B)
% 6.69/6.85          | (v2_struct_0 @ sk_A)
% 6.69/6.85          | ~ (m1_pre_topc @ X0 @ sk_B)
% 6.69/6.85          | ~ (m1_pre_topc @ X0 @ sk_B)
% 6.69/6.85          | ((k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C)
% 6.69/6.85              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.69/6.85                 sk_C @ (u1_struct_0 @ X0)))
% 6.69/6.85          | ~ (l1_pre_topc @ sk_B)
% 6.69/6.85          | ~ (v2_pre_topc @ sk_B)
% 6.69/6.85          | (v2_struct_0 @ sk_B))),
% 6.69/6.85      inference('sup-', [status(thm)], ['151', '152'])).
% 6.69/6.85  thf('154', plain, ((l1_pre_topc @ sk_B)),
% 6.69/6.85      inference('demod', [status(thm)], ['73', '74'])).
% 6.69/6.85  thf('155', plain, ((l1_pre_topc @ sk_B)),
% 6.69/6.85      inference('demod', [status(thm)], ['73', '74'])).
% 6.69/6.85  thf('156', plain, ((v2_pre_topc @ sk_B)),
% 6.69/6.85      inference('demod', [status(thm)], ['83', '84', '85'])).
% 6.69/6.85  thf('157', plain,
% 6.69/6.85      (![X0 : $i]:
% 6.69/6.85         ((v2_struct_0 @ sk_A)
% 6.69/6.85          | ~ (m1_pre_topc @ X0 @ sk_B)
% 6.69/6.85          | ~ (m1_pre_topc @ X0 @ sk_B)
% 6.69/6.85          | ((k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C)
% 6.69/6.85              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.69/6.85                 sk_C @ (u1_struct_0 @ X0)))
% 6.69/6.85          | (v2_struct_0 @ sk_B))),
% 6.69/6.85      inference('demod', [status(thm)], ['153', '154', '155', '156'])).
% 6.69/6.85  thf('158', plain,
% 6.69/6.85      (![X0 : $i]:
% 6.69/6.85         ((v2_struct_0 @ sk_B)
% 6.69/6.85          | ((k3_tmap_1 @ sk_B @ sk_A @ sk_B @ X0 @ sk_C)
% 6.69/6.85              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.69/6.85                 sk_C @ (u1_struct_0 @ X0)))
% 6.69/6.85          | ~ (m1_pre_topc @ X0 @ sk_B)
% 6.69/6.85          | (v2_struct_0 @ sk_A))),
% 6.69/6.85      inference('simplify', [status(thm)], ['157'])).
% 6.69/6.85  thf('159', plain,
% 6.69/6.85      ((~ (l1_pre_topc @ sk_B)
% 6.69/6.85        | (v2_struct_0 @ sk_A)
% 6.69/6.85        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C)
% 6.69/6.85            = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.69/6.85               sk_C @ (u1_struct_0 @ sk_B)))
% 6.69/6.85        | (v2_struct_0 @ sk_B))),
% 6.69/6.85      inference('sup-', [status(thm)], ['150', '158'])).
% 6.69/6.85  thf('160', plain, ((l1_pre_topc @ sk_B)),
% 6.69/6.85      inference('demod', [status(thm)], ['73', '74'])).
% 6.69/6.85  thf('161', plain,
% 6.69/6.85      (((k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B)
% 6.69/6.85         = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.85            (u1_struct_0 @ sk_B)))),
% 6.69/6.85      inference('clc', [status(thm)], ['97', '98'])).
% 6.69/6.85  thf('162', plain,
% 6.69/6.85      (((v2_struct_0 @ sk_A)
% 6.69/6.85        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C)
% 6.69/6.85            = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 6.69/6.85        | (v2_struct_0 @ sk_B))),
% 6.69/6.85      inference('demod', [status(thm)], ['159', '160', '161'])).
% 6.69/6.85  thf('163', plain, (~ (v2_struct_0 @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('164', plain,
% 6.69/6.85      (((v2_struct_0 @ sk_B)
% 6.69/6.85        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C)
% 6.69/6.85            = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B)))),
% 6.69/6.85      inference('clc', [status(thm)], ['162', '163'])).
% 6.69/6.85  thf('165', plain, (~ (v2_struct_0 @ sk_B)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('166', plain,
% 6.69/6.85      (((k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C)
% 6.69/6.85         = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))),
% 6.69/6.85      inference('clc', [status(thm)], ['164', '165'])).
% 6.69/6.85  thf('167', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))),
% 6.69/6.85      inference('demod', [status(thm)], ['149', '166'])).
% 6.69/6.85  thf('168', plain, ((l1_pre_topc @ sk_B)),
% 6.69/6.85      inference('demod', [status(thm)], ['73', '74'])).
% 6.69/6.85  thf('169', plain, ((v2_pre_topc @ sk_B)),
% 6.69/6.85      inference('demod', [status(thm)], ['83', '84', '85'])).
% 6.69/6.85  thf('170', plain,
% 6.69/6.85      (![X0 : $i, X1 : $i]:
% 6.69/6.85         ((v2_struct_0 @ sk_A)
% 6.69/6.85          | (v2_struct_0 @ X0)
% 6.69/6.85          | ~ (m1_pre_topc @ X0 @ sk_B)
% 6.69/6.85          | ~ (v1_funct_1 @ X1)
% 6.69/6.85          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 6.69/6.85          | ~ (m1_subset_1 @ X1 @ 
% 6.69/6.85               (k1_zfmisc_1 @ 
% 6.69/6.85                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 6.69/6.85          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 6.69/6.85             (k2_tmap_1 @ sk_B @ sk_A @ 
% 6.69/6.85              (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ X0) @ 
% 6.69/6.85             X1)
% 6.69/6.85          | (m1_subset_1 @ 
% 6.69/6.85             (sk_F @ X1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ X0 @ 
% 6.69/6.85              sk_B @ sk_A) @ 
% 6.69/6.85             (u1_struct_0 @ sk_B))
% 6.69/6.85          | (v2_struct_0 @ sk_B))),
% 6.69/6.85      inference('demod', [status(thm)],
% 6.69/6.85                ['105', '106', '107', '127', '167', '168', '169'])).
% 6.69/6.85  thf('171', plain,
% 6.69/6.85      ((m1_subset_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ 
% 6.69/6.85        (k1_zfmisc_1 @ 
% 6.69/6.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 6.69/6.85      inference('demod', [status(thm)], ['54', '102'])).
% 6.69/6.85  thf('172', plain,
% 6.69/6.85      (![X0 : $i]:
% 6.69/6.85         (~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.85             X0)
% 6.69/6.85          | ((sk_C) = (X0))
% 6.69/6.85          | ~ (m1_subset_1 @ X0 @ 
% 6.69/6.85               (k1_zfmisc_1 @ 
% 6.69/6.85                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 6.69/6.85          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 6.69/6.85          | ~ (v1_funct_1 @ X0))),
% 6.69/6.85      inference('demod', [status(thm)], ['11', '12', '13'])).
% 6.69/6.85  thf('173', plain,
% 6.69/6.85      ((~ (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 6.69/6.85        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ 
% 6.69/6.85             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 6.69/6.85        | ((sk_C) = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 6.69/6.85        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.85             (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B)))),
% 6.69/6.85      inference('sup-', [status(thm)], ['171', '172'])).
% 6.69/6.85  thf('174', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))),
% 6.69/6.85      inference('demod', [status(thm)], ['149', '166'])).
% 6.69/6.85  thf('175', plain,
% 6.69/6.85      ((v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ 
% 6.69/6.85        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 6.69/6.85      inference('demod', [status(thm)], ['125', '126'])).
% 6.69/6.85  thf('176', plain,
% 6.69/6.85      ((((sk_C) = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 6.69/6.85        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.85             (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B)))),
% 6.69/6.85      inference('demod', [status(thm)], ['173', '174', '175'])).
% 6.69/6.85  thf('177', plain,
% 6.69/6.85      (![X27 : $i]: ((m1_pre_topc @ X27 @ X27) | ~ (l1_pre_topc @ X27))),
% 6.69/6.85      inference('cnf', [status(esa)], [t2_tsep_1])).
% 6.69/6.85  thf('178', plain,
% 6.69/6.85      ((m1_subset_1 @ sk_C @ 
% 6.69/6.85        (k1_zfmisc_1 @ 
% 6.69/6.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf(t74_tmap_1, axiom,
% 6.69/6.85    (![A:$i]:
% 6.69/6.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.69/6.85       ( ![B:$i]:
% 6.69/6.85         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 6.69/6.85             ( l1_pre_topc @ B ) ) =>
% 6.69/6.85           ( ![C:$i]:
% 6.69/6.85             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 6.69/6.85               ( ![D:$i]:
% 6.69/6.85                 ( ( ( v1_funct_1 @ D ) & 
% 6.69/6.85                     ( v1_funct_2 @
% 6.69/6.85                       D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 6.69/6.85                     ( m1_subset_1 @
% 6.69/6.85                       D @ 
% 6.69/6.85                       ( k1_zfmisc_1 @
% 6.69/6.85                         ( k2_zfmisc_1 @
% 6.69/6.85                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 6.69/6.85                   ( r2_funct_2 @
% 6.69/6.85                     ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ D @ 
% 6.69/6.85                     ( k3_tmap_1 @ A @ B @ C @ C @ D ) ) ) ) ) ) ) ) ))).
% 6.69/6.85  thf('179', plain,
% 6.69/6.85      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 6.69/6.85         ((v2_struct_0 @ X39)
% 6.69/6.85          | ~ (v2_pre_topc @ X39)
% 6.69/6.85          | ~ (l1_pre_topc @ X39)
% 6.69/6.85          | ~ (v1_funct_1 @ X40)
% 6.69/6.85          | ~ (v1_funct_2 @ X40 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39))
% 6.69/6.85          | ~ (m1_subset_1 @ X40 @ 
% 6.69/6.85               (k1_zfmisc_1 @ 
% 6.69/6.85                (k2_zfmisc_1 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39))))
% 6.69/6.85          | (r2_funct_2 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X39) @ X40 @ 
% 6.69/6.85             (k3_tmap_1 @ X42 @ X39 @ X41 @ X41 @ X40))
% 6.69/6.85          | ~ (m1_pre_topc @ X41 @ X42)
% 6.69/6.85          | (v2_struct_0 @ X41)
% 6.69/6.85          | ~ (l1_pre_topc @ X42)
% 6.69/6.85          | ~ (v2_pre_topc @ X42)
% 6.69/6.85          | (v2_struct_0 @ X42))),
% 6.69/6.85      inference('cnf', [status(esa)], [t74_tmap_1])).
% 6.69/6.85  thf('180', plain,
% 6.69/6.85      (![X0 : $i]:
% 6.69/6.85         ((v2_struct_0 @ X0)
% 6.69/6.85          | ~ (v2_pre_topc @ X0)
% 6.69/6.85          | ~ (l1_pre_topc @ X0)
% 6.69/6.85          | (v2_struct_0 @ sk_B)
% 6.69/6.85          | ~ (m1_pre_topc @ sk_B @ X0)
% 6.69/6.85          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.85             (k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ sk_C))
% 6.69/6.85          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 6.69/6.85          | ~ (v1_funct_1 @ sk_C)
% 6.69/6.85          | ~ (l1_pre_topc @ sk_A)
% 6.69/6.85          | ~ (v2_pre_topc @ sk_A)
% 6.69/6.85          | (v2_struct_0 @ sk_A))),
% 6.69/6.85      inference('sup-', [status(thm)], ['178', '179'])).
% 6.69/6.85  thf('181', plain,
% 6.69/6.85      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('182', plain, ((v1_funct_1 @ sk_C)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('183', plain, ((l1_pre_topc @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('184', plain, ((v2_pre_topc @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('185', plain,
% 6.69/6.85      (![X0 : $i]:
% 6.69/6.85         ((v2_struct_0 @ X0)
% 6.69/6.85          | ~ (v2_pre_topc @ X0)
% 6.69/6.85          | ~ (l1_pre_topc @ X0)
% 6.69/6.85          | (v2_struct_0 @ sk_B)
% 6.69/6.85          | ~ (m1_pre_topc @ sk_B @ X0)
% 6.69/6.85          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.85             (k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ sk_C))
% 6.69/6.85          | (v2_struct_0 @ sk_A))),
% 6.69/6.85      inference('demod', [status(thm)], ['180', '181', '182', '183', '184'])).
% 6.69/6.85  thf('186', plain,
% 6.69/6.85      ((~ (l1_pre_topc @ sk_B)
% 6.69/6.85        | (v2_struct_0 @ sk_A)
% 6.69/6.85        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.85           (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C))
% 6.69/6.85        | (v2_struct_0 @ sk_B)
% 6.69/6.85        | ~ (l1_pre_topc @ sk_B)
% 6.69/6.85        | ~ (v2_pre_topc @ sk_B)
% 6.69/6.85        | (v2_struct_0 @ sk_B))),
% 6.69/6.85      inference('sup-', [status(thm)], ['177', '185'])).
% 6.69/6.85  thf('187', plain, ((l1_pre_topc @ sk_B)),
% 6.69/6.85      inference('demod', [status(thm)], ['73', '74'])).
% 6.69/6.85  thf('188', plain,
% 6.69/6.85      (((k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C)
% 6.69/6.85         = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))),
% 6.69/6.85      inference('clc', [status(thm)], ['164', '165'])).
% 6.69/6.85  thf('189', plain, ((l1_pre_topc @ sk_B)),
% 6.69/6.85      inference('demod', [status(thm)], ['73', '74'])).
% 6.69/6.85  thf('190', plain, ((v2_pre_topc @ sk_B)),
% 6.69/6.85      inference('demod', [status(thm)], ['83', '84', '85'])).
% 6.69/6.85  thf('191', plain,
% 6.69/6.85      (((v2_struct_0 @ sk_A)
% 6.69/6.85        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.85           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 6.69/6.85        | (v2_struct_0 @ sk_B)
% 6.69/6.85        | (v2_struct_0 @ sk_B))),
% 6.69/6.85      inference('demod', [status(thm)], ['186', '187', '188', '189', '190'])).
% 6.69/6.85  thf('192', plain,
% 6.69/6.85      (((v2_struct_0 @ sk_B)
% 6.69/6.85        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.85           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 6.69/6.85        | (v2_struct_0 @ sk_A))),
% 6.69/6.85      inference('simplify', [status(thm)], ['191'])).
% 6.69/6.85  thf('193', plain, (~ (v2_struct_0 @ sk_B)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('194', plain,
% 6.69/6.85      (((v2_struct_0 @ sk_A)
% 6.69/6.85        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.85           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B)))),
% 6.69/6.85      inference('clc', [status(thm)], ['192', '193'])).
% 6.69/6.85  thf('195', plain, (~ (v2_struct_0 @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('196', plain,
% 6.69/6.85      ((r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.85        (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))),
% 6.69/6.85      inference('clc', [status(thm)], ['194', '195'])).
% 6.69/6.85  thf('197', plain, (((sk_C) = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))),
% 6.69/6.85      inference('demod', [status(thm)], ['176', '196'])).
% 6.69/6.85  thf('198', plain, (((sk_C) = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))),
% 6.69/6.85      inference('demod', [status(thm)], ['176', '196'])).
% 6.69/6.85  thf('199', plain,
% 6.69/6.85      (![X0 : $i, X1 : $i]:
% 6.69/6.85         ((v2_struct_0 @ sk_A)
% 6.69/6.85          | (v2_struct_0 @ X0)
% 6.69/6.85          | ~ (m1_pre_topc @ X0 @ sk_B)
% 6.69/6.85          | ~ (v1_funct_1 @ X1)
% 6.69/6.85          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 6.69/6.85          | ~ (m1_subset_1 @ X1 @ 
% 6.69/6.85               (k1_zfmisc_1 @ 
% 6.69/6.85                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 6.69/6.85          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 6.69/6.85             (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 6.69/6.85          | (m1_subset_1 @ (sk_F @ X1 @ sk_C @ X0 @ sk_B @ sk_A) @ 
% 6.69/6.85             (u1_struct_0 @ sk_B))
% 6.69/6.85          | (v2_struct_0 @ sk_B))),
% 6.69/6.85      inference('demod', [status(thm)], ['170', '197', '198'])).
% 6.69/6.85  thf('200', plain,
% 6.69/6.85      (((v2_struct_0 @ sk_B)
% 6.69/6.85        | (m1_subset_1 @ 
% 6.69/6.85           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 6.69/6.85           (u1_struct_0 @ sk_B))
% 6.69/6.85        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.69/6.85           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.85        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 6.69/6.85             (u1_struct_0 @ sk_A))
% 6.69/6.85        | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.85        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 6.69/6.85        | (v2_struct_0 @ sk_B)
% 6.69/6.85        | (v2_struct_0 @ sk_A))),
% 6.69/6.85      inference('sup-', [status(thm)], ['36', '199'])).
% 6.69/6.85  thf('201', plain, (((sk_C) = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))),
% 6.69/6.85      inference('demod', [status(thm)], ['176', '196'])).
% 6.69/6.85  thf('202', plain,
% 6.69/6.85      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 6.69/6.85        (u1_struct_0 @ sk_A))),
% 6.69/6.85      inference('clc', [status(thm)], ['29', '30'])).
% 6.69/6.85  thf('203', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 6.69/6.85      inference('clc', [status(thm)], ['21', '22'])).
% 6.69/6.85  thf('204', plain,
% 6.69/6.85      (((v2_struct_0 @ sk_B)
% 6.69/6.85        | (m1_subset_1 @ 
% 6.69/6.85           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 6.69/6.85           (u1_struct_0 @ sk_B))
% 6.69/6.85        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.85           (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.85        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 6.69/6.85        | (v2_struct_0 @ sk_B)
% 6.69/6.85        | (v2_struct_0 @ sk_A))),
% 6.69/6.85      inference('demod', [status(thm)], ['200', '201', '202', '203'])).
% 6.69/6.85  thf('205', plain,
% 6.69/6.85      (((v2_struct_0 @ sk_A)
% 6.69/6.85        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 6.69/6.85        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.85           (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.85        | (m1_subset_1 @ 
% 6.69/6.85           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 6.69/6.85           (u1_struct_0 @ sk_B))
% 6.69/6.85        | (v2_struct_0 @ sk_B))),
% 6.69/6.85      inference('simplify', [status(thm)], ['204'])).
% 6.69/6.85  thf('206', plain,
% 6.69/6.85      ((~ (l1_pre_topc @ sk_B)
% 6.69/6.85        | (v2_struct_0 @ sk_B)
% 6.69/6.85        | (m1_subset_1 @ 
% 6.69/6.85           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 6.69/6.85           (u1_struct_0 @ sk_B))
% 6.69/6.85        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.85           (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.85        | (v2_struct_0 @ sk_A))),
% 6.69/6.85      inference('sup-', [status(thm)], ['35', '205'])).
% 6.69/6.85  thf('207', plain, ((l1_pre_topc @ sk_B)),
% 6.69/6.85      inference('demod', [status(thm)], ['73', '74'])).
% 6.69/6.85  thf('208', plain,
% 6.69/6.85      (((v2_struct_0 @ sk_B)
% 6.69/6.85        | (m1_subset_1 @ 
% 6.69/6.85           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 6.69/6.85           (u1_struct_0 @ sk_B))
% 6.69/6.85        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.85           (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.85        | (v2_struct_0 @ sk_A))),
% 6.69/6.85      inference('demod', [status(thm)], ['206', '207'])).
% 6.69/6.85  thf(t55_pre_topc, axiom,
% 6.69/6.85    (![A:$i]:
% 6.69/6.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 6.69/6.85       ( ![B:$i]:
% 6.69/6.85         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 6.69/6.85           ( ![C:$i]:
% 6.69/6.85             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 6.69/6.85               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 6.69/6.85  thf('209', plain,
% 6.69/6.85      (![X8 : $i, X9 : $i, X10 : $i]:
% 6.69/6.85         ((v2_struct_0 @ X8)
% 6.69/6.85          | ~ (m1_pre_topc @ X8 @ X9)
% 6.69/6.85          | (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 6.69/6.85          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X8))
% 6.69/6.85          | ~ (l1_pre_topc @ X9)
% 6.69/6.85          | (v2_struct_0 @ X9))),
% 6.69/6.85      inference('cnf', [status(esa)], [t55_pre_topc])).
% 6.69/6.85  thf('210', plain,
% 6.69/6.85      (![X0 : $i]:
% 6.69/6.85         ((v2_struct_0 @ sk_A)
% 6.69/6.85          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.85             (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.85          | (v2_struct_0 @ sk_B)
% 6.69/6.85          | (v2_struct_0 @ X0)
% 6.69/6.85          | ~ (l1_pre_topc @ X0)
% 6.69/6.85          | (m1_subset_1 @ 
% 6.69/6.85             (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 6.69/6.85             (u1_struct_0 @ X0))
% 6.69/6.85          | ~ (m1_pre_topc @ sk_B @ X0)
% 6.69/6.85          | (v2_struct_0 @ sk_B))),
% 6.69/6.85      inference('sup-', [status(thm)], ['208', '209'])).
% 6.69/6.85  thf('211', plain,
% 6.69/6.85      (![X0 : $i]:
% 6.69/6.85         (~ (m1_pre_topc @ sk_B @ X0)
% 6.69/6.85          | (m1_subset_1 @ 
% 6.69/6.85             (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 6.69/6.85             (u1_struct_0 @ X0))
% 6.69/6.85          | ~ (l1_pre_topc @ X0)
% 6.69/6.85          | (v2_struct_0 @ X0)
% 6.69/6.85          | (v2_struct_0 @ sk_B)
% 6.69/6.85          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.85             (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.85          | (v2_struct_0 @ sk_A))),
% 6.69/6.85      inference('simplify', [status(thm)], ['210'])).
% 6.69/6.85  thf('212', plain,
% 6.69/6.85      (((v2_struct_0 @ sk_A)
% 6.69/6.85        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.85           (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.85        | (v2_struct_0 @ sk_B)
% 6.69/6.85        | (v2_struct_0 @ sk_A)
% 6.69/6.85        | ~ (l1_pre_topc @ sk_A)
% 6.69/6.85        | (m1_subset_1 @ 
% 6.69/6.85           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 6.69/6.85           (u1_struct_0 @ sk_A)))),
% 6.69/6.85      inference('sup-', [status(thm)], ['34', '211'])).
% 6.69/6.85  thf('213', plain, ((l1_pre_topc @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('214', plain,
% 6.69/6.85      (((v2_struct_0 @ sk_A)
% 6.69/6.85        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.85           (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.85        | (v2_struct_0 @ sk_B)
% 6.69/6.85        | (v2_struct_0 @ sk_A)
% 6.69/6.85        | (m1_subset_1 @ 
% 6.69/6.85           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 6.69/6.85           (u1_struct_0 @ sk_A)))),
% 6.69/6.85      inference('demod', [status(thm)], ['212', '213'])).
% 6.69/6.85  thf('215', plain,
% 6.69/6.85      (((m1_subset_1 @ 
% 6.69/6.85         (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 6.69/6.85         (u1_struct_0 @ sk_A))
% 6.69/6.85        | (v2_struct_0 @ sk_B)
% 6.69/6.85        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.85           (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.85        | (v2_struct_0 @ sk_A))),
% 6.69/6.85      inference('simplify', [status(thm)], ['214'])).
% 6.69/6.85  thf('216', plain,
% 6.69/6.85      (![X27 : $i]: ((m1_pre_topc @ X27 @ X27) | ~ (l1_pre_topc @ X27))),
% 6.69/6.85      inference('cnf', [status(esa)], [t2_tsep_1])).
% 6.69/6.85  thf('217', plain,
% 6.69/6.85      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 6.69/6.85        (k1_zfmisc_1 @ 
% 6.69/6.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 6.69/6.85      inference('clc', [status(thm)], ['6', '7'])).
% 6.69/6.85  thf('218', plain,
% 6.69/6.85      ((m1_subset_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ 
% 6.69/6.85        (k1_zfmisc_1 @ 
% 6.69/6.85         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 6.69/6.85      inference('demod', [status(thm)], ['54', '102'])).
% 6.69/6.85  thf('219', plain,
% 6.69/6.85      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 6.69/6.85         ((v2_struct_0 @ X28)
% 6.69/6.85          | ~ (v2_pre_topc @ X28)
% 6.69/6.85          | ~ (l1_pre_topc @ X28)
% 6.69/6.85          | ~ (v1_funct_1 @ X29)
% 6.69/6.85          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X30))
% 6.69/6.85          | ~ (m1_subset_1 @ X29 @ 
% 6.69/6.85               (k1_zfmisc_1 @ 
% 6.69/6.85                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X30))))
% 6.69/6.85          | (r2_hidden @ (sk_F @ X31 @ X29 @ X32 @ X28 @ X30) @ 
% 6.69/6.85             (u1_struct_0 @ X32))
% 6.69/6.85          | (r2_funct_2 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X30) @ 
% 6.69/6.85             (k2_tmap_1 @ X28 @ X30 @ X29 @ X32) @ X31)
% 6.69/6.85          | ~ (m1_subset_1 @ X31 @ 
% 6.69/6.85               (k1_zfmisc_1 @ 
% 6.69/6.85                (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X30))))
% 6.69/6.85          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X30))
% 6.69/6.85          | ~ (v1_funct_1 @ X31)
% 6.69/6.85          | ~ (m1_pre_topc @ X32 @ X28)
% 6.69/6.85          | (v2_struct_0 @ X32)
% 6.69/6.85          | ~ (l1_pre_topc @ X30)
% 6.69/6.85          | ~ (v2_pre_topc @ X30)
% 6.69/6.85          | (v2_struct_0 @ X30))),
% 6.69/6.85      inference('cnf', [status(esa)], [t59_tmap_1])).
% 6.69/6.85  thf('220', plain,
% 6.69/6.85      (![X0 : $i, X1 : $i]:
% 6.69/6.85         ((v2_struct_0 @ sk_A)
% 6.69/6.85          | ~ (v2_pre_topc @ sk_A)
% 6.69/6.85          | ~ (l1_pre_topc @ sk_A)
% 6.69/6.85          | (v2_struct_0 @ X0)
% 6.69/6.85          | ~ (m1_pre_topc @ X0 @ sk_B)
% 6.69/6.85          | ~ (v1_funct_1 @ X1)
% 6.69/6.85          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 6.69/6.85          | ~ (m1_subset_1 @ X1 @ 
% 6.69/6.85               (k1_zfmisc_1 @ 
% 6.69/6.85                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 6.69/6.85          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 6.69/6.85             (k2_tmap_1 @ sk_B @ sk_A @ 
% 6.69/6.85              (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ X0) @ 
% 6.69/6.85             X1)
% 6.69/6.85          | (r2_hidden @ 
% 6.69/6.85             (sk_F @ X1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ X0 @ 
% 6.69/6.85              sk_B @ sk_A) @ 
% 6.69/6.85             (u1_struct_0 @ X0))
% 6.69/6.85          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ 
% 6.69/6.85               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 6.69/6.85          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 6.69/6.85          | ~ (l1_pre_topc @ sk_B)
% 6.69/6.85          | ~ (v2_pre_topc @ sk_B)
% 6.69/6.85          | (v2_struct_0 @ sk_B))),
% 6.69/6.85      inference('sup-', [status(thm)], ['218', '219'])).
% 6.69/6.85  thf('221', plain, ((v2_pre_topc @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('222', plain, ((l1_pre_topc @ sk_A)),
% 6.69/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.85  thf('223', plain,
% 6.69/6.85      ((v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ 
% 6.69/6.85        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 6.69/6.85      inference('demod', [status(thm)], ['125', '126'])).
% 6.69/6.85  thf('224', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))),
% 6.69/6.85      inference('demod', [status(thm)], ['149', '166'])).
% 6.69/6.85  thf('225', plain, ((l1_pre_topc @ sk_B)),
% 6.69/6.85      inference('demod', [status(thm)], ['73', '74'])).
% 6.69/6.85  thf('226', plain, ((v2_pre_topc @ sk_B)),
% 6.69/6.85      inference('demod', [status(thm)], ['83', '84', '85'])).
% 6.69/6.85  thf('227', plain,
% 6.69/6.85      (![X0 : $i, X1 : $i]:
% 6.69/6.85         ((v2_struct_0 @ sk_A)
% 6.69/6.85          | (v2_struct_0 @ X0)
% 6.69/6.85          | ~ (m1_pre_topc @ X0 @ sk_B)
% 6.69/6.85          | ~ (v1_funct_1 @ X1)
% 6.69/6.85          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 6.69/6.85          | ~ (m1_subset_1 @ X1 @ 
% 6.69/6.85               (k1_zfmisc_1 @ 
% 6.69/6.85                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 6.69/6.85          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 6.69/6.85             (k2_tmap_1 @ sk_B @ sk_A @ 
% 6.69/6.85              (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ X0) @ 
% 6.69/6.85             X1)
% 6.69/6.85          | (r2_hidden @ 
% 6.69/6.85             (sk_F @ X1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ X0 @ 
% 6.69/6.85              sk_B @ sk_A) @ 
% 6.69/6.85             (u1_struct_0 @ X0))
% 6.69/6.85          | (v2_struct_0 @ sk_B))),
% 6.69/6.85      inference('demod', [status(thm)],
% 6.69/6.85                ['220', '221', '222', '223', '224', '225', '226'])).
% 6.69/6.85  thf('228', plain, (((sk_C) = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))),
% 6.69/6.85      inference('demod', [status(thm)], ['176', '196'])).
% 6.69/6.85  thf('229', plain, (((sk_C) = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))),
% 6.69/6.85      inference('demod', [status(thm)], ['176', '196'])).
% 6.69/6.85  thf('230', plain,
% 6.69/6.85      (![X0 : $i, X1 : $i]:
% 6.69/6.85         ((v2_struct_0 @ sk_A)
% 6.69/6.85          | (v2_struct_0 @ X0)
% 6.69/6.85          | ~ (m1_pre_topc @ X0 @ sk_B)
% 6.69/6.85          | ~ (v1_funct_1 @ X1)
% 6.69/6.85          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 6.69/6.85          | ~ (m1_subset_1 @ X1 @ 
% 6.69/6.85               (k1_zfmisc_1 @ 
% 6.69/6.85                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 6.69/6.85          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 6.69/6.85             (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 6.69/6.85          | (r2_hidden @ (sk_F @ X1 @ sk_C @ X0 @ sk_B @ sk_A) @ 
% 6.69/6.85             (u1_struct_0 @ X0))
% 6.69/6.85          | (v2_struct_0 @ sk_B))),
% 6.69/6.85      inference('demod', [status(thm)], ['227', '228', '229'])).
% 6.69/6.85  thf('231', plain,
% 6.69/6.85      (((v2_struct_0 @ sk_B)
% 6.69/6.85        | (r2_hidden @ 
% 6.69/6.85           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 6.69/6.85           (u1_struct_0 @ sk_B))
% 6.69/6.85        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.69/6.85           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.85        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 6.69/6.85             (u1_struct_0 @ sk_A))
% 6.69/6.85        | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.85        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 6.69/6.85        | (v2_struct_0 @ sk_B)
% 6.69/6.85        | (v2_struct_0 @ sk_A))),
% 6.69/6.85      inference('sup-', [status(thm)], ['217', '230'])).
% 6.69/6.85  thf('232', plain, (((sk_C) = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))),
% 6.69/6.85      inference('demod', [status(thm)], ['176', '196'])).
% 6.69/6.85  thf('233', plain,
% 6.69/6.85      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 6.69/6.85        (u1_struct_0 @ sk_A))),
% 6.69/6.85      inference('clc', [status(thm)], ['29', '30'])).
% 6.69/6.85  thf('234', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 6.69/6.85      inference('clc', [status(thm)], ['21', '22'])).
% 6.69/6.85  thf('235', plain,
% 6.69/6.85      (((v2_struct_0 @ sk_B)
% 6.69/6.85        | (r2_hidden @ 
% 6.69/6.85           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 6.69/6.85           (u1_struct_0 @ sk_B))
% 6.69/6.85        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.85           (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.85        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 6.69/6.85        | (v2_struct_0 @ sk_B)
% 6.69/6.85        | (v2_struct_0 @ sk_A))),
% 6.69/6.85      inference('demod', [status(thm)], ['231', '232', '233', '234'])).
% 6.69/6.85  thf('236', plain,
% 6.69/6.85      (((v2_struct_0 @ sk_A)
% 6.69/6.85        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 6.69/6.85        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.85           (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.85        | (r2_hidden @ 
% 6.69/6.85           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 6.69/6.86           (u1_struct_0 @ sk_B))
% 6.69/6.86        | (v2_struct_0 @ sk_B))),
% 6.69/6.86      inference('simplify', [status(thm)], ['235'])).
% 6.69/6.86  thf('237', plain,
% 6.69/6.86      ((~ (l1_pre_topc @ sk_B)
% 6.69/6.86        | (v2_struct_0 @ sk_B)
% 6.69/6.86        | (r2_hidden @ 
% 6.69/6.86           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 6.69/6.86           (u1_struct_0 @ sk_B))
% 6.69/6.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86           (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.86        | (v2_struct_0 @ sk_A))),
% 6.69/6.86      inference('sup-', [status(thm)], ['216', '236'])).
% 6.69/6.86  thf('238', plain, ((l1_pre_topc @ sk_B)),
% 6.69/6.86      inference('demod', [status(thm)], ['73', '74'])).
% 6.69/6.86  thf('239', plain,
% 6.69/6.86      (((v2_struct_0 @ sk_B)
% 6.69/6.86        | (r2_hidden @ 
% 6.69/6.86           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 6.69/6.86           (u1_struct_0 @ sk_B))
% 6.69/6.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86           (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.86        | (v2_struct_0 @ sk_A))),
% 6.69/6.86      inference('demod', [status(thm)], ['237', '238'])).
% 6.69/6.86  thf('240', plain,
% 6.69/6.86      (![X49 : $i]:
% 6.69/6.86         (~ (r2_hidden @ X49 @ (u1_struct_0 @ sk_B))
% 6.69/6.86          | ((X49) = (k1_funct_1 @ sk_C @ X49))
% 6.69/6.86          | ~ (m1_subset_1 @ X49 @ (u1_struct_0 @ sk_A)))),
% 6.69/6.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.86  thf('241', plain,
% 6.69/6.86      (((v2_struct_0 @ sk_A)
% 6.69/6.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86           (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.86        | (v2_struct_0 @ sk_B)
% 6.69/6.86        | ~ (m1_subset_1 @ 
% 6.69/6.86             (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 6.69/6.86             (u1_struct_0 @ sk_A))
% 6.69/6.86        | ((sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)
% 6.69/6.86            = (k1_funct_1 @ sk_C @ 
% 6.69/6.86               (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))))),
% 6.69/6.86      inference('sup-', [status(thm)], ['239', '240'])).
% 6.69/6.86  thf('242', plain,
% 6.69/6.86      (((v2_struct_0 @ sk_A)
% 6.69/6.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86           (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.86        | (v2_struct_0 @ sk_B)
% 6.69/6.86        | ((sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)
% 6.69/6.86            = (k1_funct_1 @ sk_C @ 
% 6.69/6.86               (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)))
% 6.69/6.86        | (v2_struct_0 @ sk_B)
% 6.69/6.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86           (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.86        | (v2_struct_0 @ sk_A))),
% 6.69/6.86      inference('sup-', [status(thm)], ['215', '241'])).
% 6.69/6.86  thf('243', plain,
% 6.69/6.86      ((((sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)
% 6.69/6.86          = (k1_funct_1 @ sk_C @ 
% 6.69/6.86             (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)))
% 6.69/6.86        | (v2_struct_0 @ sk_B)
% 6.69/6.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86           (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.86        | (v2_struct_0 @ sk_A))),
% 6.69/6.86      inference('simplify', [status(thm)], ['242'])).
% 6.69/6.86  thf('244', plain,
% 6.69/6.86      (((m1_subset_1 @ 
% 6.69/6.86         (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 6.69/6.86         (u1_struct_0 @ sk_A))
% 6.69/6.86        | (v2_struct_0 @ sk_B)
% 6.69/6.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86           (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.86        | (v2_struct_0 @ sk_A))),
% 6.69/6.86      inference('simplify', [status(thm)], ['214'])).
% 6.69/6.86  thf('245', plain,
% 6.69/6.86      (((v2_struct_0 @ sk_B)
% 6.69/6.86        | (r2_hidden @ 
% 6.69/6.86           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 6.69/6.86           (u1_struct_0 @ sk_B))
% 6.69/6.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86           (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.86        | (v2_struct_0 @ sk_A))),
% 6.69/6.86      inference('demod', [status(thm)], ['237', '238'])).
% 6.69/6.86  thf(t95_tmap_1, axiom,
% 6.69/6.86    (![A:$i]:
% 6.69/6.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.69/6.86       ( ![B:$i]:
% 6.69/6.86         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 6.69/6.86           ( ![C:$i]:
% 6.69/6.86             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 6.69/6.86               ( ( r2_hidden @ C @ ( u1_struct_0 @ B ) ) =>
% 6.69/6.86                 ( ( k1_funct_1 @ ( k4_tmap_1 @ A @ B ) @ C ) = ( C ) ) ) ) ) ) ) ))).
% 6.69/6.86  thf('246', plain,
% 6.69/6.86      (![X46 : $i, X47 : $i, X48 : $i]:
% 6.69/6.86         ((v2_struct_0 @ X46)
% 6.69/6.86          | ~ (m1_pre_topc @ X46 @ X47)
% 6.69/6.86          | ~ (r2_hidden @ X48 @ (u1_struct_0 @ X46))
% 6.69/6.86          | ((k1_funct_1 @ (k4_tmap_1 @ X47 @ X46) @ X48) = (X48))
% 6.69/6.86          | ~ (m1_subset_1 @ X48 @ (u1_struct_0 @ X47))
% 6.69/6.86          | ~ (l1_pre_topc @ X47)
% 6.69/6.86          | ~ (v2_pre_topc @ X47)
% 6.69/6.86          | (v2_struct_0 @ X47))),
% 6.69/6.86      inference('cnf', [status(esa)], [t95_tmap_1])).
% 6.69/6.86  thf('247', plain,
% 6.69/6.86      (![X0 : $i]:
% 6.69/6.86         ((v2_struct_0 @ sk_A)
% 6.69/6.86          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86             (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.86          | (v2_struct_0 @ sk_B)
% 6.69/6.86          | (v2_struct_0 @ X0)
% 6.69/6.86          | ~ (v2_pre_topc @ X0)
% 6.69/6.86          | ~ (l1_pre_topc @ X0)
% 6.69/6.86          | ~ (m1_subset_1 @ 
% 6.69/6.86               (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 6.69/6.86               (u1_struct_0 @ X0))
% 6.69/6.86          | ((k1_funct_1 @ (k4_tmap_1 @ X0 @ sk_B) @ 
% 6.69/6.86              (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 6.69/6.86              = (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 6.69/6.86          | ~ (m1_pre_topc @ sk_B @ X0)
% 6.69/6.86          | (v2_struct_0 @ sk_B))),
% 6.69/6.86      inference('sup-', [status(thm)], ['245', '246'])).
% 6.69/6.86  thf('248', plain,
% 6.69/6.86      (![X0 : $i]:
% 6.69/6.86         (~ (m1_pre_topc @ sk_B @ X0)
% 6.69/6.86          | ((k1_funct_1 @ (k4_tmap_1 @ X0 @ sk_B) @ 
% 6.69/6.86              (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 6.69/6.86              = (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 6.69/6.86          | ~ (m1_subset_1 @ 
% 6.69/6.86               (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 6.69/6.86               (u1_struct_0 @ X0))
% 6.69/6.86          | ~ (l1_pre_topc @ X0)
% 6.69/6.86          | ~ (v2_pre_topc @ X0)
% 6.69/6.86          | (v2_struct_0 @ X0)
% 6.69/6.86          | (v2_struct_0 @ sk_B)
% 6.69/6.86          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86             (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.86          | (v2_struct_0 @ sk_A))),
% 6.69/6.86      inference('simplify', [status(thm)], ['247'])).
% 6.69/6.86  thf('249', plain,
% 6.69/6.86      (((v2_struct_0 @ sk_A)
% 6.69/6.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86           (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.86        | (v2_struct_0 @ sk_B)
% 6.69/6.86        | (v2_struct_0 @ sk_A)
% 6.69/6.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86           (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.86        | (v2_struct_0 @ sk_B)
% 6.69/6.86        | (v2_struct_0 @ sk_A)
% 6.69/6.86        | ~ (v2_pre_topc @ sk_A)
% 6.69/6.86        | ~ (l1_pre_topc @ sk_A)
% 6.69/6.86        | ((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 6.69/6.86            (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 6.69/6.86            = (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 6.69/6.86        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 6.69/6.86      inference('sup-', [status(thm)], ['244', '248'])).
% 6.69/6.86  thf('250', plain, ((v2_pre_topc @ sk_A)),
% 6.69/6.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.86  thf('251', plain, ((l1_pre_topc @ sk_A)),
% 6.69/6.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.86  thf('252', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 6.69/6.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.86  thf('253', plain,
% 6.69/6.86      (((v2_struct_0 @ sk_A)
% 6.69/6.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86           (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.86        | (v2_struct_0 @ sk_B)
% 6.69/6.86        | (v2_struct_0 @ sk_A)
% 6.69/6.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86           (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.86        | (v2_struct_0 @ sk_B)
% 6.69/6.86        | (v2_struct_0 @ sk_A)
% 6.69/6.86        | ((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 6.69/6.86            (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 6.69/6.86            = (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)))),
% 6.69/6.86      inference('demod', [status(thm)], ['249', '250', '251', '252'])).
% 6.69/6.86  thf('254', plain,
% 6.69/6.86      ((((k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 6.69/6.86          (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 6.69/6.86          = (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 6.69/6.86        | (v2_struct_0 @ sk_B)
% 6.69/6.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86           (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.86        | (v2_struct_0 @ sk_A))),
% 6.69/6.86      inference('simplify', [status(thm)], ['253'])).
% 6.69/6.86  thf('255', plain,
% 6.69/6.86      (![X27 : $i]: ((m1_pre_topc @ X27 @ X27) | ~ (l1_pre_topc @ X27))),
% 6.69/6.86      inference('cnf', [status(esa)], [t2_tsep_1])).
% 6.69/6.86  thf('256', plain,
% 6.69/6.86      (![X27 : $i]: ((m1_pre_topc @ X27 @ X27) | ~ (l1_pre_topc @ X27))),
% 6.69/6.86      inference('cnf', [status(esa)], [t2_tsep_1])).
% 6.69/6.86  thf('257', plain,
% 6.69/6.86      (((v2_struct_0 @ sk_B)
% 6.69/6.86        | (r2_hidden @ 
% 6.69/6.86           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 6.69/6.86           (u1_struct_0 @ sk_B))
% 6.69/6.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86           (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.86        | (v2_struct_0 @ sk_A))),
% 6.69/6.86      inference('demod', [status(thm)], ['237', '238'])).
% 6.69/6.86  thf('258', plain,
% 6.69/6.86      (((v2_struct_0 @ sk_B)
% 6.69/6.86        | (m1_subset_1 @ 
% 6.69/6.86           (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 6.69/6.86           (u1_struct_0 @ sk_B))
% 6.69/6.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86           (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.86        | (v2_struct_0 @ sk_A))),
% 6.69/6.86      inference('demod', [status(thm)], ['206', '207'])).
% 6.69/6.86  thf('259', plain,
% 6.69/6.86      ((m1_subset_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ 
% 6.69/6.86        (k1_zfmisc_1 @ 
% 6.69/6.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 6.69/6.86      inference('demod', [status(thm)], ['54', '102'])).
% 6.69/6.86  thf(t72_tmap_1, axiom,
% 6.69/6.86    (![A:$i]:
% 6.69/6.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.69/6.86       ( ![B:$i]:
% 6.69/6.86         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 6.69/6.86             ( l1_pre_topc @ B ) ) =>
% 6.69/6.86           ( ![C:$i]:
% 6.69/6.86             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 6.69/6.86               ( ![D:$i]:
% 6.69/6.86                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 6.69/6.86                   ( ![E:$i]:
% 6.69/6.86                     ( ( ( v1_funct_1 @ E ) & 
% 6.69/6.86                         ( v1_funct_2 @
% 6.69/6.86                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 6.69/6.86                         ( m1_subset_1 @
% 6.69/6.86                           E @ 
% 6.69/6.86                           ( k1_zfmisc_1 @
% 6.69/6.86                             ( k2_zfmisc_1 @
% 6.69/6.86                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 6.69/6.86                       ( ( m1_pre_topc @ C @ D ) =>
% 6.69/6.86                         ( ![F:$i]:
% 6.69/6.86                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 6.69/6.86                             ( ( r2_hidden @ F @ ( u1_struct_0 @ C ) ) =>
% 6.69/6.86                               ( ( k3_funct_2 @
% 6.69/6.86                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ 
% 6.69/6.86                                   E @ F ) =
% 6.69/6.86                                 ( k1_funct_1 @
% 6.69/6.86                                   ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 6.69/6.86  thf('260', plain,
% 6.69/6.86      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 6.69/6.86         ((v2_struct_0 @ X33)
% 6.69/6.86          | ~ (v2_pre_topc @ X33)
% 6.69/6.86          | ~ (l1_pre_topc @ X33)
% 6.69/6.86          | (v2_struct_0 @ X34)
% 6.69/6.86          | ~ (m1_pre_topc @ X34 @ X35)
% 6.69/6.86          | ~ (m1_pre_topc @ X36 @ X34)
% 6.69/6.86          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X34))
% 6.69/6.86          | ((k3_funct_2 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X33) @ X38 @ 
% 6.69/6.86              X37)
% 6.69/6.86              = (k1_funct_1 @ (k3_tmap_1 @ X35 @ X33 @ X34 @ X36 @ X38) @ X37))
% 6.69/6.86          | ~ (r2_hidden @ X37 @ (u1_struct_0 @ X36))
% 6.69/6.86          | ~ (m1_subset_1 @ X38 @ 
% 6.69/6.86               (k1_zfmisc_1 @ 
% 6.69/6.86                (k2_zfmisc_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X33))))
% 6.69/6.86          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X33))
% 6.69/6.86          | ~ (v1_funct_1 @ X38)
% 6.69/6.86          | ~ (m1_pre_topc @ X36 @ X35)
% 6.69/6.86          | (v2_struct_0 @ X36)
% 6.69/6.86          | ~ (l1_pre_topc @ X35)
% 6.69/6.86          | ~ (v2_pre_topc @ X35)
% 6.69/6.86          | (v2_struct_0 @ X35))),
% 6.69/6.86      inference('cnf', [status(esa)], [t72_tmap_1])).
% 6.69/6.86  thf('261', plain,
% 6.69/6.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.69/6.86         ((v2_struct_0 @ X0)
% 6.69/6.86          | ~ (v2_pre_topc @ X0)
% 6.69/6.86          | ~ (l1_pre_topc @ X0)
% 6.69/6.86          | (v2_struct_0 @ X1)
% 6.69/6.86          | ~ (m1_pre_topc @ X1 @ X0)
% 6.69/6.86          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))
% 6.69/6.86          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ 
% 6.69/6.86               (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 6.69/6.86          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X1))
% 6.69/6.86          | ((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.69/6.86              (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ X2)
% 6.69/6.86              = (k1_funct_1 @ 
% 6.69/6.86                 (k3_tmap_1 @ X0 @ sk_A @ sk_B @ X1 @ 
% 6.69/6.86                  (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B)) @ 
% 6.69/6.86                 X2))
% 6.69/6.86          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_B))
% 6.69/6.86          | ~ (m1_pre_topc @ X1 @ sk_B)
% 6.69/6.86          | ~ (m1_pre_topc @ sk_B @ X0)
% 6.69/6.86          | (v2_struct_0 @ sk_B)
% 6.69/6.86          | ~ (l1_pre_topc @ sk_A)
% 6.69/6.86          | ~ (v2_pre_topc @ sk_A)
% 6.69/6.86          | (v2_struct_0 @ sk_A))),
% 6.69/6.86      inference('sup-', [status(thm)], ['259', '260'])).
% 6.69/6.86  thf('262', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))),
% 6.69/6.86      inference('demod', [status(thm)], ['149', '166'])).
% 6.69/6.86  thf('263', plain,
% 6.69/6.86      ((v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ 
% 6.69/6.86        (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 6.69/6.86      inference('demod', [status(thm)], ['125', '126'])).
% 6.69/6.86  thf('264', plain, ((l1_pre_topc @ sk_A)),
% 6.69/6.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.86  thf('265', plain, ((v2_pre_topc @ sk_A)),
% 6.69/6.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.86  thf('266', plain,
% 6.69/6.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.69/6.86         ((v2_struct_0 @ X0)
% 6.69/6.86          | ~ (v2_pre_topc @ X0)
% 6.69/6.86          | ~ (l1_pre_topc @ X0)
% 6.69/6.86          | (v2_struct_0 @ X1)
% 6.69/6.86          | ~ (m1_pre_topc @ X1 @ X0)
% 6.69/6.86          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X1))
% 6.69/6.86          | ((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.69/6.86              (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ X2)
% 6.69/6.86              = (k1_funct_1 @ 
% 6.69/6.86                 (k3_tmap_1 @ X0 @ sk_A @ sk_B @ X1 @ 
% 6.69/6.86                  (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B)) @ 
% 6.69/6.86                 X2))
% 6.69/6.86          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_B))
% 6.69/6.86          | ~ (m1_pre_topc @ X1 @ sk_B)
% 6.69/6.86          | ~ (m1_pre_topc @ sk_B @ X0)
% 6.69/6.86          | (v2_struct_0 @ sk_B)
% 6.69/6.86          | (v2_struct_0 @ sk_A))),
% 6.69/6.86      inference('demod', [status(thm)], ['261', '262', '263', '264', '265'])).
% 6.69/6.86  thf('267', plain, (((sk_C) = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))),
% 6.69/6.86      inference('demod', [status(thm)], ['176', '196'])).
% 6.69/6.86  thf('268', plain, (((sk_C) = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))),
% 6.69/6.86      inference('demod', [status(thm)], ['176', '196'])).
% 6.69/6.86  thf('269', plain,
% 6.69/6.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.69/6.86         ((v2_struct_0 @ X0)
% 6.69/6.86          | ~ (v2_pre_topc @ X0)
% 6.69/6.86          | ~ (l1_pre_topc @ X0)
% 6.69/6.86          | (v2_struct_0 @ X1)
% 6.69/6.86          | ~ (m1_pre_topc @ X1 @ X0)
% 6.69/6.86          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X1))
% 6.69/6.86          | ((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.69/6.86              sk_C @ X2)
% 6.69/6.86              = (k1_funct_1 @ (k3_tmap_1 @ X0 @ sk_A @ sk_B @ X1 @ sk_C) @ X2))
% 6.69/6.86          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_B))
% 6.69/6.86          | ~ (m1_pre_topc @ X1 @ sk_B)
% 6.69/6.86          | ~ (m1_pre_topc @ sk_B @ X0)
% 6.69/6.86          | (v2_struct_0 @ sk_B)
% 6.69/6.86          | (v2_struct_0 @ sk_A))),
% 6.69/6.86      inference('demod', [status(thm)], ['266', '267', '268'])).
% 6.69/6.86  thf('270', plain,
% 6.69/6.86      (![X0 : $i, X1 : $i]:
% 6.69/6.86         ((v2_struct_0 @ sk_A)
% 6.69/6.86          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86             (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.86          | (v2_struct_0 @ sk_B)
% 6.69/6.86          | (v2_struct_0 @ sk_A)
% 6.69/6.86          | (v2_struct_0 @ sk_B)
% 6.69/6.86          | ~ (m1_pre_topc @ sk_B @ X0)
% 6.69/6.86          | ~ (m1_pre_topc @ X1 @ sk_B)
% 6.69/6.86          | ((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.69/6.86              sk_C @ 
% 6.69/6.86              (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 6.69/6.86              = (k1_funct_1 @ (k3_tmap_1 @ X0 @ sk_A @ sk_B @ X1 @ sk_C) @ 
% 6.69/6.86                 (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)))
% 6.69/6.86          | ~ (r2_hidden @ 
% 6.69/6.86               (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 6.69/6.86               (u1_struct_0 @ X1))
% 6.69/6.86          | ~ (m1_pre_topc @ X1 @ X0)
% 6.69/6.86          | (v2_struct_0 @ X1)
% 6.69/6.86          | ~ (l1_pre_topc @ X0)
% 6.69/6.86          | ~ (v2_pre_topc @ X0)
% 6.69/6.86          | (v2_struct_0 @ X0))),
% 6.69/6.86      inference('sup-', [status(thm)], ['258', '269'])).
% 6.69/6.86  thf('271', plain,
% 6.69/6.86      (![X0 : $i, X1 : $i]:
% 6.69/6.86         ((v2_struct_0 @ X0)
% 6.69/6.86          | ~ (v2_pre_topc @ X0)
% 6.69/6.86          | ~ (l1_pre_topc @ X0)
% 6.69/6.86          | (v2_struct_0 @ X1)
% 6.69/6.86          | ~ (m1_pre_topc @ X1 @ X0)
% 6.69/6.86          | ~ (r2_hidden @ 
% 6.69/6.86               (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A) @ 
% 6.69/6.86               (u1_struct_0 @ X1))
% 6.69/6.86          | ((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.69/6.86              sk_C @ 
% 6.69/6.86              (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 6.69/6.86              = (k1_funct_1 @ (k3_tmap_1 @ X0 @ sk_A @ sk_B @ X1 @ sk_C) @ 
% 6.69/6.86                 (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)))
% 6.69/6.86          | ~ (m1_pre_topc @ X1 @ sk_B)
% 6.69/6.86          | ~ (m1_pre_topc @ sk_B @ X0)
% 6.69/6.86          | (v2_struct_0 @ sk_B)
% 6.69/6.86          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86             (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.86          | (v2_struct_0 @ sk_A))),
% 6.69/6.86      inference('simplify', [status(thm)], ['270'])).
% 6.69/6.86  thf('272', plain,
% 6.69/6.86      (![X0 : $i]:
% 6.69/6.86         ((v2_struct_0 @ sk_A)
% 6.69/6.86          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86             (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.86          | (v2_struct_0 @ sk_B)
% 6.69/6.86          | (v2_struct_0 @ sk_A)
% 6.69/6.86          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86             (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.86          | (v2_struct_0 @ sk_B)
% 6.69/6.86          | ~ (m1_pre_topc @ sk_B @ X0)
% 6.69/6.86          | ~ (m1_pre_topc @ sk_B @ sk_B)
% 6.69/6.86          | ((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.69/6.86              sk_C @ 
% 6.69/6.86              (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 6.69/6.86              = (k1_funct_1 @ (k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 6.69/6.86                 (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)))
% 6.69/6.86          | ~ (m1_pre_topc @ sk_B @ X0)
% 6.69/6.86          | (v2_struct_0 @ sk_B)
% 6.69/6.86          | ~ (l1_pre_topc @ X0)
% 6.69/6.86          | ~ (v2_pre_topc @ X0)
% 6.69/6.86          | (v2_struct_0 @ X0))),
% 6.69/6.86      inference('sup-', [status(thm)], ['257', '271'])).
% 6.69/6.86  thf('273', plain,
% 6.69/6.86      (![X0 : $i]:
% 6.69/6.86         ((v2_struct_0 @ X0)
% 6.69/6.86          | ~ (v2_pre_topc @ X0)
% 6.69/6.86          | ~ (l1_pre_topc @ X0)
% 6.69/6.86          | ((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.69/6.86              sk_C @ 
% 6.69/6.86              (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 6.69/6.86              = (k1_funct_1 @ (k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 6.69/6.86                 (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)))
% 6.69/6.86          | ~ (m1_pre_topc @ sk_B @ sk_B)
% 6.69/6.86          | ~ (m1_pre_topc @ sk_B @ X0)
% 6.69/6.86          | (v2_struct_0 @ sk_B)
% 6.69/6.86          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86             (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.86          | (v2_struct_0 @ sk_A))),
% 6.69/6.86      inference('simplify', [status(thm)], ['272'])).
% 6.69/6.86  thf('274', plain,
% 6.69/6.86      (![X0 : $i]:
% 6.69/6.86         (~ (l1_pre_topc @ sk_B)
% 6.69/6.86          | (v2_struct_0 @ sk_A)
% 6.69/6.86          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86             (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.86          | (v2_struct_0 @ sk_B)
% 6.69/6.86          | ~ (m1_pre_topc @ sk_B @ X0)
% 6.69/6.86          | ((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.69/6.86              sk_C @ 
% 6.69/6.86              (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 6.69/6.86              = (k1_funct_1 @ (k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 6.69/6.86                 (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)))
% 6.69/6.86          | ~ (l1_pre_topc @ X0)
% 6.69/6.86          | ~ (v2_pre_topc @ X0)
% 6.69/6.86          | (v2_struct_0 @ X0))),
% 6.69/6.86      inference('sup-', [status(thm)], ['256', '273'])).
% 6.69/6.86  thf('275', plain, ((l1_pre_topc @ sk_B)),
% 6.69/6.86      inference('demod', [status(thm)], ['73', '74'])).
% 6.69/6.86  thf('276', plain,
% 6.69/6.86      (![X0 : $i]:
% 6.69/6.86         ((v2_struct_0 @ sk_A)
% 6.69/6.86          | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86             (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.86          | (v2_struct_0 @ sk_B)
% 6.69/6.86          | ~ (m1_pre_topc @ sk_B @ X0)
% 6.69/6.86          | ((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.69/6.86              sk_C @ 
% 6.69/6.86              (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 6.69/6.86              = (k1_funct_1 @ (k3_tmap_1 @ X0 @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 6.69/6.86                 (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)))
% 6.69/6.86          | ~ (l1_pre_topc @ X0)
% 6.69/6.86          | ~ (v2_pre_topc @ X0)
% 6.69/6.86          | (v2_struct_0 @ X0))),
% 6.69/6.86      inference('demod', [status(thm)], ['274', '275'])).
% 6.69/6.86  thf('277', plain,
% 6.69/6.86      ((~ (l1_pre_topc @ sk_B)
% 6.69/6.86        | (v2_struct_0 @ sk_B)
% 6.69/6.86        | ~ (v2_pre_topc @ sk_B)
% 6.69/6.86        | ~ (l1_pre_topc @ sk_B)
% 6.69/6.86        | ((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86            (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 6.69/6.86            = (k1_funct_1 @ (k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C) @ 
% 6.69/6.86               (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)))
% 6.69/6.86        | (v2_struct_0 @ sk_B)
% 6.69/6.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86           (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.86        | (v2_struct_0 @ sk_A))),
% 6.69/6.86      inference('sup-', [status(thm)], ['255', '276'])).
% 6.69/6.86  thf('278', plain, ((l1_pre_topc @ sk_B)),
% 6.69/6.86      inference('demod', [status(thm)], ['73', '74'])).
% 6.69/6.86  thf('279', plain, ((v2_pre_topc @ sk_B)),
% 6.69/6.86      inference('demod', [status(thm)], ['83', '84', '85'])).
% 6.69/6.86  thf('280', plain, ((l1_pre_topc @ sk_B)),
% 6.69/6.86      inference('demod', [status(thm)], ['73', '74'])).
% 6.69/6.86  thf('281', plain,
% 6.69/6.86      (((k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C)
% 6.69/6.86         = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))),
% 6.69/6.86      inference('clc', [status(thm)], ['164', '165'])).
% 6.69/6.86  thf('282', plain, (((sk_C) = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))),
% 6.69/6.86      inference('demod', [status(thm)], ['176', '196'])).
% 6.69/6.86  thf('283', plain,
% 6.69/6.86      (((k3_tmap_1 @ sk_B @ sk_A @ sk_B @ sk_B @ sk_C) = (sk_C))),
% 6.69/6.86      inference('demod', [status(thm)], ['281', '282'])).
% 6.69/6.86  thf('284', plain,
% 6.69/6.86      (((v2_struct_0 @ sk_B)
% 6.69/6.86        | ((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86            (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 6.69/6.86            = (k1_funct_1 @ sk_C @ 
% 6.69/6.86               (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)))
% 6.69/6.86        | (v2_struct_0 @ sk_B)
% 6.69/6.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86           (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.86        | (v2_struct_0 @ sk_A))),
% 6.69/6.86      inference('demod', [status(thm)], ['277', '278', '279', '280', '283'])).
% 6.69/6.86  thf('285', plain,
% 6.69/6.86      (((v2_struct_0 @ sk_A)
% 6.69/6.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86           (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.86        | ((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86            (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 6.69/6.86            = (k1_funct_1 @ sk_C @ 
% 6.69/6.86               (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)))
% 6.69/6.86        | (v2_struct_0 @ sk_B))),
% 6.69/6.86      inference('simplify', [status(thm)], ['284'])).
% 6.69/6.86  thf('286', plain,
% 6.69/6.86      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 6.69/6.86         ((v2_struct_0 @ X28)
% 6.69/6.86          | ~ (v2_pre_topc @ X28)
% 6.69/6.86          | ~ (l1_pre_topc @ X28)
% 6.69/6.86          | ~ (v1_funct_1 @ X29)
% 6.69/6.86          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X30))
% 6.69/6.86          | ~ (m1_subset_1 @ X29 @ 
% 6.69/6.86               (k1_zfmisc_1 @ 
% 6.69/6.86                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X30))))
% 6.69/6.86          | ((k3_funct_2 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X30) @ X29 @ 
% 6.69/6.86              (sk_F @ X31 @ X29 @ X32 @ X28 @ X30))
% 6.69/6.86              != (k1_funct_1 @ X31 @ (sk_F @ X31 @ X29 @ X32 @ X28 @ X30)))
% 6.69/6.86          | (r2_funct_2 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X30) @ 
% 6.69/6.86             (k2_tmap_1 @ X28 @ X30 @ X29 @ X32) @ X31)
% 6.69/6.86          | ~ (m1_subset_1 @ X31 @ 
% 6.69/6.86               (k1_zfmisc_1 @ 
% 6.69/6.86                (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X30))))
% 6.69/6.86          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X30))
% 6.69/6.86          | ~ (v1_funct_1 @ X31)
% 6.69/6.86          | ~ (m1_pre_topc @ X32 @ X28)
% 6.69/6.86          | (v2_struct_0 @ X32)
% 6.69/6.86          | ~ (l1_pre_topc @ X30)
% 6.69/6.86          | ~ (v2_pre_topc @ X30)
% 6.69/6.86          | (v2_struct_0 @ X30))),
% 6.69/6.86      inference('cnf', [status(esa)], [t59_tmap_1])).
% 6.69/6.86  thf('287', plain,
% 6.69/6.86      ((((k1_funct_1 @ sk_C @ 
% 6.69/6.86          (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 6.69/6.86          != (k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 6.69/6.86              (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)))
% 6.69/6.86        | (v2_struct_0 @ sk_B)
% 6.69/6.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86           (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.86        | (v2_struct_0 @ sk_A)
% 6.69/6.86        | (v2_struct_0 @ sk_A)
% 6.69/6.86        | ~ (v2_pre_topc @ sk_A)
% 6.69/6.86        | ~ (l1_pre_topc @ sk_A)
% 6.69/6.86        | (v2_struct_0 @ sk_B)
% 6.69/6.86        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 6.69/6.86        | ~ (v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.86        | ~ (v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 6.69/6.86             (u1_struct_0 @ sk_A))
% 6.69/6.86        | ~ (m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 6.69/6.86             (k1_zfmisc_1 @ 
% 6.69/6.86              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 6.69/6.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.69/6.86           (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B) @ (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.86        | ~ (m1_subset_1 @ sk_C @ 
% 6.69/6.86             (k1_zfmisc_1 @ 
% 6.69/6.86              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 6.69/6.86        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 6.69/6.86        | ~ (v1_funct_1 @ sk_C)
% 6.69/6.86        | ~ (l1_pre_topc @ sk_B)
% 6.69/6.86        | ~ (v2_pre_topc @ sk_B)
% 6.69/6.86        | (v2_struct_0 @ sk_B))),
% 6.69/6.86      inference('sup-', [status(thm)], ['285', '286'])).
% 6.69/6.86  thf('288', plain, ((v2_pre_topc @ sk_A)),
% 6.69/6.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.86  thf('289', plain, ((l1_pre_topc @ sk_A)),
% 6.69/6.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.86  thf('290', plain, ((v1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B))),
% 6.69/6.86      inference('clc', [status(thm)], ['21', '22'])).
% 6.69/6.86  thf('291', plain,
% 6.69/6.86      ((v1_funct_2 @ (k4_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B) @ 
% 6.69/6.86        (u1_struct_0 @ sk_A))),
% 6.69/6.86      inference('clc', [status(thm)], ['29', '30'])).
% 6.69/6.86  thf('292', plain,
% 6.69/6.86      ((m1_subset_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 6.69/6.86        (k1_zfmisc_1 @ 
% 6.69/6.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 6.69/6.86      inference('clc', [status(thm)], ['6', '7'])).
% 6.69/6.86  thf('293', plain, (((sk_C) = (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_B))),
% 6.69/6.86      inference('demod', [status(thm)], ['176', '196'])).
% 6.69/6.86  thf('294', plain,
% 6.69/6.86      ((m1_subset_1 @ sk_C @ 
% 6.69/6.86        (k1_zfmisc_1 @ 
% 6.69/6.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 6.69/6.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.86  thf('295', plain,
% 6.69/6.86      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 6.69/6.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.86  thf('296', plain, ((v1_funct_1 @ sk_C)),
% 6.69/6.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.86  thf('297', plain, ((l1_pre_topc @ sk_B)),
% 6.69/6.86      inference('demod', [status(thm)], ['73', '74'])).
% 6.69/6.86  thf('298', plain, ((v2_pre_topc @ sk_B)),
% 6.69/6.86      inference('demod', [status(thm)], ['83', '84', '85'])).
% 6.69/6.86  thf('299', plain,
% 6.69/6.86      ((((k1_funct_1 @ sk_C @ 
% 6.69/6.86          (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 6.69/6.86          != (k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 6.69/6.86              (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)))
% 6.69/6.86        | (v2_struct_0 @ sk_B)
% 6.69/6.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86           (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.86        | (v2_struct_0 @ sk_A)
% 6.69/6.86        | (v2_struct_0 @ sk_A)
% 6.69/6.86        | (v2_struct_0 @ sk_B)
% 6.69/6.86        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 6.69/6.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86           (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.86        | (v2_struct_0 @ sk_B))),
% 6.69/6.86      inference('demod', [status(thm)],
% 6.69/6.86                ['287', '288', '289', '290', '291', '292', '293', '294', 
% 6.69/6.86                 '295', '296', '297', '298'])).
% 6.69/6.86  thf('300', plain,
% 6.69/6.86      ((~ (m1_pre_topc @ sk_B @ sk_B)
% 6.69/6.86        | (v2_struct_0 @ sk_A)
% 6.69/6.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86           (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.86        | (v2_struct_0 @ sk_B)
% 6.69/6.86        | ((k1_funct_1 @ sk_C @ 
% 6.69/6.86            (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 6.69/6.86            != (k1_funct_1 @ (k4_tmap_1 @ sk_A @ sk_B) @ 
% 6.69/6.86                (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))))),
% 6.69/6.86      inference('simplify', [status(thm)], ['299'])).
% 6.69/6.86  thf('301', plain,
% 6.69/6.86      ((((k1_funct_1 @ sk_C @ 
% 6.69/6.86          (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 6.69/6.86          != (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 6.69/6.86        | (v2_struct_0 @ sk_A)
% 6.69/6.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86           (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.86        | (v2_struct_0 @ sk_B)
% 6.69/6.86        | (v2_struct_0 @ sk_B)
% 6.69/6.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86           (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.86        | (v2_struct_0 @ sk_A)
% 6.69/6.86        | ~ (m1_pre_topc @ sk_B @ sk_B))),
% 6.69/6.86      inference('sup-', [status(thm)], ['254', '300'])).
% 6.69/6.86  thf('302', plain,
% 6.69/6.86      ((~ (m1_pre_topc @ sk_B @ sk_B)
% 6.69/6.86        | (v2_struct_0 @ sk_B)
% 6.69/6.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86           (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.86        | (v2_struct_0 @ sk_A)
% 6.69/6.86        | ((k1_funct_1 @ sk_C @ 
% 6.69/6.86            (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 6.69/6.86            != (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)))),
% 6.69/6.86      inference('simplify', [status(thm)], ['301'])).
% 6.69/6.86  thf('303', plain,
% 6.69/6.86      ((((sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A)
% 6.69/6.86          != (sk_F @ (k4_tmap_1 @ sk_A @ sk_B) @ sk_C @ sk_B @ sk_B @ sk_A))
% 6.69/6.86        | (v2_struct_0 @ sk_A)
% 6.69/6.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86           (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.86        | (v2_struct_0 @ sk_B)
% 6.69/6.86        | (v2_struct_0 @ sk_A)
% 6.69/6.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86           (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.86        | (v2_struct_0 @ sk_B)
% 6.69/6.86        | ~ (m1_pre_topc @ sk_B @ sk_B))),
% 6.69/6.86      inference('sup-', [status(thm)], ['243', '302'])).
% 6.69/6.86  thf('304', plain,
% 6.69/6.86      ((~ (m1_pre_topc @ sk_B @ sk_B)
% 6.69/6.86        | (v2_struct_0 @ sk_B)
% 6.69/6.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86           (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.86        | (v2_struct_0 @ sk_A))),
% 6.69/6.86      inference('simplify', [status(thm)], ['303'])).
% 6.69/6.86  thf('305', plain,
% 6.69/6.86      ((~ (l1_pre_topc @ sk_B)
% 6.69/6.86        | (v2_struct_0 @ sk_A)
% 6.69/6.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86           (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.86        | (v2_struct_0 @ sk_B))),
% 6.69/6.86      inference('sup-', [status(thm)], ['33', '304'])).
% 6.69/6.86  thf('306', plain, ((l1_pre_topc @ sk_B)),
% 6.69/6.86      inference('demod', [status(thm)], ['73', '74'])).
% 6.69/6.86  thf('307', plain,
% 6.69/6.86      (((v2_struct_0 @ sk_A)
% 6.69/6.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86           (k4_tmap_1 @ sk_A @ sk_B))
% 6.69/6.86        | (v2_struct_0 @ sk_B))),
% 6.69/6.86      inference('demod', [status(thm)], ['305', '306'])).
% 6.69/6.86  thf('308', plain, (~ (v2_struct_0 @ sk_A)),
% 6.69/6.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.86  thf('309', plain,
% 6.69/6.86      (((v2_struct_0 @ sk_B)
% 6.69/6.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86           (k4_tmap_1 @ sk_A @ sk_B)))),
% 6.69/6.86      inference('clc', [status(thm)], ['307', '308'])).
% 6.69/6.86  thf('310', plain, (~ (v2_struct_0 @ sk_B)),
% 6.69/6.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.86  thf('311', plain,
% 6.69/6.86      ((r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86        (k4_tmap_1 @ sk_A @ sk_B))),
% 6.69/6.86      inference('clc', [status(thm)], ['309', '310'])).
% 6.69/6.86  thf('312', plain, (((sk_C) = (k4_tmap_1 @ sk_A @ sk_B))),
% 6.69/6.86      inference('demod', [status(thm)], ['32', '311'])).
% 6.69/6.86  thf('313', plain,
% 6.69/6.86      ((m1_subset_1 @ sk_C @ 
% 6.69/6.86        (k1_zfmisc_1 @ 
% 6.69/6.86         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 6.69/6.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.86  thf('314', plain,
% 6.69/6.86      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.69/6.86         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 6.69/6.86          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 6.69/6.86          | ~ (v1_funct_1 @ X0)
% 6.69/6.86          | ~ (v1_funct_1 @ X3)
% 6.69/6.86          | ~ (v1_funct_2 @ X3 @ X1 @ X2)
% 6.69/6.86          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 6.69/6.86          | (r2_funct_2 @ X1 @ X2 @ X0 @ X3)
% 6.69/6.86          | ((X0) != (X3)))),
% 6.69/6.86      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 6.69/6.86  thf('315', plain,
% 6.69/6.86      (![X1 : $i, X2 : $i, X3 : $i]:
% 6.69/6.86         ((r2_funct_2 @ X1 @ X2 @ X3 @ X3)
% 6.69/6.86          | ~ (v1_funct_1 @ X3)
% 6.69/6.86          | ~ (v1_funct_2 @ X3 @ X1 @ X2)
% 6.69/6.86          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2))))),
% 6.69/6.86      inference('simplify', [status(thm)], ['314'])).
% 6.69/6.86  thf('316', plain,
% 6.69/6.86      ((~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 6.69/6.86        | ~ (v1_funct_1 @ sk_C)
% 6.69/6.86        | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 6.69/6.86           sk_C))),
% 6.69/6.86      inference('sup-', [status(thm)], ['313', '315'])).
% 6.69/6.86  thf('317', plain,
% 6.69/6.86      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 6.69/6.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.86  thf('318', plain, ((v1_funct_1 @ sk_C)),
% 6.69/6.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.69/6.86  thf('319', plain,
% 6.69/6.86      ((r2_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_C @ sk_C)),
% 6.69/6.86      inference('demod', [status(thm)], ['316', '317', '318'])).
% 6.69/6.86  thf('320', plain, ($false),
% 6.69/6.86      inference('demod', [status(thm)], ['0', '312', '319'])).
% 6.69/6.86  
% 6.69/6.86  % SZS output end Refutation
% 6.69/6.86  
% 6.69/6.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
