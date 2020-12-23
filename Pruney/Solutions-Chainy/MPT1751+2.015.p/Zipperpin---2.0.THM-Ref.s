%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wrXWkBiBkq

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:48 EST 2020

% Result     : Theorem 8.66s
% Output     : Refutation 8.66s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 241 expanded)
%              Number of leaves         :   41 (  92 expanded)
%              Depth                    :   18
%              Number of atoms          : 1058 (4388 expanded)
%              Number of equality atoms :   33 (  81 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) )
        = ( k9_relat_1 @ X15 @ X16 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t61_tmap_1,conjecture,(
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
                      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ( ( r1_tarski @ E @ ( u1_struct_0 @ C ) )
                       => ( ( k7_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ D @ E )
                          = ( k7_relset_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) )).

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
                  & ( m1_pre_topc @ C @ B ) )
               => ! [D: $i] :
                    ( ( ( v1_funct_1 @ D )
                      & ( v1_funct_2 @ D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                       => ( ( r1_tarski @ E @ ( u1_struct_0 @ C ) )
                         => ( ( k7_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ D @ E )
                            = ( k7_relset_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_tmap_1])).

thf('1',plain,(
    r1_tarski @ sk_E @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t103_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k7_relat_1 @ C @ A ) ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X14 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X14 @ X13 ) @ X12 )
        = ( k7_relat_1 @ X14 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t103_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ ( u1_struct_0 @ sk_C ) ) @ sk_E )
        = ( k7_relat_1 @ X0 @ sk_E ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) )
        = ( k9_relat_1 @ X15 @ X16 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X0 @ sk_E ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X0 @ ( u1_struct_0 @ sk_C ) ) @ sk_E ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ ( u1_struct_0 @ sk_C ) ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('6',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X19 @ X20 ) @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X0 @ sk_E ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X0 @ ( u1_struct_0 @ sk_C ) ) @ sk_E ) ) ) ),
    inference(clc,[status(thm)],['5','11'])).

thf('13',plain,(
    ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_E )
 != ( k7_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('15',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k7_relset_1 @ X25 @ X26 @ X24 @ X27 )
        = ( k9_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ( k9_relat_1 @ sk_D @ sk_E )
 != ( k7_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) @ sk_E ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('20',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( v2_struct_0 @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( m1_pre_topc @ X36 @ X37 )
      | ( ( k2_tmap_1 @ X37 @ X35 @ X38 @ X36 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X35 ) @ X38 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X35 ) ) ) )
      | ~ ( v1_funct_2 @ X38 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X35 ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('27',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ( ( k2_partfun1 @ X32 @ X33 @ X31 @ X34 )
        = ( k7_relat_1 @ X31 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','25','30','31','32'])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['18','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
    = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('41',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X19 @ X20 ) @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('49',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('50',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['45','50'])).

thf('52',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('53',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('54',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v5_relat_1 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('56',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v5_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('59',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','62'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('64',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) ) @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('65',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X28 ) @ X29 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X28 ) @ X30 )
      | ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('69',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['48','49'])).

thf('70',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k7_relset_1 @ X25 @ X26 @ X24 @ X27 )
        = ( k9_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relset_1 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( k7_relat_1 @ sk_D @ X0 ) @ X1 )
      = ( k9_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ( k9_relat_1 @ sk_D @ sk_E )
 != ( k9_relat_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E ) ),
    inference(demod,[status(thm)],['17','38','72'])).

thf('74',plain,
    ( ( ( k9_relat_1 @ sk_D @ sk_E )
     != ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ sk_E ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['12','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['48','49'])).

thf('76',plain,(
    ( k9_relat_1 @ sk_D @ sk_E )
 != ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ sk_E ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( k9_relat_1 @ sk_D @ sk_E )
     != ( k9_relat_1 @ sk_D @ sk_E ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['0','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['48','49'])).

thf('79',plain,(
    ( k9_relat_1 @ sk_D @ sk_E )
 != ( k9_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    $false ),
    inference(simplify,[status(thm)],['79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wrXWkBiBkq
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:49:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 8.66/8.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 8.66/8.89  % Solved by: fo/fo7.sh
% 8.66/8.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.66/8.89  % done 3717 iterations in 8.431s
% 8.66/8.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 8.66/8.89  % SZS output start Refutation
% 8.66/8.89  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 8.66/8.89  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 8.66/8.89  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 8.66/8.89  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 8.66/8.89  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 8.66/8.89  thf(sk_C_type, type, sk_C: $i).
% 8.66/8.89  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 8.66/8.89  thf(sk_B_type, type, sk_B: $i).
% 8.66/8.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 8.66/8.89  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 8.66/8.89  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 8.66/8.89  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 8.66/8.89  thf(sk_E_type, type, sk_E: $i).
% 8.66/8.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.66/8.89  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 8.66/8.89  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 8.66/8.89  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 8.66/8.89  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 8.66/8.89  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 8.66/8.89  thf(sk_D_type, type, sk_D: $i).
% 8.66/8.89  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 8.66/8.89  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 8.66/8.89  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 8.66/8.89  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 8.66/8.89  thf(sk_A_type, type, sk_A: $i).
% 8.66/8.89  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 8.66/8.89  thf(t148_relat_1, axiom,
% 8.66/8.89    (![A:$i,B:$i]:
% 8.66/8.89     ( ( v1_relat_1 @ B ) =>
% 8.66/8.89       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 8.66/8.89  thf('0', plain,
% 8.66/8.89      (![X15 : $i, X16 : $i]:
% 8.66/8.89         (((k2_relat_1 @ (k7_relat_1 @ X15 @ X16)) = (k9_relat_1 @ X15 @ X16))
% 8.66/8.89          | ~ (v1_relat_1 @ X15))),
% 8.66/8.89      inference('cnf', [status(esa)], [t148_relat_1])).
% 8.66/8.89  thf(t61_tmap_1, conjecture,
% 8.66/8.89    (![A:$i]:
% 8.66/8.89     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 8.66/8.89       ( ![B:$i]:
% 8.66/8.89         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 8.66/8.89             ( l1_pre_topc @ B ) ) =>
% 8.66/8.89           ( ![C:$i]:
% 8.66/8.89             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 8.66/8.89               ( ![D:$i]:
% 8.66/8.89                 ( ( ( v1_funct_1 @ D ) & 
% 8.66/8.89                     ( v1_funct_2 @
% 8.66/8.89                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 8.66/8.89                     ( m1_subset_1 @
% 8.66/8.89                       D @ 
% 8.66/8.89                       ( k1_zfmisc_1 @
% 8.66/8.89                         ( k2_zfmisc_1 @
% 8.66/8.89                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 8.66/8.89                   ( ![E:$i]:
% 8.66/8.89                     ( ( m1_subset_1 @
% 8.66/8.89                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 8.66/8.89                       ( ( r1_tarski @ E @ ( u1_struct_0 @ C ) ) =>
% 8.66/8.89                         ( ( k7_relset_1 @
% 8.66/8.89                             ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ D @ E ) =
% 8.66/8.89                           ( k7_relset_1 @
% 8.66/8.89                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 8.66/8.89                             ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 8.66/8.89  thf(zf_stmt_0, negated_conjecture,
% 8.66/8.89    (~( ![A:$i]:
% 8.66/8.89        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 8.66/8.89            ( l1_pre_topc @ A ) ) =>
% 8.66/8.89          ( ![B:$i]:
% 8.66/8.89            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 8.66/8.89                ( l1_pre_topc @ B ) ) =>
% 8.66/8.89              ( ![C:$i]:
% 8.66/8.89                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 8.66/8.89                  ( ![D:$i]:
% 8.66/8.89                    ( ( ( v1_funct_1 @ D ) & 
% 8.66/8.89                        ( v1_funct_2 @
% 8.66/8.89                          D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 8.66/8.89                        ( m1_subset_1 @
% 8.66/8.89                          D @ 
% 8.66/8.89                          ( k1_zfmisc_1 @
% 8.66/8.89                            ( k2_zfmisc_1 @
% 8.66/8.89                              ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 8.66/8.89                      ( ![E:$i]:
% 8.66/8.89                        ( ( m1_subset_1 @
% 8.66/8.89                            E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 8.66/8.89                          ( ( r1_tarski @ E @ ( u1_struct_0 @ C ) ) =>
% 8.66/8.89                            ( ( k7_relset_1 @
% 8.66/8.89                                ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 8.66/8.89                                D @ E ) =
% 8.66/8.89                              ( k7_relset_1 @
% 8.66/8.89                                ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 8.66/8.89                                ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ) ) )),
% 8.66/8.89    inference('cnf.neg', [status(esa)], [t61_tmap_1])).
% 8.66/8.89  thf('1', plain, ((r1_tarski @ sk_E @ (u1_struct_0 @ sk_C))),
% 8.66/8.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.66/8.89  thf(t103_relat_1, axiom,
% 8.66/8.89    (![A:$i,B:$i,C:$i]:
% 8.66/8.89     ( ( v1_relat_1 @ C ) =>
% 8.66/8.89       ( ( r1_tarski @ A @ B ) =>
% 8.66/8.89         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k7_relat_1 @ C @ A ) ) ) ))).
% 8.66/8.89  thf('2', plain,
% 8.66/8.89      (![X12 : $i, X13 : $i, X14 : $i]:
% 8.66/8.89         (~ (r1_tarski @ X12 @ X13)
% 8.66/8.89          | ~ (v1_relat_1 @ X14)
% 8.66/8.89          | ((k7_relat_1 @ (k7_relat_1 @ X14 @ X13) @ X12)
% 8.66/8.89              = (k7_relat_1 @ X14 @ X12)))),
% 8.66/8.89      inference('cnf', [status(esa)], [t103_relat_1])).
% 8.66/8.89  thf('3', plain,
% 8.66/8.89      (![X0 : $i]:
% 8.66/8.89         (((k7_relat_1 @ (k7_relat_1 @ X0 @ (u1_struct_0 @ sk_C)) @ sk_E)
% 8.66/8.89            = (k7_relat_1 @ X0 @ sk_E))
% 8.66/8.89          | ~ (v1_relat_1 @ X0))),
% 8.66/8.89      inference('sup-', [status(thm)], ['1', '2'])).
% 8.66/8.89  thf('4', plain,
% 8.66/8.89      (![X15 : $i, X16 : $i]:
% 8.66/8.89         (((k2_relat_1 @ (k7_relat_1 @ X15 @ X16)) = (k9_relat_1 @ X15 @ X16))
% 8.66/8.89          | ~ (v1_relat_1 @ X15))),
% 8.66/8.89      inference('cnf', [status(esa)], [t148_relat_1])).
% 8.66/8.89  thf('5', plain,
% 8.66/8.89      (![X0 : $i]:
% 8.66/8.89         (((k2_relat_1 @ (k7_relat_1 @ X0 @ sk_E))
% 8.66/8.89            = (k9_relat_1 @ (k7_relat_1 @ X0 @ (u1_struct_0 @ sk_C)) @ sk_E))
% 8.66/8.89          | ~ (v1_relat_1 @ X0)
% 8.66/8.89          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ (u1_struct_0 @ sk_C))))),
% 8.66/8.89      inference('sup+', [status(thm)], ['3', '4'])).
% 8.66/8.89  thf(t88_relat_1, axiom,
% 8.66/8.89    (![A:$i,B:$i]:
% 8.66/8.89     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 8.66/8.89  thf('6', plain,
% 8.66/8.89      (![X19 : $i, X20 : $i]:
% 8.66/8.89         ((r1_tarski @ (k7_relat_1 @ X19 @ X20) @ X19) | ~ (v1_relat_1 @ X19))),
% 8.66/8.89      inference('cnf', [status(esa)], [t88_relat_1])).
% 8.66/8.89  thf(t3_subset, axiom,
% 8.66/8.89    (![A:$i,B:$i]:
% 8.66/8.89     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 8.66/8.89  thf('7', plain,
% 8.66/8.89      (![X3 : $i, X5 : $i]:
% 8.66/8.89         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 8.66/8.89      inference('cnf', [status(esa)], [t3_subset])).
% 8.66/8.89  thf('8', plain,
% 8.66/8.89      (![X0 : $i, X1 : $i]:
% 8.66/8.89         (~ (v1_relat_1 @ X0)
% 8.66/8.89          | (m1_subset_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 8.66/8.89      inference('sup-', [status(thm)], ['6', '7'])).
% 8.66/8.89  thf(cc2_relat_1, axiom,
% 8.66/8.89    (![A:$i]:
% 8.66/8.89     ( ( v1_relat_1 @ A ) =>
% 8.66/8.89       ( ![B:$i]:
% 8.66/8.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 8.66/8.89  thf('9', plain,
% 8.66/8.89      (![X6 : $i, X7 : $i]:
% 8.66/8.89         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 8.66/8.89          | (v1_relat_1 @ X6)
% 8.66/8.89          | ~ (v1_relat_1 @ X7))),
% 8.66/8.89      inference('cnf', [status(esa)], [cc2_relat_1])).
% 8.66/8.89  thf('10', plain,
% 8.66/8.89      (![X0 : $i, X1 : $i]:
% 8.66/8.89         (~ (v1_relat_1 @ X0)
% 8.66/8.89          | ~ (v1_relat_1 @ X0)
% 8.66/8.89          | (v1_relat_1 @ (k7_relat_1 @ X0 @ X1)))),
% 8.66/8.89      inference('sup-', [status(thm)], ['8', '9'])).
% 8.66/8.89  thf('11', plain,
% 8.66/8.89      (![X0 : $i, X1 : $i]:
% 8.66/8.89         ((v1_relat_1 @ (k7_relat_1 @ X0 @ X1)) | ~ (v1_relat_1 @ X0))),
% 8.66/8.89      inference('simplify', [status(thm)], ['10'])).
% 8.66/8.89  thf('12', plain,
% 8.66/8.89      (![X0 : $i]:
% 8.66/8.89         (~ (v1_relat_1 @ X0)
% 8.66/8.89          | ((k2_relat_1 @ (k7_relat_1 @ X0 @ sk_E))
% 8.66/8.89              = (k9_relat_1 @ (k7_relat_1 @ X0 @ (u1_struct_0 @ sk_C)) @ sk_E)))),
% 8.66/8.89      inference('clc', [status(thm)], ['5', '11'])).
% 8.66/8.89  thf('13', plain,
% 8.66/8.89      (((k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 8.66/8.89         sk_E)
% 8.66/8.89         != (k7_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 8.66/8.89             (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) @ sk_E))),
% 8.66/8.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.66/8.89  thf('14', plain,
% 8.66/8.89      ((m1_subset_1 @ sk_D @ 
% 8.66/8.89        (k1_zfmisc_1 @ 
% 8.66/8.89         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 8.66/8.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.66/8.89  thf(redefinition_k7_relset_1, axiom,
% 8.66/8.89    (![A:$i,B:$i,C:$i,D:$i]:
% 8.66/8.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.66/8.89       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 8.66/8.89  thf('15', plain,
% 8.66/8.89      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 8.66/8.89         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 8.66/8.89          | ((k7_relset_1 @ X25 @ X26 @ X24 @ X27) = (k9_relat_1 @ X24 @ X27)))),
% 8.66/8.89      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 8.66/8.89  thf('16', plain,
% 8.66/8.89      (![X0 : $i]:
% 8.66/8.89         ((k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 8.66/8.89           X0) = (k9_relat_1 @ sk_D @ X0))),
% 8.66/8.89      inference('sup-', [status(thm)], ['14', '15'])).
% 8.66/8.89  thf('17', plain,
% 8.66/8.89      (((k9_relat_1 @ sk_D @ sk_E)
% 8.66/8.89         != (k7_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 8.66/8.89             (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) @ sk_E))),
% 8.66/8.89      inference('demod', [status(thm)], ['13', '16'])).
% 8.66/8.89  thf('18', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 8.66/8.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.66/8.89  thf('19', plain,
% 8.66/8.89      ((m1_subset_1 @ sk_D @ 
% 8.66/8.89        (k1_zfmisc_1 @ 
% 8.66/8.89         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 8.66/8.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.66/8.89  thf(d4_tmap_1, axiom,
% 8.66/8.89    (![A:$i]:
% 8.66/8.89     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 8.66/8.89       ( ![B:$i]:
% 8.66/8.89         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 8.66/8.89             ( l1_pre_topc @ B ) ) =>
% 8.66/8.89           ( ![C:$i]:
% 8.66/8.89             ( ( ( v1_funct_1 @ C ) & 
% 8.66/8.89                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 8.66/8.89                 ( m1_subset_1 @
% 8.66/8.89                   C @ 
% 8.66/8.89                   ( k1_zfmisc_1 @
% 8.66/8.89                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 8.66/8.89               ( ![D:$i]:
% 8.66/8.89                 ( ( m1_pre_topc @ D @ A ) =>
% 8.66/8.89                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 8.66/8.89                     ( k2_partfun1 @
% 8.66/8.89                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 8.66/8.89                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 8.66/8.89  thf('20', plain,
% 8.66/8.89      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 8.66/8.89         ((v2_struct_0 @ X35)
% 8.66/8.89          | ~ (v2_pre_topc @ X35)
% 8.66/8.89          | ~ (l1_pre_topc @ X35)
% 8.66/8.89          | ~ (m1_pre_topc @ X36 @ X37)
% 8.66/8.89          | ((k2_tmap_1 @ X37 @ X35 @ X38 @ X36)
% 8.66/8.89              = (k2_partfun1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X35) @ 
% 8.66/8.89                 X38 @ (u1_struct_0 @ X36)))
% 8.66/8.89          | ~ (m1_subset_1 @ X38 @ 
% 8.66/8.89               (k1_zfmisc_1 @ 
% 8.66/8.89                (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X35))))
% 8.66/8.89          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X35))
% 8.66/8.89          | ~ (v1_funct_1 @ X38)
% 8.66/8.89          | ~ (l1_pre_topc @ X37)
% 8.66/8.89          | ~ (v2_pre_topc @ X37)
% 8.66/8.89          | (v2_struct_0 @ X37))),
% 8.66/8.89      inference('cnf', [status(esa)], [d4_tmap_1])).
% 8.66/8.89  thf('21', plain,
% 8.66/8.89      (![X0 : $i]:
% 8.66/8.89         ((v2_struct_0 @ sk_B)
% 8.66/8.89          | ~ (v2_pre_topc @ sk_B)
% 8.66/8.89          | ~ (l1_pre_topc @ sk_B)
% 8.66/8.89          | ~ (v1_funct_1 @ sk_D)
% 8.66/8.89          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 8.66/8.89          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 8.66/8.89              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 8.66/8.89                 sk_D @ (u1_struct_0 @ X0)))
% 8.66/8.89          | ~ (m1_pre_topc @ X0 @ sk_B)
% 8.66/8.89          | ~ (l1_pre_topc @ sk_A)
% 8.66/8.89          | ~ (v2_pre_topc @ sk_A)
% 8.66/8.89          | (v2_struct_0 @ sk_A))),
% 8.66/8.89      inference('sup-', [status(thm)], ['19', '20'])).
% 8.66/8.89  thf('22', plain, ((v2_pre_topc @ sk_B)),
% 8.66/8.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.66/8.89  thf('23', plain, ((l1_pre_topc @ sk_B)),
% 8.66/8.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.66/8.89  thf('24', plain, ((v1_funct_1 @ sk_D)),
% 8.66/8.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.66/8.89  thf('25', plain,
% 8.66/8.89      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 8.66/8.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.66/8.89  thf('26', plain,
% 8.66/8.89      ((m1_subset_1 @ sk_D @ 
% 8.66/8.89        (k1_zfmisc_1 @ 
% 8.66/8.89         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 8.66/8.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.66/8.89  thf(redefinition_k2_partfun1, axiom,
% 8.66/8.89    (![A:$i,B:$i,C:$i,D:$i]:
% 8.66/8.89     ( ( ( v1_funct_1 @ C ) & 
% 8.66/8.89         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 8.66/8.89       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 8.66/8.89  thf('27', plain,
% 8.66/8.89      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 8.66/8.89         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 8.66/8.89          | ~ (v1_funct_1 @ X31)
% 8.66/8.89          | ((k2_partfun1 @ X32 @ X33 @ X31 @ X34) = (k7_relat_1 @ X31 @ X34)))),
% 8.66/8.89      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 8.66/8.89  thf('28', plain,
% 8.66/8.89      (![X0 : $i]:
% 8.66/8.89         (((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 8.66/8.89            X0) = (k7_relat_1 @ sk_D @ X0))
% 8.66/8.89          | ~ (v1_funct_1 @ sk_D))),
% 8.66/8.89      inference('sup-', [status(thm)], ['26', '27'])).
% 8.66/8.89  thf('29', plain, ((v1_funct_1 @ sk_D)),
% 8.66/8.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.66/8.89  thf('30', plain,
% 8.66/8.89      (![X0 : $i]:
% 8.66/8.89         ((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 8.66/8.89           X0) = (k7_relat_1 @ sk_D @ X0))),
% 8.66/8.89      inference('demod', [status(thm)], ['28', '29'])).
% 8.66/8.89  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 8.66/8.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.66/8.89  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 8.66/8.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.66/8.89  thf('33', plain,
% 8.66/8.89      (![X0 : $i]:
% 8.66/8.89         ((v2_struct_0 @ sk_B)
% 8.66/8.89          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 8.66/8.89              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X0)))
% 8.66/8.89          | ~ (m1_pre_topc @ X0 @ sk_B)
% 8.66/8.89          | (v2_struct_0 @ sk_A))),
% 8.66/8.89      inference('demod', [status(thm)],
% 8.66/8.89                ['21', '22', '23', '24', '25', '30', '31', '32'])).
% 8.66/8.89  thf('34', plain,
% 8.66/8.89      (((v2_struct_0 @ sk_A)
% 8.66/8.89        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 8.66/8.89            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 8.66/8.89        | (v2_struct_0 @ sk_B))),
% 8.66/8.89      inference('sup-', [status(thm)], ['18', '33'])).
% 8.66/8.89  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 8.66/8.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.66/8.89  thf('36', plain,
% 8.66/8.89      (((v2_struct_0 @ sk_B)
% 8.66/8.89        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 8.66/8.89            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C))))),
% 8.66/8.89      inference('clc', [status(thm)], ['34', '35'])).
% 8.66/8.89  thf('37', plain, (~ (v2_struct_0 @ sk_B)),
% 8.66/8.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.66/8.89  thf('38', plain,
% 8.66/8.89      (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 8.66/8.89         = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 8.66/8.89      inference('clc', [status(thm)], ['36', '37'])).
% 8.66/8.89  thf('39', plain,
% 8.66/8.89      ((m1_subset_1 @ sk_D @ 
% 8.66/8.89        (k1_zfmisc_1 @ 
% 8.66/8.89         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 8.66/8.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.66/8.89  thf('40', plain,
% 8.66/8.89      (![X3 : $i, X4 : $i]:
% 8.66/8.89         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 8.66/8.89      inference('cnf', [status(esa)], [t3_subset])).
% 8.66/8.89  thf('41', plain,
% 8.66/8.89      ((r1_tarski @ sk_D @ 
% 8.66/8.89        (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 8.66/8.89      inference('sup-', [status(thm)], ['39', '40'])).
% 8.66/8.89  thf('42', plain,
% 8.66/8.89      (![X19 : $i, X20 : $i]:
% 8.66/8.89         ((r1_tarski @ (k7_relat_1 @ X19 @ X20) @ X19) | ~ (v1_relat_1 @ X19))),
% 8.66/8.89      inference('cnf', [status(esa)], [t88_relat_1])).
% 8.66/8.89  thf(t1_xboole_1, axiom,
% 8.66/8.89    (![A:$i,B:$i,C:$i]:
% 8.66/8.89     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 8.66/8.89       ( r1_tarski @ A @ C ) ))).
% 8.66/8.89  thf('43', plain,
% 8.66/8.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.66/8.89         (~ (r1_tarski @ X0 @ X1)
% 8.66/8.89          | ~ (r1_tarski @ X1 @ X2)
% 8.66/8.89          | (r1_tarski @ X0 @ X2))),
% 8.66/8.89      inference('cnf', [status(esa)], [t1_xboole_1])).
% 8.66/8.89  thf('44', plain,
% 8.66/8.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.66/8.89         (~ (v1_relat_1 @ X0)
% 8.66/8.89          | (r1_tarski @ (k7_relat_1 @ X0 @ X1) @ X2)
% 8.66/8.89          | ~ (r1_tarski @ X0 @ X2))),
% 8.66/8.89      inference('sup-', [status(thm)], ['42', '43'])).
% 8.66/8.89  thf('45', plain,
% 8.66/8.89      (![X0 : $i]:
% 8.66/8.89         ((r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ 
% 8.66/8.89           (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))
% 8.66/8.89          | ~ (v1_relat_1 @ sk_D))),
% 8.66/8.89      inference('sup-', [status(thm)], ['41', '44'])).
% 8.66/8.89  thf('46', plain,
% 8.66/8.89      ((m1_subset_1 @ sk_D @ 
% 8.66/8.89        (k1_zfmisc_1 @ 
% 8.66/8.89         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 8.66/8.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.66/8.89  thf('47', plain,
% 8.66/8.89      (![X6 : $i, X7 : $i]:
% 8.66/8.89         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 8.66/8.89          | (v1_relat_1 @ X6)
% 8.66/8.89          | ~ (v1_relat_1 @ X7))),
% 8.66/8.89      inference('cnf', [status(esa)], [cc2_relat_1])).
% 8.66/8.89  thf('48', plain,
% 8.66/8.89      ((~ (v1_relat_1 @ 
% 8.66/8.89           (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))
% 8.66/8.89        | (v1_relat_1 @ sk_D))),
% 8.66/8.89      inference('sup-', [status(thm)], ['46', '47'])).
% 8.66/8.89  thf(fc6_relat_1, axiom,
% 8.66/8.89    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 8.66/8.89  thf('49', plain,
% 8.66/8.89      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 8.66/8.89      inference('cnf', [status(esa)], [fc6_relat_1])).
% 8.66/8.89  thf('50', plain, ((v1_relat_1 @ sk_D)),
% 8.66/8.89      inference('demod', [status(thm)], ['48', '49'])).
% 8.66/8.89  thf('51', plain,
% 8.66/8.89      (![X0 : $i]:
% 8.66/8.89         (r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ 
% 8.66/8.89          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 8.66/8.89      inference('demod', [status(thm)], ['45', '50'])).
% 8.66/8.89  thf('52', plain,
% 8.66/8.89      (![X3 : $i, X5 : $i]:
% 8.66/8.89         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 8.66/8.89      inference('cnf', [status(esa)], [t3_subset])).
% 8.66/8.89  thf('53', plain,
% 8.66/8.89      (![X0 : $i]:
% 8.66/8.89         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 8.66/8.89          (k1_zfmisc_1 @ 
% 8.66/8.89           (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 8.66/8.89      inference('sup-', [status(thm)], ['51', '52'])).
% 8.66/8.89  thf(cc2_relset_1, axiom,
% 8.66/8.89    (![A:$i,B:$i,C:$i]:
% 8.66/8.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.66/8.89       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 8.66/8.89  thf('54', plain,
% 8.66/8.89      (![X21 : $i, X22 : $i, X23 : $i]:
% 8.66/8.89         ((v5_relat_1 @ X21 @ X23)
% 8.66/8.89          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 8.66/8.89      inference('cnf', [status(esa)], [cc2_relset_1])).
% 8.66/8.89  thf('55', plain,
% 8.66/8.89      (![X0 : $i]:
% 8.66/8.89         (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ (u1_struct_0 @ sk_A))),
% 8.66/8.89      inference('sup-', [status(thm)], ['53', '54'])).
% 8.66/8.89  thf(d19_relat_1, axiom,
% 8.66/8.89    (![A:$i,B:$i]:
% 8.66/8.89     ( ( v1_relat_1 @ B ) =>
% 8.66/8.89       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 8.66/8.89  thf('56', plain,
% 8.66/8.89      (![X8 : $i, X9 : $i]:
% 8.66/8.89         (~ (v5_relat_1 @ X8 @ X9)
% 8.66/8.89          | (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 8.66/8.89          | ~ (v1_relat_1 @ X8))),
% 8.66/8.89      inference('cnf', [status(esa)], [d19_relat_1])).
% 8.66/8.89  thf('57', plain,
% 8.66/8.89      (![X0 : $i]:
% 8.66/8.89         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 8.66/8.89          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ 
% 8.66/8.89             (u1_struct_0 @ sk_A)))),
% 8.66/8.89      inference('sup-', [status(thm)], ['55', '56'])).
% 8.66/8.89  thf('58', plain,
% 8.66/8.89      (![X0 : $i]:
% 8.66/8.89         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 8.66/8.89          (k1_zfmisc_1 @ 
% 8.66/8.89           (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 8.66/8.89      inference('sup-', [status(thm)], ['51', '52'])).
% 8.66/8.89  thf('59', plain,
% 8.66/8.89      (![X6 : $i, X7 : $i]:
% 8.66/8.89         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 8.66/8.89          | (v1_relat_1 @ X6)
% 8.66/8.89          | ~ (v1_relat_1 @ X7))),
% 8.66/8.89      inference('cnf', [status(esa)], [cc2_relat_1])).
% 8.66/8.89  thf('60', plain,
% 8.66/8.89      (![X0 : $i]:
% 8.66/8.89         (~ (v1_relat_1 @ 
% 8.66/8.89             (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))
% 8.66/8.89          | (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 8.66/8.89      inference('sup-', [status(thm)], ['58', '59'])).
% 8.66/8.89  thf('61', plain,
% 8.66/8.89      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 8.66/8.89      inference('cnf', [status(esa)], [fc6_relat_1])).
% 8.66/8.89  thf('62', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 8.66/8.89      inference('demod', [status(thm)], ['60', '61'])).
% 8.66/8.89  thf('63', plain,
% 8.66/8.89      (![X0 : $i]:
% 8.66/8.89         (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ 
% 8.66/8.89          (u1_struct_0 @ sk_A))),
% 8.66/8.89      inference('demod', [status(thm)], ['57', '62'])).
% 8.66/8.89  thf(t87_relat_1, axiom,
% 8.66/8.89    (![A:$i,B:$i]:
% 8.66/8.89     ( ( v1_relat_1 @ B ) =>
% 8.66/8.89       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 8.66/8.89  thf('64', plain,
% 8.66/8.89      (![X17 : $i, X18 : $i]:
% 8.66/8.89         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X17 @ X18)) @ X18)
% 8.66/8.89          | ~ (v1_relat_1 @ X17))),
% 8.66/8.89      inference('cnf', [status(esa)], [t87_relat_1])).
% 8.66/8.89  thf(t11_relset_1, axiom,
% 8.66/8.89    (![A:$i,B:$i,C:$i]:
% 8.66/8.89     ( ( v1_relat_1 @ C ) =>
% 8.66/8.89       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 8.66/8.89           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 8.66/8.89         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 8.66/8.89  thf('65', plain,
% 8.66/8.89      (![X28 : $i, X29 : $i, X30 : $i]:
% 8.66/8.89         (~ (r1_tarski @ (k1_relat_1 @ X28) @ X29)
% 8.66/8.89          | ~ (r1_tarski @ (k2_relat_1 @ X28) @ X30)
% 8.66/8.89          | (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 8.66/8.89          | ~ (v1_relat_1 @ X28))),
% 8.66/8.89      inference('cnf', [status(esa)], [t11_relset_1])).
% 8.66/8.89  thf('66', plain,
% 8.66/8.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.66/8.89         (~ (v1_relat_1 @ X1)
% 8.66/8.89          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 8.66/8.89          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 8.66/8.89             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 8.66/8.89          | ~ (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2))),
% 8.66/8.89      inference('sup-', [status(thm)], ['64', '65'])).
% 8.66/8.89  thf('67', plain,
% 8.66/8.89      (![X0 : $i]:
% 8.66/8.89         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 8.66/8.89           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 8.66/8.89          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 8.66/8.89          | ~ (v1_relat_1 @ sk_D))),
% 8.66/8.89      inference('sup-', [status(thm)], ['63', '66'])).
% 8.66/8.89  thf('68', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 8.66/8.89      inference('demod', [status(thm)], ['60', '61'])).
% 8.66/8.89  thf('69', plain, ((v1_relat_1 @ sk_D)),
% 8.66/8.89      inference('demod', [status(thm)], ['48', '49'])).
% 8.66/8.89  thf('70', plain,
% 8.66/8.89      (![X0 : $i]:
% 8.66/8.89         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 8.66/8.89          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_A))))),
% 8.66/8.89      inference('demod', [status(thm)], ['67', '68', '69'])).
% 8.66/8.89  thf('71', plain,
% 8.66/8.89      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 8.66/8.89         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 8.66/8.89          | ((k7_relset_1 @ X25 @ X26 @ X24 @ X27) = (k9_relat_1 @ X24 @ X27)))),
% 8.66/8.89      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 8.66/8.89  thf('72', plain,
% 8.66/8.89      (![X0 : $i, X1 : $i]:
% 8.66/8.89         ((k7_relset_1 @ X0 @ (u1_struct_0 @ sk_A) @ 
% 8.66/8.89           (k7_relat_1 @ sk_D @ X0) @ X1)
% 8.66/8.89           = (k9_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ X1))),
% 8.66/8.89      inference('sup-', [status(thm)], ['70', '71'])).
% 8.66/8.89  thf('73', plain,
% 8.66/8.89      (((k9_relat_1 @ sk_D @ sk_E)
% 8.66/8.89         != (k9_relat_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E))),
% 8.66/8.89      inference('demod', [status(thm)], ['17', '38', '72'])).
% 8.66/8.89  thf('74', plain,
% 8.66/8.89      ((((k9_relat_1 @ sk_D @ sk_E)
% 8.66/8.89          != (k2_relat_1 @ (k7_relat_1 @ sk_D @ sk_E)))
% 8.66/8.89        | ~ (v1_relat_1 @ sk_D))),
% 8.66/8.89      inference('sup-', [status(thm)], ['12', '73'])).
% 8.66/8.89  thf('75', plain, ((v1_relat_1 @ sk_D)),
% 8.66/8.89      inference('demod', [status(thm)], ['48', '49'])).
% 8.66/8.89  thf('76', plain,
% 8.66/8.89      (((k9_relat_1 @ sk_D @ sk_E) != (k2_relat_1 @ (k7_relat_1 @ sk_D @ sk_E)))),
% 8.66/8.89      inference('demod', [status(thm)], ['74', '75'])).
% 8.66/8.89  thf('77', plain,
% 8.66/8.89      ((((k9_relat_1 @ sk_D @ sk_E) != (k9_relat_1 @ sk_D @ sk_E))
% 8.66/8.89        | ~ (v1_relat_1 @ sk_D))),
% 8.66/8.89      inference('sup-', [status(thm)], ['0', '76'])).
% 8.66/8.89  thf('78', plain, ((v1_relat_1 @ sk_D)),
% 8.66/8.89      inference('demod', [status(thm)], ['48', '49'])).
% 8.66/8.89  thf('79', plain,
% 8.66/8.89      (((k9_relat_1 @ sk_D @ sk_E) != (k9_relat_1 @ sk_D @ sk_E))),
% 8.66/8.89      inference('demod', [status(thm)], ['77', '78'])).
% 8.66/8.89  thf('80', plain, ($false), inference('simplify', [status(thm)], ['79'])).
% 8.66/8.89  
% 8.66/8.89  % SZS output end Refutation
% 8.66/8.89  
% 8.66/8.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
