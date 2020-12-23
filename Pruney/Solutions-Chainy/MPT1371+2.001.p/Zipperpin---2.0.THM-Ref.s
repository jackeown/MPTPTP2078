%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.K18QxIXx9E

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:41 EST 2020

% Result     : Theorem 4.44s
% Output     : Refutation 4.44s
% Verified   : 
% Statistics : Number of formulae       :  264 (4027 expanded)
%              Number of leaves         :   47 (1219 expanded)
%              Depth                    :   32
%              Number of atoms          : 2895 (94925 expanded)
%              Number of equality atoms :  135 (4067 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v3_tops_2_type,type,(
    v3_tops_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X41: $i] :
      ( ( ( k2_struct_0 @ X41 )
        = ( u1_struct_0 @ X41 ) )
      | ~ ( l1_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t26_compts_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( v1_compts_1 @ A )
                  & ( v8_pre_topc @ B )
                  & ( ( k1_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ A ) )
                  & ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v2_funct_1 @ C )
                  & ( v5_pre_topc @ C @ A @ B ) )
               => ( v3_tops_2 @ C @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v2_pre_topc @ B )
              & ( l1_pre_topc @ B ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( ( ( v1_compts_1 @ A )
                    & ( v8_pre_topc @ B )
                    & ( ( k1_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                      = ( k2_struct_0 @ A ) )
                    & ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                      = ( k2_struct_0 @ B ) )
                    & ( v2_funct_1 @ C )
                    & ( v5_pre_topc @ C @ A @ B ) )
                 => ( v3_tops_2 @ C @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t26_compts_1])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('4',plain,(
    ! [X42: $i] :
      ( ( l1_struct_0 @ X42 )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('5',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('9',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('13',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k7_relset_1 @ X25 @ X26 @ X24 @ X27 )
        = ( k9_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X41: $i] :
      ( ( ( k2_struct_0 @ X41 )
        = ( u1_struct_0 @ X41 ) )
      | ~ ( l1_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('16',plain,(
    ! [X41: $i] :
      ( ( ( k2_struct_0 @ X41 )
        = ( u1_struct_0 @ X41 ) )
      | ~ ( l1_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('18',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k7_relset_1 @ X32 @ X33 @ X34 @ X32 )
        = ( k2_relset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('19',plain,
    ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_A ) )
    = ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('21',plain,
    ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_A ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k7_relset_1 @ X25 @ X26 @ X24 @ X27 )
        = ( k9_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k9_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['16','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('28',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('29',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X42: $i] :
      ( ( l1_struct_0 @ X42 )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('34',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['26','31','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('37',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X15 @ X16 @ X14 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('40',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_relat_1 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['35','40'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('42',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('43',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('44',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('45',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ sk_B )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','45'])).

thf('47',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('49',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf('51',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['46','47','49','50'])).

thf(t72_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( v3_tops_2 @ C @ A @ B )
              <=> ( ( ( k1_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ A ) )
                  & ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v2_funct_1 @ C )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                     => ( ( v4_pre_topc @ D @ A )
                      <=> ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ B ) ) ) ) ) ) ) ) )).

thf('52',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( v2_struct_0 @ X43 )
      | ~ ( l1_pre_topc @ X43 )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X43 ) @ X45 )
       != ( k2_struct_0 @ X44 ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X43 ) @ X45 )
       != ( k2_struct_0 @ X43 ) )
      | ~ ( v2_funct_1 @ X45 )
      | ~ ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X43 ) @ X45 @ ( sk_D_1 @ X45 @ X43 @ X44 ) ) @ X43 )
      | ~ ( v4_pre_topc @ ( sk_D_1 @ X45 @ X43 @ X44 ) @ X44 )
      | ( v3_tops_2 @ X45 @ X44 @ X43 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X43 ) ) ) )
      | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X43 ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[t72_tops_2])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_relat_1 @ sk_C ) @ X1 @ ( sk_D_1 @ X1 @ sk_B @ X0 ) ) @ sk_B )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v3_tops_2 @ X1 @ X0 @ sk_B )
      | ~ ( v4_pre_topc @ ( sk_D_1 @ X1 @ sk_B @ X0 ) @ X0 )
      | ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 )
       != ( k2_struct_0 @ sk_B ) )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 )
       != ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['46','47','49','50'])).

thf('55',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['46','47','49','50'])).

thf('56',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['46','47','49','50'])).

thf('57',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('58',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['46','47','49','50'])).

thf('59',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_relat_1 @ sk_C ) @ X1 @ ( sk_D_1 @ X1 @ sk_B @ X0 ) ) @ sk_B )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( k2_relat_1 @ sk_C ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( k2_relat_1 @ sk_C ) ) ) )
      | ( v3_tops_2 @ X1 @ X0 @ sk_B )
      | ~ ( v4_pre_topc @ ( sk_D_1 @ X1 @ sk_B @ X0 ) @ X0 )
      | ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_relat_1 @ sk_C ) @ X1 )
       != ( k2_relat_1 @ sk_C ) )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_relat_1 @ sk_C ) @ X1 )
       != ( k2_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54','55','56','57','58','59'])).

thf('61',plain,
    ( ~ ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v4_pre_topc @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['14','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('63',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('64',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('66',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('68',plain,(
    ! [X41: $i] :
      ( ( ( k2_struct_0 @ X41 )
        = ( u1_struct_0 @ X41 ) )
      | ~ ( l1_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('69',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf('72',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('74',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('75',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('78',plain,(
    ! [X41: $i] :
      ( ( ( k2_struct_0 @ X41 )
        = ( u1_struct_0 @ X41 ) )
      | ~ ( l1_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('79',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf('82',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('84',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ~ ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v4_pre_topc @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['61','66','67','75','76','77','84','85','86'])).

thf('88',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v4_pre_topc @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_B ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('90',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['46','47','49','50'])).

thf('91',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( v2_struct_0 @ X43 )
      | ~ ( l1_pre_topc @ X43 )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X43 ) @ X45 )
       != ( k2_struct_0 @ X44 ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X43 ) @ X45 )
       != ( k2_struct_0 @ X43 ) )
      | ~ ( v2_funct_1 @ X45 )
      | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X43 ) @ X45 @ ( sk_D_1 @ X45 @ X43 @ X44 ) ) @ X43 )
      | ( v4_pre_topc @ ( sk_D_1 @ X45 @ X43 @ X44 ) @ X44 )
      | ( v3_tops_2 @ X45 @ X44 @ X43 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X43 ) ) ) )
      | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X43 ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[t72_tops_2])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( k2_relat_1 @ sk_C ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v3_tops_2 @ X1 @ X0 @ sk_B )
      | ( v4_pre_topc @ ( sk_D_1 @ X1 @ sk_B @ X0 ) @ X0 )
      | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 @ ( sk_D_1 @ X1 @ sk_B @ X0 ) ) @ sk_B )
      | ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 )
       != ( k2_struct_0 @ sk_B ) )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 )
       != ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['46','47','49','50'])).

thf('94',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['46','47','49','50'])).

thf('95',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['46','47','49','50'])).

thf('96',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('97',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['46','47','49','50'])).

thf('98',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( k2_relat_1 @ sk_C ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( k2_relat_1 @ sk_C ) )
      | ( v3_tops_2 @ X1 @ X0 @ sk_B )
      | ( v4_pre_topc @ ( sk_D_1 @ X1 @ sk_B @ X0 ) @ X0 )
      | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_relat_1 @ sk_C ) @ X1 @ ( sk_D_1 @ X1 @ sk_B @ X0 ) ) @ sk_B )
      | ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_relat_1 @ sk_C ) @ X1 )
       != ( k2_relat_1 @ sk_C ) )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_relat_1 @ sk_C ) @ X1 )
       != ( k2_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['92','93','94','95','96','97','98'])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_B )
    | ( v4_pre_topc @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['89','99'])).

thf('101',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('102',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('103',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('104',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('106',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('107',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_B )
    | ( v4_pre_topc @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['100','101','102','103','104','105','106','107','108'])).

thf('110',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( v4_pre_topc @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X41: $i] :
      ( ( ( k2_struct_0 @ X41 )
        = ( u1_struct_0 @ X41 ) )
      | ~ ( l1_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('112',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_relat_1 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k9_relat_1 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) )
      | ~ ( l1_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('115',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf('116',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_relat_1 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,(
    ! [X41: $i] :
      ( ( ( k2_struct_0 @ X41 )
        = ( u1_struct_0 @ X41 ) )
      | ~ ( l1_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('118',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('119',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( l1_pre_topc @ X37 )
      | ~ ( v5_pre_topc @ X38 @ X39 @ X37 )
      | ~ ( v4_pre_topc @ X40 @ X37 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X37 ) @ X38 @ X40 ) @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X37 ) ) ) )
      | ~ ( v1_funct_2 @ X38 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X37 ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_B )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('125',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( ( k8_relset_1 @ X29 @ X30 @ X28 @ X31 )
        = ( k10_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['120','121','122','123','126','127','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v4_pre_topc @ X0 @ sk_B )
      | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['117','129'])).

thf('131',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('132',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_relat_1 @ sk_C ) ) )
      | ~ ( v4_pre_topc @ X0 @ sk_B )
      | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) ) @ sk_A )
      | ~ ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['116','133'])).

thf('135',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v4_pre_topc @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( v4_pre_topc @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['110','134'])).

thf('136',plain,(
    ! [X41: $i] :
      ( ( ( k2_struct_0 @ X41 )
        = ( u1_struct_0 @ X41 ) )
      | ~ ( l1_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('137',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('138',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['46','47','49','50'])).

thf('139',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( v2_struct_0 @ X43 )
      | ~ ( l1_pre_topc @ X43 )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X43 ) @ X45 )
       != ( k2_struct_0 @ X44 ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X43 ) @ X45 )
       != ( k2_struct_0 @ X43 ) )
      | ~ ( v2_funct_1 @ X45 )
      | ( m1_subset_1 @ ( sk_D_1 @ X45 @ X43 @ X44 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ( v3_tops_2 @ X45 @ X44 @ X43 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X43 ) ) ) )
      | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X43 ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[t72_tops_2])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( k2_relat_1 @ sk_C ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v3_tops_2 @ X1 @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ X1 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 )
       != ( k2_struct_0 @ sk_B ) )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 )
       != ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['46','47','49','50'])).

thf('142',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['46','47','49','50'])).

thf('143',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('144',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['46','47','49','50'])).

thf('145',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( k2_relat_1 @ sk_C ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( k2_relat_1 @ sk_C ) )
      | ( v3_tops_2 @ X1 @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ X1 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_relat_1 @ sk_C ) @ X1 )
       != ( k2_relat_1 @ sk_C ) )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_relat_1 @ sk_C ) @ X1 )
       != ( k2_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['140','141','142','143','144','145'])).

thf('147',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['137','146'])).

thf('148',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('149',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('150',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('151',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('153',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['147','148','149','150','151','152','153','154'])).

thf('156',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,(
    ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('159',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('162',plain,(
    r1_tarski @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,
    ( ( r1_tarski @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['136','162'])).

thf('164',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('165',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['32','33'])).

thf('166',plain,(
    r1_tarski @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['163','164','165'])).

thf(t164_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('167',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X6 @ ( k1_relat_1 @ X7 ) )
      | ~ ( v2_funct_1 @ X7 )
      | ( ( k10_relat_1 @ X7 @ ( k9_relat_1 @ X7 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('168',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      = ( sk_D_1 @ sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('170',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('171',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    = ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['168','171','172','173'])).

thf('175',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v4_pre_topc @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( v4_pre_topc @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['135','174'])).

thf('176',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( v4_pre_topc @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,(
    ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v4_pre_topc @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['176','177'])).

thf('179',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    v4_pre_topc @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['178','179'])).

thf('181',plain,
    ( ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['88','180'])).

thf('182',plain,(
    ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ~ ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['181','182'])).

thf('184',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    ~ ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_B ) ),
    inference(clc,[status(thm)],['183','184'])).

thf('186',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['158','159'])).

thf('187',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('188',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['46','47','49','50'])).

thf(t25_compts_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( v1_compts_1 @ A )
                  & ( v8_pre_topc @ B )
                  & ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v5_pre_topc @ C @ A @ B ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ( ( v4_pre_topc @ D @ A )
                     => ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ B ) ) ) ) ) ) ) )).

thf('189',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( v2_struct_0 @ X47 )
      | ~ ( v2_pre_topc @ X47 )
      | ~ ( l1_pre_topc @ X47 )
      | ~ ( v1_compts_1 @ X48 )
      | ~ ( v8_pre_topc @ X47 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ X47 ) @ X49 )
       != ( k2_struct_0 @ X47 ) )
      | ~ ( v5_pre_topc @ X49 @ X48 @ X47 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ X47 ) @ X49 @ X50 ) @ X47 )
      | ~ ( v4_pre_topc @ X50 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ X47 ) ) ) )
      | ~ ( v1_funct_2 @ X49 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ X47 ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( l1_pre_topc @ X48 )
      | ~ ( v2_pre_topc @ X48 ) ) ),
    inference(cnf,[status(esa)],[t25_compts_1])).

thf('190',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( k2_relat_1 @ sk_C ) ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v4_pre_topc @ X2 @ X0 )
      | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 @ X2 ) @ sk_B )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v5_pre_topc @ X1 @ X0 @ sk_B )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( v8_pre_topc @ sk_B )
      | ~ ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['46','47','49','50'])).

thf('192',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['46','47','49','50'])).

thf('193',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['46','47','49','50'])).

thf('194',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('195',plain,(
    v8_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( k2_relat_1 @ sk_C ) ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( k2_relat_1 @ sk_C ) )
      | ~ ( v4_pre_topc @ X2 @ X0 )
      | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_relat_1 @ sk_C ) @ X1 @ X2 ) @ sk_B )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v5_pre_topc @ X1 @ X0 @ sk_B )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_relat_1 @ sk_C ) @ X1 )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( v1_compts_1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['190','191','192','193','194','195','196','197'])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v1_compts_1 @ sk_A )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C @ X0 ) @ sk_B )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['187','198'])).

thf('200',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('202',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('204',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('205',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( k2_relat_1 @ sk_C )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ X0 ) @ sk_B )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['199','200','201','202','203','204','205','206','207'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ X0 @ sk_A )
      | ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['208'])).

thf('210',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_B )
    | ~ ( v4_pre_topc @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['186','209'])).

thf('211',plain,(
    v4_pre_topc @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['178','179'])).

thf('212',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v4_pre_topc @ ( k9_relat_1 @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['210','211'])).

thf('213',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    v4_pre_topc @ ( k9_relat_1 @ sk_C @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ sk_B ),
    inference(clc,[status(thm)],['212','213'])).

thf('215',plain,(
    $false ),
    inference(demod,[status(thm)],['185','214'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.K18QxIXx9E
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:56:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 4.44/4.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.44/4.66  % Solved by: fo/fo7.sh
% 4.44/4.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.44/4.66  % done 3973 iterations in 4.201s
% 4.44/4.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.44/4.66  % SZS output start Refutation
% 4.44/4.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.44/4.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.44/4.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.44/4.66  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 4.44/4.66  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 4.44/4.66  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 4.44/4.66  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 4.44/4.66  thf(v3_tops_2_type, type, v3_tops_2: $i > $i > $i > $o).
% 4.44/4.66  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 4.44/4.66  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 4.44/4.66  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 4.44/4.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.44/4.66  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 4.44/4.66  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.44/4.66  thf(sk_B_type, type, sk_B: $i).
% 4.44/4.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.44/4.66  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 4.44/4.66  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 4.44/4.66  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 4.44/4.66  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 4.44/4.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.44/4.66  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 4.44/4.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.44/4.66  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 4.44/4.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.44/4.66  thf(sk_A_type, type, sk_A: $i).
% 4.44/4.66  thf(sk_C_type, type, sk_C: $i).
% 4.44/4.66  thf(v1_compts_1_type, type, v1_compts_1: $i > $o).
% 4.44/4.66  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 4.44/4.66  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 4.44/4.66  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 4.44/4.66  thf(d3_struct_0, axiom,
% 4.44/4.66    (![A:$i]:
% 4.44/4.66     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 4.44/4.66  thf('0', plain,
% 4.44/4.66      (![X41 : $i]:
% 4.44/4.66         (((k2_struct_0 @ X41) = (u1_struct_0 @ X41)) | ~ (l1_struct_0 @ X41))),
% 4.44/4.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.44/4.66  thf(t26_compts_1, conjecture,
% 4.44/4.66    (![A:$i]:
% 4.44/4.66     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.44/4.66       ( ![B:$i]:
% 4.44/4.66         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 4.44/4.66             ( l1_pre_topc @ B ) ) =>
% 4.44/4.66           ( ![C:$i]:
% 4.44/4.66             ( ( ( v1_funct_1 @ C ) & 
% 4.44/4.66                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 4.44/4.66                 ( m1_subset_1 @
% 4.44/4.66                   C @ 
% 4.44/4.66                   ( k1_zfmisc_1 @
% 4.44/4.66                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 4.44/4.66               ( ( ( v1_compts_1 @ A ) & ( v8_pre_topc @ B ) & 
% 4.44/4.66                   ( ( k1_relset_1 @
% 4.44/4.66                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 4.44/4.66                     ( k2_struct_0 @ A ) ) & 
% 4.44/4.66                   ( ( k2_relset_1 @
% 4.44/4.66                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 4.44/4.66                     ( k2_struct_0 @ B ) ) & 
% 4.44/4.66                   ( v2_funct_1 @ C ) & ( v5_pre_topc @ C @ A @ B ) ) =>
% 4.44/4.66                 ( v3_tops_2 @ C @ A @ B ) ) ) ) ) ) ))).
% 4.44/4.66  thf(zf_stmt_0, negated_conjecture,
% 4.44/4.66    (~( ![A:$i]:
% 4.44/4.66        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.44/4.66          ( ![B:$i]:
% 4.44/4.66            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 4.44/4.66                ( l1_pre_topc @ B ) ) =>
% 4.44/4.66              ( ![C:$i]:
% 4.44/4.66                ( ( ( v1_funct_1 @ C ) & 
% 4.44/4.66                    ( v1_funct_2 @
% 4.44/4.66                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 4.44/4.66                    ( m1_subset_1 @
% 4.44/4.66                      C @ 
% 4.44/4.66                      ( k1_zfmisc_1 @
% 4.44/4.66                        ( k2_zfmisc_1 @
% 4.44/4.66                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 4.44/4.66                  ( ( ( v1_compts_1 @ A ) & ( v8_pre_topc @ B ) & 
% 4.44/4.66                      ( ( k1_relset_1 @
% 4.44/4.66                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 4.44/4.66                        ( k2_struct_0 @ A ) ) & 
% 4.44/4.66                      ( ( k2_relset_1 @
% 4.44/4.66                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 4.44/4.66                        ( k2_struct_0 @ B ) ) & 
% 4.44/4.66                      ( v2_funct_1 @ C ) & ( v5_pre_topc @ C @ A @ B ) ) =>
% 4.44/4.66                    ( v3_tops_2 @ C @ A @ B ) ) ) ) ) ) ) )),
% 4.44/4.66    inference('cnf.neg', [status(esa)], [t26_compts_1])).
% 4.44/4.66  thf('1', plain,
% 4.44/4.66      ((m1_subset_1 @ sk_C @ 
% 4.44/4.66        (k1_zfmisc_1 @ 
% 4.44/4.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('2', plain,
% 4.44/4.66      (((m1_subset_1 @ sk_C @ 
% 4.44/4.66         (k1_zfmisc_1 @ 
% 4.44/4.66          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 4.44/4.66        | ~ (l1_struct_0 @ sk_B))),
% 4.44/4.66      inference('sup+', [status(thm)], ['0', '1'])).
% 4.44/4.66  thf('3', plain, ((l1_pre_topc @ sk_B)),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf(dt_l1_pre_topc, axiom,
% 4.44/4.66    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 4.44/4.66  thf('4', plain, (![X42 : $i]: ((l1_struct_0 @ X42) | ~ (l1_pre_topc @ X42))),
% 4.44/4.66      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 4.44/4.66  thf('5', plain, ((l1_struct_0 @ sk_B)),
% 4.44/4.66      inference('sup-', [status(thm)], ['3', '4'])).
% 4.44/4.66  thf('6', plain,
% 4.44/4.66      ((m1_subset_1 @ sk_C @ 
% 4.44/4.66        (k1_zfmisc_1 @ 
% 4.44/4.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 4.44/4.66      inference('demod', [status(thm)], ['2', '5'])).
% 4.44/4.66  thf('7', plain,
% 4.44/4.66      ((m1_subset_1 @ sk_C @ 
% 4.44/4.66        (k1_zfmisc_1 @ 
% 4.44/4.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf(redefinition_k2_relset_1, axiom,
% 4.44/4.66    (![A:$i,B:$i,C:$i]:
% 4.44/4.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.44/4.66       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 4.44/4.66  thf('8', plain,
% 4.44/4.66      (![X21 : $i, X22 : $i, X23 : $i]:
% 4.44/4.66         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 4.44/4.66          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 4.44/4.66      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.44/4.66  thf('9', plain,
% 4.44/4.66      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.44/4.66         = (k2_relat_1 @ sk_C))),
% 4.44/4.66      inference('sup-', [status(thm)], ['7', '8'])).
% 4.44/4.66  thf('10', plain,
% 4.44/4.66      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.44/4.66         = (k2_struct_0 @ sk_B))),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('11', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.44/4.66      inference('sup+', [status(thm)], ['9', '10'])).
% 4.44/4.66  thf('12', plain,
% 4.44/4.66      ((m1_subset_1 @ sk_C @ 
% 4.44/4.66        (k1_zfmisc_1 @ 
% 4.44/4.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 4.44/4.66      inference('demod', [status(thm)], ['6', '11'])).
% 4.44/4.66  thf(redefinition_k7_relset_1, axiom,
% 4.44/4.66    (![A:$i,B:$i,C:$i,D:$i]:
% 4.44/4.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.44/4.66       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 4.44/4.66  thf('13', plain,
% 4.44/4.66      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 4.44/4.66         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 4.44/4.66          | ((k7_relset_1 @ X25 @ X26 @ X24 @ X27) = (k9_relat_1 @ X24 @ X27)))),
% 4.44/4.66      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 4.44/4.66  thf('14', plain,
% 4.44/4.66      (![X0 : $i]:
% 4.44/4.66         ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C @ X0)
% 4.44/4.66           = (k9_relat_1 @ sk_C @ X0))),
% 4.44/4.66      inference('sup-', [status(thm)], ['12', '13'])).
% 4.44/4.66  thf('15', plain,
% 4.44/4.66      (![X41 : $i]:
% 4.44/4.66         (((k2_struct_0 @ X41) = (u1_struct_0 @ X41)) | ~ (l1_struct_0 @ X41))),
% 4.44/4.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.44/4.66  thf('16', plain,
% 4.44/4.66      (![X41 : $i]:
% 4.44/4.66         (((k2_struct_0 @ X41) = (u1_struct_0 @ X41)) | ~ (l1_struct_0 @ X41))),
% 4.44/4.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.44/4.66  thf('17', plain,
% 4.44/4.66      ((m1_subset_1 @ sk_C @ 
% 4.44/4.66        (k1_zfmisc_1 @ 
% 4.44/4.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf(t38_relset_1, axiom,
% 4.44/4.66    (![A:$i,B:$i,C:$i]:
% 4.44/4.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.44/4.66       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 4.44/4.66         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 4.44/4.66  thf('18', plain,
% 4.44/4.66      (![X32 : $i, X33 : $i, X34 : $i]:
% 4.44/4.66         (((k7_relset_1 @ X32 @ X33 @ X34 @ X32)
% 4.44/4.66            = (k2_relset_1 @ X32 @ X33 @ X34))
% 4.44/4.66          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 4.44/4.66      inference('cnf', [status(esa)], [t38_relset_1])).
% 4.44/4.66  thf('19', plain,
% 4.44/4.66      (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 4.44/4.66         (u1_struct_0 @ sk_A))
% 4.44/4.66         = (k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 4.44/4.66      inference('sup-', [status(thm)], ['17', '18'])).
% 4.44/4.66  thf('20', plain,
% 4.44/4.66      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.44/4.66         = (k2_relat_1 @ sk_C))),
% 4.44/4.66      inference('sup-', [status(thm)], ['7', '8'])).
% 4.44/4.66  thf('21', plain,
% 4.44/4.66      (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 4.44/4.66         (u1_struct_0 @ sk_A)) = (k2_relat_1 @ sk_C))),
% 4.44/4.66      inference('demod', [status(thm)], ['19', '20'])).
% 4.44/4.66  thf('22', plain,
% 4.44/4.66      ((m1_subset_1 @ sk_C @ 
% 4.44/4.66        (k1_zfmisc_1 @ 
% 4.44/4.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('23', plain,
% 4.44/4.66      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 4.44/4.66         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 4.44/4.66          | ((k7_relset_1 @ X25 @ X26 @ X24 @ X27) = (k9_relat_1 @ X24 @ X27)))),
% 4.44/4.66      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 4.44/4.66  thf('24', plain,
% 4.44/4.66      (![X0 : $i]:
% 4.44/4.66         ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 4.44/4.66           X0) = (k9_relat_1 @ sk_C @ X0))),
% 4.44/4.66      inference('sup-', [status(thm)], ['22', '23'])).
% 4.44/4.66  thf('25', plain,
% 4.44/4.66      (((k9_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)) = (k2_relat_1 @ sk_C))),
% 4.44/4.66      inference('demod', [status(thm)], ['21', '24'])).
% 4.44/4.66  thf('26', plain,
% 4.44/4.66      ((((k9_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)) = (k2_relat_1 @ sk_C))
% 4.44/4.66        | ~ (l1_struct_0 @ sk_A))),
% 4.44/4.66      inference('sup+', [status(thm)], ['16', '25'])).
% 4.44/4.66  thf('27', plain,
% 4.44/4.66      ((m1_subset_1 @ sk_C @ 
% 4.44/4.66        (k1_zfmisc_1 @ 
% 4.44/4.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf(redefinition_k1_relset_1, axiom,
% 4.44/4.66    (![A:$i,B:$i,C:$i]:
% 4.44/4.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.44/4.66       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 4.44/4.66  thf('28', plain,
% 4.44/4.66      (![X18 : $i, X19 : $i, X20 : $i]:
% 4.44/4.66         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 4.44/4.66          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 4.44/4.66      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.44/4.66  thf('29', plain,
% 4.44/4.66      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.44/4.66         = (k1_relat_1 @ sk_C))),
% 4.44/4.66      inference('sup-', [status(thm)], ['27', '28'])).
% 4.44/4.66  thf('30', plain,
% 4.44/4.66      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.44/4.66         = (k2_struct_0 @ sk_A))),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('31', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 4.44/4.66      inference('sup+', [status(thm)], ['29', '30'])).
% 4.44/4.66  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('33', plain,
% 4.44/4.66      (![X42 : $i]: ((l1_struct_0 @ X42) | ~ (l1_pre_topc @ X42))),
% 4.44/4.66      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 4.44/4.66  thf('34', plain, ((l1_struct_0 @ sk_A)),
% 4.44/4.66      inference('sup-', [status(thm)], ['32', '33'])).
% 4.44/4.66  thf('35', plain,
% 4.44/4.66      (((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 4.44/4.66      inference('demod', [status(thm)], ['26', '31', '34'])).
% 4.44/4.66  thf('36', plain,
% 4.44/4.66      ((m1_subset_1 @ sk_C @ 
% 4.44/4.66        (k1_zfmisc_1 @ 
% 4.44/4.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf(dt_k7_relset_1, axiom,
% 4.44/4.66    (![A:$i,B:$i,C:$i,D:$i]:
% 4.44/4.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.44/4.66       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 4.44/4.66  thf('37', plain,
% 4.44/4.66      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 4.44/4.66         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 4.44/4.66          | (m1_subset_1 @ (k7_relset_1 @ X15 @ X16 @ X14 @ X17) @ 
% 4.44/4.66             (k1_zfmisc_1 @ X16)))),
% 4.44/4.66      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 4.44/4.66  thf('38', plain,
% 4.44/4.66      (![X0 : $i]:
% 4.44/4.66         (m1_subset_1 @ 
% 4.44/4.66          (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 4.44/4.66           X0) @ 
% 4.44/4.66          (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 4.44/4.66      inference('sup-', [status(thm)], ['36', '37'])).
% 4.44/4.66  thf('39', plain,
% 4.44/4.66      (![X0 : $i]:
% 4.44/4.66         ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 4.44/4.66           X0) = (k9_relat_1 @ sk_C @ X0))),
% 4.44/4.66      inference('sup-', [status(thm)], ['22', '23'])).
% 4.44/4.66  thf('40', plain,
% 4.44/4.66      (![X0 : $i]:
% 4.44/4.66         (m1_subset_1 @ (k9_relat_1 @ sk_C @ X0) @ 
% 4.44/4.66          (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 4.44/4.66      inference('demod', [status(thm)], ['38', '39'])).
% 4.44/4.66  thf('41', plain,
% 4.44/4.66      ((m1_subset_1 @ (k2_relat_1 @ sk_C) @ 
% 4.44/4.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 4.44/4.66      inference('sup+', [status(thm)], ['35', '40'])).
% 4.44/4.66  thf(t3_subset, axiom,
% 4.44/4.66    (![A:$i,B:$i]:
% 4.44/4.66     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 4.44/4.66  thf('42', plain,
% 4.44/4.66      (![X3 : $i, X4 : $i]:
% 4.44/4.66         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 4.44/4.66      inference('cnf', [status(esa)], [t3_subset])).
% 4.44/4.66  thf('43', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 4.44/4.66      inference('sup-', [status(thm)], ['41', '42'])).
% 4.44/4.66  thf(d10_xboole_0, axiom,
% 4.44/4.66    (![A:$i,B:$i]:
% 4.44/4.66     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.44/4.66  thf('44', plain,
% 4.44/4.66      (![X0 : $i, X2 : $i]:
% 4.44/4.66         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 4.44/4.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.44/4.66  thf('45', plain,
% 4.44/4.66      ((~ (r1_tarski @ (u1_struct_0 @ sk_B) @ (k2_relat_1 @ sk_C))
% 4.44/4.66        | ((u1_struct_0 @ sk_B) = (k2_relat_1 @ sk_C)))),
% 4.44/4.66      inference('sup-', [status(thm)], ['43', '44'])).
% 4.44/4.66  thf('46', plain,
% 4.44/4.66      ((~ (r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_relat_1 @ sk_C))
% 4.44/4.66        | ~ (l1_struct_0 @ sk_B)
% 4.44/4.66        | ((u1_struct_0 @ sk_B) = (k2_relat_1 @ sk_C)))),
% 4.44/4.66      inference('sup-', [status(thm)], ['15', '45'])).
% 4.44/4.66  thf('47', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.44/4.66      inference('sup+', [status(thm)], ['9', '10'])).
% 4.44/4.66  thf('48', plain,
% 4.44/4.66      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 4.44/4.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.44/4.66  thf('49', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 4.44/4.66      inference('simplify', [status(thm)], ['48'])).
% 4.44/4.66  thf('50', plain, ((l1_struct_0 @ sk_B)),
% 4.44/4.66      inference('sup-', [status(thm)], ['3', '4'])).
% 4.44/4.66  thf('51', plain, (((u1_struct_0 @ sk_B) = (k2_relat_1 @ sk_C))),
% 4.44/4.66      inference('demod', [status(thm)], ['46', '47', '49', '50'])).
% 4.44/4.66  thf(t72_tops_2, axiom,
% 4.44/4.66    (![A:$i]:
% 4.44/4.66     ( ( l1_pre_topc @ A ) =>
% 4.44/4.66       ( ![B:$i]:
% 4.44/4.66         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_pre_topc @ B ) ) =>
% 4.44/4.66           ( ![C:$i]:
% 4.44/4.66             ( ( ( v1_funct_1 @ C ) & 
% 4.44/4.66                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 4.44/4.66                 ( m1_subset_1 @
% 4.44/4.66                   C @ 
% 4.44/4.66                   ( k1_zfmisc_1 @
% 4.44/4.66                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 4.44/4.66               ( ( v3_tops_2 @ C @ A @ B ) <=>
% 4.44/4.66                 ( ( ( k1_relset_1 @
% 4.44/4.66                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 4.44/4.66                     ( k2_struct_0 @ A ) ) & 
% 4.44/4.66                   ( ( k2_relset_1 @
% 4.44/4.66                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 4.44/4.66                     ( k2_struct_0 @ B ) ) & 
% 4.44/4.66                   ( v2_funct_1 @ C ) & 
% 4.44/4.66                   ( ![D:$i]:
% 4.44/4.66                     ( ( m1_subset_1 @
% 4.44/4.66                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.44/4.66                       ( ( v4_pre_topc @ D @ A ) <=>
% 4.44/4.66                         ( v4_pre_topc @
% 4.44/4.66                           ( k7_relset_1 @
% 4.44/4.66                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 4.44/4.66                           B ) ) ) ) ) ) ) ) ) ) ))).
% 4.44/4.66  thf('52', plain,
% 4.44/4.66      (![X43 : $i, X44 : $i, X45 : $i]:
% 4.44/4.66         ((v2_struct_0 @ X43)
% 4.44/4.66          | ~ (l1_pre_topc @ X43)
% 4.44/4.66          | ((k1_relset_1 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X43) @ X45)
% 4.44/4.66              != (k2_struct_0 @ X44))
% 4.44/4.66          | ((k2_relset_1 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X43) @ X45)
% 4.44/4.66              != (k2_struct_0 @ X43))
% 4.44/4.66          | ~ (v2_funct_1 @ X45)
% 4.44/4.66          | ~ (v4_pre_topc @ 
% 4.44/4.66               (k7_relset_1 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X43) @ 
% 4.44/4.66                X45 @ (sk_D_1 @ X45 @ X43 @ X44)) @ 
% 4.44/4.66               X43)
% 4.44/4.66          | ~ (v4_pre_topc @ (sk_D_1 @ X45 @ X43 @ X44) @ X44)
% 4.44/4.66          | (v3_tops_2 @ X45 @ X44 @ X43)
% 4.44/4.66          | ~ (m1_subset_1 @ X45 @ 
% 4.44/4.66               (k1_zfmisc_1 @ 
% 4.44/4.66                (k2_zfmisc_1 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X43))))
% 4.44/4.66          | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X43))
% 4.44/4.66          | ~ (v1_funct_1 @ X45)
% 4.44/4.66          | ~ (l1_pre_topc @ X44))),
% 4.44/4.66      inference('cnf', [status(esa)], [t72_tops_2])).
% 4.44/4.66  thf('53', plain,
% 4.44/4.66      (![X0 : $i, X1 : $i]:
% 4.44/4.66         (~ (v4_pre_topc @ 
% 4.44/4.66             (k7_relset_1 @ (u1_struct_0 @ X0) @ (k2_relat_1 @ sk_C) @ X1 @ 
% 4.44/4.66              (sk_D_1 @ X1 @ sk_B @ X0)) @ 
% 4.44/4.66             sk_B)
% 4.44/4.66          | ~ (l1_pre_topc @ X0)
% 4.44/4.66          | ~ (v1_funct_1 @ X1)
% 4.44/4.66          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 4.44/4.66          | ~ (m1_subset_1 @ X1 @ 
% 4.44/4.66               (k1_zfmisc_1 @ 
% 4.44/4.66                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 4.44/4.66          | (v3_tops_2 @ X1 @ X0 @ sk_B)
% 4.44/4.66          | ~ (v4_pre_topc @ (sk_D_1 @ X1 @ sk_B @ X0) @ X0)
% 4.44/4.66          | ~ (v2_funct_1 @ X1)
% 4.44/4.66          | ((k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1)
% 4.44/4.66              != (k2_struct_0 @ sk_B))
% 4.44/4.66          | ((k1_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1)
% 4.44/4.66              != (k2_struct_0 @ X0))
% 4.44/4.66          | ~ (l1_pre_topc @ sk_B)
% 4.44/4.66          | (v2_struct_0 @ sk_B))),
% 4.44/4.66      inference('sup-', [status(thm)], ['51', '52'])).
% 4.44/4.66  thf('54', plain, (((u1_struct_0 @ sk_B) = (k2_relat_1 @ sk_C))),
% 4.44/4.66      inference('demod', [status(thm)], ['46', '47', '49', '50'])).
% 4.44/4.66  thf('55', plain, (((u1_struct_0 @ sk_B) = (k2_relat_1 @ sk_C))),
% 4.44/4.66      inference('demod', [status(thm)], ['46', '47', '49', '50'])).
% 4.44/4.66  thf('56', plain, (((u1_struct_0 @ sk_B) = (k2_relat_1 @ sk_C))),
% 4.44/4.66      inference('demod', [status(thm)], ['46', '47', '49', '50'])).
% 4.44/4.66  thf('57', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.44/4.66      inference('sup+', [status(thm)], ['9', '10'])).
% 4.44/4.66  thf('58', plain, (((u1_struct_0 @ sk_B) = (k2_relat_1 @ sk_C))),
% 4.44/4.66      inference('demod', [status(thm)], ['46', '47', '49', '50'])).
% 4.44/4.66  thf('59', plain, ((l1_pre_topc @ sk_B)),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('60', plain,
% 4.44/4.66      (![X0 : $i, X1 : $i]:
% 4.44/4.66         (~ (v4_pre_topc @ 
% 4.44/4.66             (k7_relset_1 @ (u1_struct_0 @ X0) @ (k2_relat_1 @ sk_C) @ X1 @ 
% 4.44/4.66              (sk_D_1 @ X1 @ sk_B @ X0)) @ 
% 4.44/4.66             sk_B)
% 4.44/4.66          | ~ (l1_pre_topc @ X0)
% 4.44/4.66          | ~ (v1_funct_1 @ X1)
% 4.44/4.66          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (k2_relat_1 @ sk_C))
% 4.44/4.66          | ~ (m1_subset_1 @ X1 @ 
% 4.44/4.66               (k1_zfmisc_1 @ 
% 4.44/4.66                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (k2_relat_1 @ sk_C))))
% 4.44/4.66          | (v3_tops_2 @ X1 @ X0 @ sk_B)
% 4.44/4.66          | ~ (v4_pre_topc @ (sk_D_1 @ X1 @ sk_B @ X0) @ X0)
% 4.44/4.66          | ~ (v2_funct_1 @ X1)
% 4.44/4.66          | ((k2_relset_1 @ (u1_struct_0 @ X0) @ (k2_relat_1 @ sk_C) @ X1)
% 4.44/4.66              != (k2_relat_1 @ sk_C))
% 4.44/4.66          | ((k1_relset_1 @ (u1_struct_0 @ X0) @ (k2_relat_1 @ sk_C) @ X1)
% 4.44/4.66              != (k2_struct_0 @ X0))
% 4.44/4.66          | (v2_struct_0 @ sk_B))),
% 4.44/4.66      inference('demod', [status(thm)],
% 4.44/4.66                ['53', '54', '55', '56', '57', '58', '59'])).
% 4.44/4.66  thf('61', plain,
% 4.44/4.66      ((~ (v4_pre_topc @ (k9_relat_1 @ sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A)) @ 
% 4.44/4.66           sk_B)
% 4.44/4.66        | (v2_struct_0 @ sk_B)
% 4.44/4.66        | ((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.44/4.66            != (k2_struct_0 @ sk_A))
% 4.44/4.66        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.44/4.66            != (k2_relat_1 @ sk_C))
% 4.44/4.66        | ~ (v2_funct_1 @ sk_C)
% 4.44/4.66        | ~ (v4_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 4.44/4.66        | (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 4.44/4.66        | ~ (m1_subset_1 @ sk_C @ 
% 4.44/4.66             (k1_zfmisc_1 @ 
% 4.44/4.66              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))
% 4.44/4.66        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 4.44/4.66        | ~ (v1_funct_1 @ sk_C)
% 4.44/4.66        | ~ (l1_pre_topc @ sk_A))),
% 4.44/4.66      inference('sup-', [status(thm)], ['14', '60'])).
% 4.44/4.66  thf('62', plain,
% 4.44/4.66      ((m1_subset_1 @ sk_C @ 
% 4.44/4.66        (k1_zfmisc_1 @ 
% 4.44/4.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 4.44/4.66      inference('demod', [status(thm)], ['2', '5'])).
% 4.44/4.66  thf('63', plain,
% 4.44/4.66      (![X18 : $i, X19 : $i, X20 : $i]:
% 4.44/4.66         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 4.44/4.66          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 4.44/4.66      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.44/4.66  thf('64', plain,
% 4.44/4.66      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 4.44/4.66         = (k1_relat_1 @ sk_C))),
% 4.44/4.66      inference('sup-', [status(thm)], ['62', '63'])).
% 4.44/4.66  thf('65', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.44/4.66      inference('sup+', [status(thm)], ['9', '10'])).
% 4.44/4.66  thf('66', plain,
% 4.44/4.66      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.44/4.66         = (k1_relat_1 @ sk_C))),
% 4.44/4.66      inference('demod', [status(thm)], ['64', '65'])).
% 4.44/4.66  thf('67', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 4.44/4.66      inference('sup+', [status(thm)], ['29', '30'])).
% 4.44/4.66  thf('68', plain,
% 4.44/4.66      (![X41 : $i]:
% 4.44/4.66         (((k2_struct_0 @ X41) = (u1_struct_0 @ X41)) | ~ (l1_struct_0 @ X41))),
% 4.44/4.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.44/4.66  thf('69', plain,
% 4.44/4.66      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.44/4.66         = (k2_struct_0 @ sk_B))),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('70', plain,
% 4.44/4.66      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 4.44/4.66          = (k2_struct_0 @ sk_B))
% 4.44/4.66        | ~ (l1_struct_0 @ sk_B))),
% 4.44/4.66      inference('sup+', [status(thm)], ['68', '69'])).
% 4.44/4.66  thf('71', plain, ((l1_struct_0 @ sk_B)),
% 4.44/4.66      inference('sup-', [status(thm)], ['3', '4'])).
% 4.44/4.66  thf('72', plain,
% 4.44/4.66      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 4.44/4.66         = (k2_struct_0 @ sk_B))),
% 4.44/4.66      inference('demod', [status(thm)], ['70', '71'])).
% 4.44/4.66  thf('73', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.44/4.66      inference('sup+', [status(thm)], ['9', '10'])).
% 4.44/4.66  thf('74', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.44/4.66      inference('sup+', [status(thm)], ['9', '10'])).
% 4.44/4.66  thf('75', plain,
% 4.44/4.66      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.44/4.66         = (k2_relat_1 @ sk_C))),
% 4.44/4.66      inference('demod', [status(thm)], ['72', '73', '74'])).
% 4.44/4.66  thf('76', plain, ((v2_funct_1 @ sk_C)),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('77', plain,
% 4.44/4.66      ((m1_subset_1 @ sk_C @ 
% 4.44/4.66        (k1_zfmisc_1 @ 
% 4.44/4.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 4.44/4.66      inference('demod', [status(thm)], ['6', '11'])).
% 4.44/4.66  thf('78', plain,
% 4.44/4.66      (![X41 : $i]:
% 4.44/4.66         (((k2_struct_0 @ X41) = (u1_struct_0 @ X41)) | ~ (l1_struct_0 @ X41))),
% 4.44/4.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.44/4.66  thf('79', plain,
% 4.44/4.66      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('80', plain,
% 4.44/4.66      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 4.44/4.66        | ~ (l1_struct_0 @ sk_B))),
% 4.44/4.66      inference('sup+', [status(thm)], ['78', '79'])).
% 4.44/4.66  thf('81', plain, ((l1_struct_0 @ sk_B)),
% 4.44/4.66      inference('sup-', [status(thm)], ['3', '4'])).
% 4.44/4.66  thf('82', plain,
% 4.44/4.66      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 4.44/4.66      inference('demod', [status(thm)], ['80', '81'])).
% 4.44/4.66  thf('83', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.44/4.66      inference('sup+', [status(thm)], ['9', '10'])).
% 4.44/4.66  thf('84', plain,
% 4.44/4.66      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 4.44/4.66      inference('demod', [status(thm)], ['82', '83'])).
% 4.44/4.66  thf('85', plain, ((v1_funct_1 @ sk_C)),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('87', plain,
% 4.44/4.66      ((~ (v4_pre_topc @ (k9_relat_1 @ sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A)) @ 
% 4.44/4.66           sk_B)
% 4.44/4.66        | (v2_struct_0 @ sk_B)
% 4.44/4.66        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 4.44/4.66        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 4.44/4.66        | ~ (v4_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 4.44/4.66        | (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 4.44/4.66      inference('demod', [status(thm)],
% 4.44/4.66                ['61', '66', '67', '75', '76', '77', '84', '85', '86'])).
% 4.44/4.66  thf('88', plain,
% 4.44/4.66      (((v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 4.44/4.66        | ~ (v4_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 4.44/4.66        | (v2_struct_0 @ sk_B)
% 4.44/4.66        | ~ (v4_pre_topc @ 
% 4.44/4.66             (k9_relat_1 @ sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A)) @ sk_B))),
% 4.44/4.66      inference('simplify', [status(thm)], ['87'])).
% 4.44/4.66  thf('89', plain,
% 4.44/4.66      ((m1_subset_1 @ sk_C @ 
% 4.44/4.66        (k1_zfmisc_1 @ 
% 4.44/4.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 4.44/4.66      inference('demod', [status(thm)], ['6', '11'])).
% 4.44/4.66  thf('90', plain, (((u1_struct_0 @ sk_B) = (k2_relat_1 @ sk_C))),
% 4.44/4.66      inference('demod', [status(thm)], ['46', '47', '49', '50'])).
% 4.44/4.66  thf('91', plain,
% 4.44/4.66      (![X43 : $i, X44 : $i, X45 : $i]:
% 4.44/4.66         ((v2_struct_0 @ X43)
% 4.44/4.66          | ~ (l1_pre_topc @ X43)
% 4.44/4.66          | ((k1_relset_1 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X43) @ X45)
% 4.44/4.66              != (k2_struct_0 @ X44))
% 4.44/4.66          | ((k2_relset_1 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X43) @ X45)
% 4.44/4.66              != (k2_struct_0 @ X43))
% 4.44/4.66          | ~ (v2_funct_1 @ X45)
% 4.44/4.66          | (v4_pre_topc @ 
% 4.44/4.66             (k7_relset_1 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X43) @ X45 @ 
% 4.44/4.66              (sk_D_1 @ X45 @ X43 @ X44)) @ 
% 4.44/4.66             X43)
% 4.44/4.66          | (v4_pre_topc @ (sk_D_1 @ X45 @ X43 @ X44) @ X44)
% 4.44/4.66          | (v3_tops_2 @ X45 @ X44 @ X43)
% 4.44/4.66          | ~ (m1_subset_1 @ X45 @ 
% 4.44/4.66               (k1_zfmisc_1 @ 
% 4.44/4.66                (k2_zfmisc_1 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X43))))
% 4.44/4.66          | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X43))
% 4.44/4.66          | ~ (v1_funct_1 @ X45)
% 4.44/4.66          | ~ (l1_pre_topc @ X44))),
% 4.44/4.66      inference('cnf', [status(esa)], [t72_tops_2])).
% 4.44/4.66  thf('92', plain,
% 4.44/4.66      (![X0 : $i, X1 : $i]:
% 4.44/4.66         (~ (m1_subset_1 @ X1 @ 
% 4.44/4.66             (k1_zfmisc_1 @ 
% 4.44/4.66              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (k2_relat_1 @ sk_C))))
% 4.44/4.66          | ~ (l1_pre_topc @ X0)
% 4.44/4.66          | ~ (v1_funct_1 @ X1)
% 4.44/4.66          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 4.44/4.66          | (v3_tops_2 @ X1 @ X0 @ sk_B)
% 4.44/4.66          | (v4_pre_topc @ (sk_D_1 @ X1 @ sk_B @ X0) @ X0)
% 4.44/4.66          | (v4_pre_topc @ 
% 4.44/4.66             (k7_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1 @ 
% 4.44/4.66              (sk_D_1 @ X1 @ sk_B @ X0)) @ 
% 4.44/4.66             sk_B)
% 4.44/4.66          | ~ (v2_funct_1 @ X1)
% 4.44/4.66          | ((k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1)
% 4.44/4.66              != (k2_struct_0 @ sk_B))
% 4.44/4.66          | ((k1_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1)
% 4.44/4.66              != (k2_struct_0 @ X0))
% 4.44/4.66          | ~ (l1_pre_topc @ sk_B)
% 4.44/4.66          | (v2_struct_0 @ sk_B))),
% 4.44/4.66      inference('sup-', [status(thm)], ['90', '91'])).
% 4.44/4.66  thf('93', plain, (((u1_struct_0 @ sk_B) = (k2_relat_1 @ sk_C))),
% 4.44/4.66      inference('demod', [status(thm)], ['46', '47', '49', '50'])).
% 4.44/4.66  thf('94', plain, (((u1_struct_0 @ sk_B) = (k2_relat_1 @ sk_C))),
% 4.44/4.66      inference('demod', [status(thm)], ['46', '47', '49', '50'])).
% 4.44/4.66  thf('95', plain, (((u1_struct_0 @ sk_B) = (k2_relat_1 @ sk_C))),
% 4.44/4.66      inference('demod', [status(thm)], ['46', '47', '49', '50'])).
% 4.44/4.66  thf('96', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.44/4.66      inference('sup+', [status(thm)], ['9', '10'])).
% 4.44/4.66  thf('97', plain, (((u1_struct_0 @ sk_B) = (k2_relat_1 @ sk_C))),
% 4.44/4.66      inference('demod', [status(thm)], ['46', '47', '49', '50'])).
% 4.44/4.66  thf('98', plain, ((l1_pre_topc @ sk_B)),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('99', plain,
% 4.44/4.66      (![X0 : $i, X1 : $i]:
% 4.44/4.66         (~ (m1_subset_1 @ X1 @ 
% 4.44/4.66             (k1_zfmisc_1 @ 
% 4.44/4.66              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (k2_relat_1 @ sk_C))))
% 4.44/4.66          | ~ (l1_pre_topc @ X0)
% 4.44/4.66          | ~ (v1_funct_1 @ X1)
% 4.44/4.66          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (k2_relat_1 @ sk_C))
% 4.44/4.66          | (v3_tops_2 @ X1 @ X0 @ sk_B)
% 4.44/4.66          | (v4_pre_topc @ (sk_D_1 @ X1 @ sk_B @ X0) @ X0)
% 4.44/4.66          | (v4_pre_topc @ 
% 4.44/4.66             (k7_relset_1 @ (u1_struct_0 @ X0) @ (k2_relat_1 @ sk_C) @ X1 @ 
% 4.44/4.66              (sk_D_1 @ X1 @ sk_B @ X0)) @ 
% 4.44/4.66             sk_B)
% 4.44/4.66          | ~ (v2_funct_1 @ X1)
% 4.44/4.66          | ((k2_relset_1 @ (u1_struct_0 @ X0) @ (k2_relat_1 @ sk_C) @ X1)
% 4.44/4.66              != (k2_relat_1 @ sk_C))
% 4.44/4.66          | ((k1_relset_1 @ (u1_struct_0 @ X0) @ (k2_relat_1 @ sk_C) @ X1)
% 4.44/4.66              != (k2_struct_0 @ X0))
% 4.44/4.66          | (v2_struct_0 @ sk_B))),
% 4.44/4.66      inference('demod', [status(thm)],
% 4.44/4.66                ['92', '93', '94', '95', '96', '97', '98'])).
% 4.44/4.66  thf('100', plain,
% 4.44/4.66      (((v2_struct_0 @ sk_B)
% 4.44/4.66        | ((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.44/4.66            != (k2_struct_0 @ sk_A))
% 4.44/4.66        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.44/4.66            != (k2_relat_1 @ sk_C))
% 4.44/4.66        | ~ (v2_funct_1 @ sk_C)
% 4.44/4.66        | (v4_pre_topc @ 
% 4.44/4.66           (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C @ 
% 4.44/4.66            (sk_D_1 @ sk_C @ sk_B @ sk_A)) @ 
% 4.44/4.66           sk_B)
% 4.44/4.66        | (v4_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 4.44/4.66        | (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 4.44/4.66        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 4.44/4.66        | ~ (v1_funct_1 @ sk_C)
% 4.44/4.66        | ~ (l1_pre_topc @ sk_A))),
% 4.44/4.66      inference('sup-', [status(thm)], ['89', '99'])).
% 4.44/4.66  thf('101', plain,
% 4.44/4.66      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.44/4.66         = (k1_relat_1 @ sk_C))),
% 4.44/4.66      inference('demod', [status(thm)], ['64', '65'])).
% 4.44/4.66  thf('102', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 4.44/4.66      inference('sup+', [status(thm)], ['29', '30'])).
% 4.44/4.66  thf('103', plain,
% 4.44/4.66      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.44/4.66         = (k2_relat_1 @ sk_C))),
% 4.44/4.66      inference('demod', [status(thm)], ['72', '73', '74'])).
% 4.44/4.66  thf('104', plain, ((v2_funct_1 @ sk_C)),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('105', plain,
% 4.44/4.66      (![X0 : $i]:
% 4.44/4.66         ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C @ X0)
% 4.44/4.66           = (k9_relat_1 @ sk_C @ X0))),
% 4.44/4.66      inference('sup-', [status(thm)], ['12', '13'])).
% 4.44/4.66  thf('106', plain,
% 4.44/4.66      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 4.44/4.66      inference('demod', [status(thm)], ['82', '83'])).
% 4.44/4.66  thf('107', plain, ((v1_funct_1 @ sk_C)),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('108', plain, ((l1_pre_topc @ sk_A)),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('109', plain,
% 4.44/4.66      (((v2_struct_0 @ sk_B)
% 4.44/4.66        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 4.44/4.66        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 4.44/4.66        | (v4_pre_topc @ (k9_relat_1 @ sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A)) @ 
% 4.44/4.66           sk_B)
% 4.44/4.66        | (v4_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 4.44/4.66        | (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 4.44/4.66      inference('demod', [status(thm)],
% 4.44/4.66                ['100', '101', '102', '103', '104', '105', '106', '107', '108'])).
% 4.44/4.66  thf('110', plain,
% 4.44/4.66      (((v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 4.44/4.66        | (v4_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 4.44/4.66        | (v4_pre_topc @ (k9_relat_1 @ sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A)) @ 
% 4.44/4.66           sk_B)
% 4.44/4.66        | (v2_struct_0 @ sk_B))),
% 4.44/4.66      inference('simplify', [status(thm)], ['109'])).
% 4.44/4.66  thf('111', plain,
% 4.44/4.66      (![X41 : $i]:
% 4.44/4.66         (((k2_struct_0 @ X41) = (u1_struct_0 @ X41)) | ~ (l1_struct_0 @ X41))),
% 4.44/4.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.44/4.66  thf('112', plain,
% 4.44/4.66      (![X0 : $i]:
% 4.44/4.66         (m1_subset_1 @ (k9_relat_1 @ sk_C @ X0) @ 
% 4.44/4.66          (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 4.44/4.66      inference('demod', [status(thm)], ['38', '39'])).
% 4.44/4.66  thf('113', plain,
% 4.44/4.66      (![X0 : $i]:
% 4.44/4.66         ((m1_subset_1 @ (k9_relat_1 @ sk_C @ X0) @ 
% 4.44/4.66           (k1_zfmisc_1 @ (k2_struct_0 @ sk_B)))
% 4.44/4.66          | ~ (l1_struct_0 @ sk_B))),
% 4.44/4.66      inference('sup+', [status(thm)], ['111', '112'])).
% 4.44/4.66  thf('114', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.44/4.66      inference('sup+', [status(thm)], ['9', '10'])).
% 4.44/4.66  thf('115', plain, ((l1_struct_0 @ sk_B)),
% 4.44/4.66      inference('sup-', [status(thm)], ['3', '4'])).
% 4.44/4.66  thf('116', plain,
% 4.44/4.66      (![X0 : $i]:
% 4.44/4.66         (m1_subset_1 @ (k9_relat_1 @ sk_C @ X0) @ 
% 4.44/4.66          (k1_zfmisc_1 @ (k2_relat_1 @ sk_C)))),
% 4.44/4.66      inference('demod', [status(thm)], ['113', '114', '115'])).
% 4.44/4.66  thf('117', plain,
% 4.44/4.66      (![X41 : $i]:
% 4.44/4.66         (((k2_struct_0 @ X41) = (u1_struct_0 @ X41)) | ~ (l1_struct_0 @ X41))),
% 4.44/4.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.44/4.66  thf('118', plain,
% 4.44/4.66      ((m1_subset_1 @ sk_C @ 
% 4.44/4.66        (k1_zfmisc_1 @ 
% 4.44/4.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf(d12_pre_topc, axiom,
% 4.44/4.66    (![A:$i]:
% 4.44/4.66     ( ( l1_pre_topc @ A ) =>
% 4.44/4.66       ( ![B:$i]:
% 4.44/4.66         ( ( l1_pre_topc @ B ) =>
% 4.44/4.66           ( ![C:$i]:
% 4.44/4.66             ( ( ( v1_funct_1 @ C ) & 
% 4.44/4.66                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 4.44/4.66                 ( m1_subset_1 @
% 4.44/4.66                   C @ 
% 4.44/4.66                   ( k1_zfmisc_1 @
% 4.44/4.66                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 4.44/4.66               ( ( v5_pre_topc @ C @ A @ B ) <=>
% 4.44/4.66                 ( ![D:$i]:
% 4.44/4.66                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 4.44/4.66                     ( ( v4_pre_topc @ D @ B ) =>
% 4.44/4.66                       ( v4_pre_topc @
% 4.44/4.66                         ( k8_relset_1 @
% 4.44/4.66                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 4.44/4.66                         A ) ) ) ) ) ) ) ) ) ))).
% 4.44/4.66  thf('119', plain,
% 4.44/4.66      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 4.44/4.66         (~ (l1_pre_topc @ X37)
% 4.44/4.66          | ~ (v5_pre_topc @ X38 @ X39 @ X37)
% 4.44/4.66          | ~ (v4_pre_topc @ X40 @ X37)
% 4.44/4.66          | (v4_pre_topc @ 
% 4.44/4.66             (k8_relset_1 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X37) @ X38 @ 
% 4.44/4.66              X40) @ 
% 4.44/4.66             X39)
% 4.44/4.66          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 4.44/4.66          | ~ (m1_subset_1 @ X38 @ 
% 4.44/4.66               (k1_zfmisc_1 @ 
% 4.44/4.66                (k2_zfmisc_1 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X37))))
% 4.44/4.66          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X37))
% 4.44/4.66          | ~ (v1_funct_1 @ X38)
% 4.44/4.66          | ~ (l1_pre_topc @ X39))),
% 4.44/4.66      inference('cnf', [status(esa)], [d12_pre_topc])).
% 4.44/4.66  thf('120', plain,
% 4.44/4.66      (![X0 : $i]:
% 4.44/4.66         (~ (l1_pre_topc @ sk_A)
% 4.44/4.66          | ~ (v1_funct_1 @ sk_C)
% 4.44/4.66          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 4.44/4.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 4.44/4.66          | (v4_pre_topc @ 
% 4.44/4.66             (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 4.44/4.66              sk_C @ X0) @ 
% 4.44/4.66             sk_A)
% 4.44/4.66          | ~ (v4_pre_topc @ X0 @ sk_B)
% 4.44/4.66          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 4.44/4.66          | ~ (l1_pre_topc @ sk_B))),
% 4.44/4.66      inference('sup-', [status(thm)], ['118', '119'])).
% 4.44/4.66  thf('121', plain, ((l1_pre_topc @ sk_A)),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('122', plain, ((v1_funct_1 @ sk_C)),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('123', plain,
% 4.44/4.66      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('124', plain,
% 4.44/4.66      ((m1_subset_1 @ sk_C @ 
% 4.44/4.66        (k1_zfmisc_1 @ 
% 4.44/4.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf(redefinition_k8_relset_1, axiom,
% 4.44/4.66    (![A:$i,B:$i,C:$i,D:$i]:
% 4.44/4.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.44/4.66       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 4.44/4.66  thf('125', plain,
% 4.44/4.66      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 4.44/4.66         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 4.44/4.66          | ((k8_relset_1 @ X29 @ X30 @ X28 @ X31) = (k10_relat_1 @ X28 @ X31)))),
% 4.44/4.66      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 4.44/4.66  thf('126', plain,
% 4.44/4.66      (![X0 : $i]:
% 4.44/4.66         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 4.44/4.66           X0) = (k10_relat_1 @ sk_C @ X0))),
% 4.44/4.66      inference('sup-', [status(thm)], ['124', '125'])).
% 4.44/4.66  thf('127', plain, ((v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('128', plain, ((l1_pre_topc @ sk_B)),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('129', plain,
% 4.44/4.66      (![X0 : $i]:
% 4.44/4.66         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 4.44/4.66          | (v4_pre_topc @ (k10_relat_1 @ sk_C @ X0) @ sk_A)
% 4.44/4.66          | ~ (v4_pre_topc @ X0 @ sk_B))),
% 4.44/4.66      inference('demod', [status(thm)],
% 4.44/4.66                ['120', '121', '122', '123', '126', '127', '128'])).
% 4.44/4.66  thf('130', plain,
% 4.44/4.66      (![X0 : $i]:
% 4.44/4.66         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_B)))
% 4.44/4.66          | ~ (l1_struct_0 @ sk_B)
% 4.44/4.66          | ~ (v4_pre_topc @ X0 @ sk_B)
% 4.44/4.66          | (v4_pre_topc @ (k10_relat_1 @ sk_C @ X0) @ sk_A))),
% 4.44/4.66      inference('sup-', [status(thm)], ['117', '129'])).
% 4.44/4.66  thf('131', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.44/4.66      inference('sup+', [status(thm)], ['9', '10'])).
% 4.44/4.66  thf('132', plain, ((l1_struct_0 @ sk_B)),
% 4.44/4.66      inference('sup-', [status(thm)], ['3', '4'])).
% 4.44/4.66  thf('133', plain,
% 4.44/4.66      (![X0 : $i]:
% 4.44/4.66         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_relat_1 @ sk_C)))
% 4.44/4.66          | ~ (v4_pre_topc @ X0 @ sk_B)
% 4.44/4.66          | (v4_pre_topc @ (k10_relat_1 @ sk_C @ X0) @ sk_A))),
% 4.44/4.66      inference('demod', [status(thm)], ['130', '131', '132'])).
% 4.44/4.66  thf('134', plain,
% 4.44/4.66      (![X0 : $i]:
% 4.44/4.66         ((v4_pre_topc @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)) @ sk_A)
% 4.44/4.66          | ~ (v4_pre_topc @ (k9_relat_1 @ sk_C @ X0) @ sk_B))),
% 4.44/4.66      inference('sup-', [status(thm)], ['116', '133'])).
% 4.44/4.66  thf('135', plain,
% 4.44/4.66      (((v2_struct_0 @ sk_B)
% 4.44/4.66        | (v4_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 4.44/4.66        | (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 4.44/4.66        | (v4_pre_topc @ 
% 4.44/4.66           (k10_relat_1 @ sk_C @ 
% 4.44/4.66            (k9_relat_1 @ sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A))) @ 
% 4.44/4.66           sk_A))),
% 4.44/4.66      inference('sup-', [status(thm)], ['110', '134'])).
% 4.44/4.66  thf('136', plain,
% 4.44/4.66      (![X41 : $i]:
% 4.44/4.66         (((k2_struct_0 @ X41) = (u1_struct_0 @ X41)) | ~ (l1_struct_0 @ X41))),
% 4.44/4.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.44/4.66  thf('137', plain,
% 4.44/4.66      ((m1_subset_1 @ sk_C @ 
% 4.44/4.66        (k1_zfmisc_1 @ 
% 4.44/4.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 4.44/4.66      inference('demod', [status(thm)], ['6', '11'])).
% 4.44/4.66  thf('138', plain, (((u1_struct_0 @ sk_B) = (k2_relat_1 @ sk_C))),
% 4.44/4.66      inference('demod', [status(thm)], ['46', '47', '49', '50'])).
% 4.44/4.66  thf('139', plain,
% 4.44/4.66      (![X43 : $i, X44 : $i, X45 : $i]:
% 4.44/4.66         ((v2_struct_0 @ X43)
% 4.44/4.66          | ~ (l1_pre_topc @ X43)
% 4.44/4.66          | ((k1_relset_1 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X43) @ X45)
% 4.44/4.66              != (k2_struct_0 @ X44))
% 4.44/4.66          | ((k2_relset_1 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X43) @ X45)
% 4.44/4.66              != (k2_struct_0 @ X43))
% 4.44/4.66          | ~ (v2_funct_1 @ X45)
% 4.44/4.66          | (m1_subset_1 @ (sk_D_1 @ X45 @ X43 @ X44) @ 
% 4.44/4.66             (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 4.44/4.66          | (v3_tops_2 @ X45 @ X44 @ X43)
% 4.44/4.66          | ~ (m1_subset_1 @ X45 @ 
% 4.44/4.66               (k1_zfmisc_1 @ 
% 4.44/4.66                (k2_zfmisc_1 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X43))))
% 4.44/4.66          | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X43))
% 4.44/4.66          | ~ (v1_funct_1 @ X45)
% 4.44/4.66          | ~ (l1_pre_topc @ X44))),
% 4.44/4.66      inference('cnf', [status(esa)], [t72_tops_2])).
% 4.44/4.66  thf('140', plain,
% 4.44/4.66      (![X0 : $i, X1 : $i]:
% 4.44/4.66         (~ (m1_subset_1 @ X1 @ 
% 4.44/4.66             (k1_zfmisc_1 @ 
% 4.44/4.66              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (k2_relat_1 @ sk_C))))
% 4.44/4.66          | ~ (l1_pre_topc @ X0)
% 4.44/4.66          | ~ (v1_funct_1 @ X1)
% 4.44/4.66          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 4.44/4.66          | (v3_tops_2 @ X1 @ X0 @ sk_B)
% 4.44/4.66          | (m1_subset_1 @ (sk_D_1 @ X1 @ sk_B @ X0) @ 
% 4.44/4.66             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 4.44/4.66          | ~ (v2_funct_1 @ X1)
% 4.44/4.66          | ((k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1)
% 4.44/4.66              != (k2_struct_0 @ sk_B))
% 4.44/4.66          | ((k1_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1)
% 4.44/4.66              != (k2_struct_0 @ X0))
% 4.44/4.66          | ~ (l1_pre_topc @ sk_B)
% 4.44/4.66          | (v2_struct_0 @ sk_B))),
% 4.44/4.66      inference('sup-', [status(thm)], ['138', '139'])).
% 4.44/4.66  thf('141', plain, (((u1_struct_0 @ sk_B) = (k2_relat_1 @ sk_C))),
% 4.44/4.66      inference('demod', [status(thm)], ['46', '47', '49', '50'])).
% 4.44/4.66  thf('142', plain, (((u1_struct_0 @ sk_B) = (k2_relat_1 @ sk_C))),
% 4.44/4.66      inference('demod', [status(thm)], ['46', '47', '49', '50'])).
% 4.44/4.66  thf('143', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.44/4.66      inference('sup+', [status(thm)], ['9', '10'])).
% 4.44/4.66  thf('144', plain, (((u1_struct_0 @ sk_B) = (k2_relat_1 @ sk_C))),
% 4.44/4.66      inference('demod', [status(thm)], ['46', '47', '49', '50'])).
% 4.44/4.66  thf('145', plain, ((l1_pre_topc @ sk_B)),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('146', plain,
% 4.44/4.66      (![X0 : $i, X1 : $i]:
% 4.44/4.66         (~ (m1_subset_1 @ X1 @ 
% 4.44/4.66             (k1_zfmisc_1 @ 
% 4.44/4.66              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (k2_relat_1 @ sk_C))))
% 4.44/4.66          | ~ (l1_pre_topc @ X0)
% 4.44/4.66          | ~ (v1_funct_1 @ X1)
% 4.44/4.66          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (k2_relat_1 @ sk_C))
% 4.44/4.66          | (v3_tops_2 @ X1 @ X0 @ sk_B)
% 4.44/4.66          | (m1_subset_1 @ (sk_D_1 @ X1 @ sk_B @ X0) @ 
% 4.44/4.66             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 4.44/4.66          | ~ (v2_funct_1 @ X1)
% 4.44/4.66          | ((k2_relset_1 @ (u1_struct_0 @ X0) @ (k2_relat_1 @ sk_C) @ X1)
% 4.44/4.66              != (k2_relat_1 @ sk_C))
% 4.44/4.66          | ((k1_relset_1 @ (u1_struct_0 @ X0) @ (k2_relat_1 @ sk_C) @ X1)
% 4.44/4.66              != (k2_struct_0 @ X0))
% 4.44/4.66          | (v2_struct_0 @ sk_B))),
% 4.44/4.66      inference('demod', [status(thm)],
% 4.44/4.66                ['140', '141', '142', '143', '144', '145'])).
% 4.44/4.66  thf('147', plain,
% 4.44/4.66      (((v2_struct_0 @ sk_B)
% 4.44/4.66        | ((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.44/4.66            != (k2_struct_0 @ sk_A))
% 4.44/4.66        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.44/4.66            != (k2_relat_1 @ sk_C))
% 4.44/4.66        | ~ (v2_funct_1 @ sk_C)
% 4.44/4.66        | (m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ 
% 4.44/4.66           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.44/4.66        | (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 4.44/4.66        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 4.44/4.66        | ~ (v1_funct_1 @ sk_C)
% 4.44/4.66        | ~ (l1_pre_topc @ sk_A))),
% 4.44/4.66      inference('sup-', [status(thm)], ['137', '146'])).
% 4.44/4.66  thf('148', plain,
% 4.44/4.66      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.44/4.66         = (k1_relat_1 @ sk_C))),
% 4.44/4.66      inference('demod', [status(thm)], ['64', '65'])).
% 4.44/4.66  thf('149', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 4.44/4.66      inference('sup+', [status(thm)], ['29', '30'])).
% 4.44/4.66  thf('150', plain,
% 4.44/4.66      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.44/4.66         = (k2_relat_1 @ sk_C))),
% 4.44/4.66      inference('demod', [status(thm)], ['72', '73', '74'])).
% 4.44/4.66  thf('151', plain, ((v2_funct_1 @ sk_C)),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('152', plain,
% 4.44/4.66      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 4.44/4.66      inference('demod', [status(thm)], ['82', '83'])).
% 4.44/4.66  thf('153', plain, ((v1_funct_1 @ sk_C)),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('154', plain, ((l1_pre_topc @ sk_A)),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('155', plain,
% 4.44/4.66      (((v2_struct_0 @ sk_B)
% 4.44/4.66        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 4.44/4.66        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 4.44/4.66        | (m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ 
% 4.44/4.66           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.44/4.66        | (v3_tops_2 @ sk_C @ sk_A @ sk_B))),
% 4.44/4.66      inference('demod', [status(thm)],
% 4.44/4.66                ['147', '148', '149', '150', '151', '152', '153', '154'])).
% 4.44/4.66  thf('156', plain,
% 4.44/4.66      (((v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 4.44/4.66        | (m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ 
% 4.44/4.66           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.44/4.66        | (v2_struct_0 @ sk_B))),
% 4.44/4.66      inference('simplify', [status(thm)], ['155'])).
% 4.44/4.66  thf('157', plain, (~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('158', plain,
% 4.44/4.66      (((v2_struct_0 @ sk_B)
% 4.44/4.66        | (m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ 
% 4.44/4.66           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 4.44/4.66      inference('clc', [status(thm)], ['156', '157'])).
% 4.44/4.66  thf('159', plain, (~ (v2_struct_0 @ sk_B)),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('160', plain,
% 4.44/4.66      ((m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ 
% 4.44/4.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.44/4.66      inference('clc', [status(thm)], ['158', '159'])).
% 4.44/4.66  thf('161', plain,
% 4.44/4.66      (![X3 : $i, X4 : $i]:
% 4.44/4.66         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 4.44/4.66      inference('cnf', [status(esa)], [t3_subset])).
% 4.44/4.66  thf('162', plain,
% 4.44/4.66      ((r1_tarski @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 4.44/4.66      inference('sup-', [status(thm)], ['160', '161'])).
% 4.44/4.66  thf('163', plain,
% 4.44/4.66      (((r1_tarski @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ (k2_struct_0 @ sk_A))
% 4.44/4.66        | ~ (l1_struct_0 @ sk_A))),
% 4.44/4.66      inference('sup+', [status(thm)], ['136', '162'])).
% 4.44/4.66  thf('164', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 4.44/4.66      inference('sup+', [status(thm)], ['29', '30'])).
% 4.44/4.66  thf('165', plain, ((l1_struct_0 @ sk_A)),
% 4.44/4.66      inference('sup-', [status(thm)], ['32', '33'])).
% 4.44/4.66  thf('166', plain,
% 4.44/4.66      ((r1_tarski @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ (k1_relat_1 @ sk_C))),
% 4.44/4.66      inference('demod', [status(thm)], ['163', '164', '165'])).
% 4.44/4.66  thf(t164_funct_1, axiom,
% 4.44/4.66    (![A:$i,B:$i]:
% 4.44/4.66     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 4.44/4.66       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 4.44/4.66         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 4.44/4.66  thf('167', plain,
% 4.44/4.66      (![X6 : $i, X7 : $i]:
% 4.44/4.66         (~ (r1_tarski @ X6 @ (k1_relat_1 @ X7))
% 4.44/4.66          | ~ (v2_funct_1 @ X7)
% 4.44/4.66          | ((k10_relat_1 @ X7 @ (k9_relat_1 @ X7 @ X6)) = (X6))
% 4.44/4.66          | ~ (v1_funct_1 @ X7)
% 4.44/4.66          | ~ (v1_relat_1 @ X7))),
% 4.44/4.66      inference('cnf', [status(esa)], [t164_funct_1])).
% 4.44/4.66  thf('168', plain,
% 4.44/4.66      ((~ (v1_relat_1 @ sk_C)
% 4.44/4.66        | ~ (v1_funct_1 @ sk_C)
% 4.44/4.66        | ((k10_relat_1 @ sk_C @ 
% 4.44/4.66            (k9_relat_1 @ sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A)))
% 4.44/4.66            = (sk_D_1 @ sk_C @ sk_B @ sk_A))
% 4.44/4.66        | ~ (v2_funct_1 @ sk_C))),
% 4.44/4.66      inference('sup-', [status(thm)], ['166', '167'])).
% 4.44/4.66  thf('169', plain,
% 4.44/4.66      ((m1_subset_1 @ sk_C @ 
% 4.44/4.66        (k1_zfmisc_1 @ 
% 4.44/4.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf(cc1_relset_1, axiom,
% 4.44/4.66    (![A:$i,B:$i,C:$i]:
% 4.44/4.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.44/4.66       ( v1_relat_1 @ C ) ))).
% 4.44/4.66  thf('170', plain,
% 4.44/4.66      (![X8 : $i, X9 : $i, X10 : $i]:
% 4.44/4.66         ((v1_relat_1 @ X8)
% 4.44/4.66          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 4.44/4.66      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.44/4.66  thf('171', plain, ((v1_relat_1 @ sk_C)),
% 4.44/4.66      inference('sup-', [status(thm)], ['169', '170'])).
% 4.44/4.66  thf('172', plain, ((v1_funct_1 @ sk_C)),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('173', plain, ((v2_funct_1 @ sk_C)),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('174', plain,
% 4.44/4.66      (((k10_relat_1 @ sk_C @ 
% 4.44/4.66         (k9_relat_1 @ sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A)))
% 4.44/4.66         = (sk_D_1 @ sk_C @ sk_B @ sk_A))),
% 4.44/4.66      inference('demod', [status(thm)], ['168', '171', '172', '173'])).
% 4.44/4.66  thf('175', plain,
% 4.44/4.66      (((v2_struct_0 @ sk_B)
% 4.44/4.66        | (v4_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 4.44/4.66        | (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 4.44/4.66        | (v4_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A))),
% 4.44/4.66      inference('demod', [status(thm)], ['135', '174'])).
% 4.44/4.66  thf('176', plain,
% 4.44/4.66      (((v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 4.44/4.66        | (v4_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 4.44/4.66        | (v2_struct_0 @ sk_B))),
% 4.44/4.66      inference('simplify', [status(thm)], ['175'])).
% 4.44/4.66  thf('177', plain, (~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('178', plain,
% 4.44/4.66      (((v2_struct_0 @ sk_B)
% 4.44/4.66        | (v4_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A))),
% 4.44/4.66      inference('clc', [status(thm)], ['176', '177'])).
% 4.44/4.66  thf('179', plain, (~ (v2_struct_0 @ sk_B)),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('180', plain, ((v4_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A)),
% 4.44/4.66      inference('clc', [status(thm)], ['178', '179'])).
% 4.44/4.66  thf('181', plain,
% 4.44/4.66      (((v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 4.44/4.66        | (v2_struct_0 @ sk_B)
% 4.44/4.66        | ~ (v4_pre_topc @ 
% 4.44/4.66             (k9_relat_1 @ sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A)) @ sk_B))),
% 4.44/4.66      inference('demod', [status(thm)], ['88', '180'])).
% 4.44/4.66  thf('182', plain, (~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('183', plain,
% 4.44/4.66      ((~ (v4_pre_topc @ (k9_relat_1 @ sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A)) @ 
% 4.44/4.66           sk_B)
% 4.44/4.66        | (v2_struct_0 @ sk_B))),
% 4.44/4.66      inference('clc', [status(thm)], ['181', '182'])).
% 4.44/4.66  thf('184', plain, (~ (v2_struct_0 @ sk_B)),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('185', plain,
% 4.44/4.66      (~ (v4_pre_topc @ (k9_relat_1 @ sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A)) @ 
% 4.44/4.66          sk_B)),
% 4.44/4.66      inference('clc', [status(thm)], ['183', '184'])).
% 4.44/4.66  thf('186', plain,
% 4.44/4.66      ((m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ 
% 4.44/4.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.44/4.66      inference('clc', [status(thm)], ['158', '159'])).
% 4.44/4.66  thf('187', plain,
% 4.44/4.66      ((m1_subset_1 @ sk_C @ 
% 4.44/4.66        (k1_zfmisc_1 @ 
% 4.44/4.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 4.44/4.66      inference('demod', [status(thm)], ['6', '11'])).
% 4.44/4.66  thf('188', plain, (((u1_struct_0 @ sk_B) = (k2_relat_1 @ sk_C))),
% 4.44/4.66      inference('demod', [status(thm)], ['46', '47', '49', '50'])).
% 4.44/4.66  thf(t25_compts_1, axiom,
% 4.44/4.66    (![A:$i]:
% 4.44/4.66     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.44/4.66       ( ![B:$i]:
% 4.44/4.66         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 4.44/4.66             ( l1_pre_topc @ B ) ) =>
% 4.44/4.66           ( ![C:$i]:
% 4.44/4.66             ( ( ( v1_funct_1 @ C ) & 
% 4.44/4.66                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 4.44/4.66                 ( m1_subset_1 @
% 4.44/4.66                   C @ 
% 4.44/4.66                   ( k1_zfmisc_1 @
% 4.44/4.66                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 4.44/4.66               ( ( ( v1_compts_1 @ A ) & ( v8_pre_topc @ B ) & 
% 4.44/4.66                   ( ( k2_relset_1 @
% 4.44/4.66                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 4.44/4.66                     ( k2_struct_0 @ B ) ) & 
% 4.44/4.66                   ( v5_pre_topc @ C @ A @ B ) ) =>
% 4.44/4.66                 ( ![D:$i]:
% 4.44/4.66                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.44/4.66                     ( ( v4_pre_topc @ D @ A ) =>
% 4.44/4.66                       ( v4_pre_topc @
% 4.44/4.66                         ( k7_relset_1 @
% 4.44/4.66                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 4.44/4.66                         B ) ) ) ) ) ) ) ) ) ))).
% 4.44/4.66  thf('189', plain,
% 4.44/4.66      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 4.44/4.66         ((v2_struct_0 @ X47)
% 4.44/4.66          | ~ (v2_pre_topc @ X47)
% 4.44/4.66          | ~ (l1_pre_topc @ X47)
% 4.44/4.66          | ~ (v1_compts_1 @ X48)
% 4.44/4.66          | ~ (v8_pre_topc @ X47)
% 4.44/4.66          | ((k2_relset_1 @ (u1_struct_0 @ X48) @ (u1_struct_0 @ X47) @ X49)
% 4.44/4.66              != (k2_struct_0 @ X47))
% 4.44/4.66          | ~ (v5_pre_topc @ X49 @ X48 @ X47)
% 4.44/4.66          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 4.44/4.66          | (v4_pre_topc @ 
% 4.44/4.66             (k7_relset_1 @ (u1_struct_0 @ X48) @ (u1_struct_0 @ X47) @ X49 @ 
% 4.44/4.66              X50) @ 
% 4.44/4.66             X47)
% 4.44/4.66          | ~ (v4_pre_topc @ X50 @ X48)
% 4.44/4.66          | ~ (m1_subset_1 @ X49 @ 
% 4.44/4.66               (k1_zfmisc_1 @ 
% 4.44/4.66                (k2_zfmisc_1 @ (u1_struct_0 @ X48) @ (u1_struct_0 @ X47))))
% 4.44/4.66          | ~ (v1_funct_2 @ X49 @ (u1_struct_0 @ X48) @ (u1_struct_0 @ X47))
% 4.44/4.66          | ~ (v1_funct_1 @ X49)
% 4.44/4.66          | ~ (l1_pre_topc @ X48)
% 4.44/4.66          | ~ (v2_pre_topc @ X48))),
% 4.44/4.66      inference('cnf', [status(esa)], [t25_compts_1])).
% 4.44/4.66  thf('190', plain,
% 4.44/4.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.44/4.66         (~ (m1_subset_1 @ X1 @ 
% 4.44/4.66             (k1_zfmisc_1 @ 
% 4.44/4.66              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (k2_relat_1 @ sk_C))))
% 4.44/4.66          | ~ (v2_pre_topc @ X0)
% 4.44/4.66          | ~ (l1_pre_topc @ X0)
% 4.44/4.66          | ~ (v1_funct_1 @ X1)
% 4.44/4.66          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 4.44/4.66          | ~ (v4_pre_topc @ X2 @ X0)
% 4.44/4.66          | (v4_pre_topc @ 
% 4.44/4.66             (k7_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1 @ X2) @ 
% 4.44/4.66             sk_B)
% 4.44/4.66          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 4.44/4.66          | ~ (v5_pre_topc @ X1 @ X0 @ sk_B)
% 4.44/4.66          | ((k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1)
% 4.44/4.66              != (k2_struct_0 @ sk_B))
% 4.44/4.66          | ~ (v8_pre_topc @ sk_B)
% 4.44/4.66          | ~ (v1_compts_1 @ X0)
% 4.44/4.66          | ~ (l1_pre_topc @ sk_B)
% 4.44/4.66          | ~ (v2_pre_topc @ sk_B)
% 4.44/4.66          | (v2_struct_0 @ sk_B))),
% 4.44/4.66      inference('sup-', [status(thm)], ['188', '189'])).
% 4.44/4.66  thf('191', plain, (((u1_struct_0 @ sk_B) = (k2_relat_1 @ sk_C))),
% 4.44/4.66      inference('demod', [status(thm)], ['46', '47', '49', '50'])).
% 4.44/4.66  thf('192', plain, (((u1_struct_0 @ sk_B) = (k2_relat_1 @ sk_C))),
% 4.44/4.66      inference('demod', [status(thm)], ['46', '47', '49', '50'])).
% 4.44/4.66  thf('193', plain, (((u1_struct_0 @ sk_B) = (k2_relat_1 @ sk_C))),
% 4.44/4.66      inference('demod', [status(thm)], ['46', '47', '49', '50'])).
% 4.44/4.66  thf('194', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.44/4.66      inference('sup+', [status(thm)], ['9', '10'])).
% 4.44/4.66  thf('195', plain, ((v8_pre_topc @ sk_B)),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('196', plain, ((l1_pre_topc @ sk_B)),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('197', plain, ((v2_pre_topc @ sk_B)),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('198', plain,
% 4.44/4.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.44/4.66         (~ (m1_subset_1 @ X1 @ 
% 4.44/4.66             (k1_zfmisc_1 @ 
% 4.44/4.66              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (k2_relat_1 @ sk_C))))
% 4.44/4.66          | ~ (v2_pre_topc @ X0)
% 4.44/4.66          | ~ (l1_pre_topc @ X0)
% 4.44/4.66          | ~ (v1_funct_1 @ X1)
% 4.44/4.66          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (k2_relat_1 @ sk_C))
% 4.44/4.66          | ~ (v4_pre_topc @ X2 @ X0)
% 4.44/4.66          | (v4_pre_topc @ 
% 4.44/4.66             (k7_relset_1 @ (u1_struct_0 @ X0) @ (k2_relat_1 @ sk_C) @ X1 @ X2) @ 
% 4.44/4.66             sk_B)
% 4.44/4.66          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 4.44/4.66          | ~ (v5_pre_topc @ X1 @ X0 @ sk_B)
% 4.44/4.66          | ((k2_relset_1 @ (u1_struct_0 @ X0) @ (k2_relat_1 @ sk_C) @ X1)
% 4.44/4.66              != (k2_relat_1 @ sk_C))
% 4.44/4.66          | ~ (v1_compts_1 @ X0)
% 4.44/4.66          | (v2_struct_0 @ sk_B))),
% 4.44/4.66      inference('demod', [status(thm)],
% 4.44/4.66                ['190', '191', '192', '193', '194', '195', '196', '197'])).
% 4.44/4.66  thf('199', plain,
% 4.44/4.66      (![X0 : $i]:
% 4.44/4.66         ((v2_struct_0 @ sk_B)
% 4.44/4.66          | ~ (v1_compts_1 @ sk_A)
% 4.44/4.66          | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.44/4.66              != (k2_relat_1 @ sk_C))
% 4.44/4.66          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 4.44/4.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.44/4.66          | (v4_pre_topc @ 
% 4.44/4.66             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ 
% 4.44/4.66              sk_C @ X0) @ 
% 4.44/4.66             sk_B)
% 4.44/4.66          | ~ (v4_pre_topc @ X0 @ sk_A)
% 4.44/4.66          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 4.44/4.66          | ~ (v1_funct_1 @ sk_C)
% 4.44/4.66          | ~ (l1_pre_topc @ sk_A)
% 4.44/4.66          | ~ (v2_pre_topc @ sk_A))),
% 4.44/4.66      inference('sup-', [status(thm)], ['187', '198'])).
% 4.44/4.66  thf('200', plain, ((v1_compts_1 @ sk_A)),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('201', plain,
% 4.44/4.66      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.44/4.66         = (k2_relat_1 @ sk_C))),
% 4.44/4.66      inference('demod', [status(thm)], ['72', '73', '74'])).
% 4.44/4.66  thf('202', plain, ((v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('203', plain,
% 4.44/4.66      (![X0 : $i]:
% 4.44/4.66         ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C @ X0)
% 4.44/4.66           = (k9_relat_1 @ sk_C @ X0))),
% 4.44/4.66      inference('sup-', [status(thm)], ['12', '13'])).
% 4.44/4.66  thf('204', plain,
% 4.44/4.66      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 4.44/4.66      inference('demod', [status(thm)], ['82', '83'])).
% 4.44/4.66  thf('205', plain, ((v1_funct_1 @ sk_C)),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('206', plain, ((l1_pre_topc @ sk_A)),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('207', plain, ((v2_pre_topc @ sk_A)),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('208', plain,
% 4.44/4.66      (![X0 : $i]:
% 4.44/4.66         ((v2_struct_0 @ sk_B)
% 4.44/4.66          | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 4.44/4.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.44/4.66          | (v4_pre_topc @ (k9_relat_1 @ sk_C @ X0) @ sk_B)
% 4.44/4.66          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 4.44/4.66      inference('demod', [status(thm)],
% 4.44/4.66                ['199', '200', '201', '202', '203', '204', '205', '206', '207'])).
% 4.44/4.66  thf('209', plain,
% 4.44/4.66      (![X0 : $i]:
% 4.44/4.66         (~ (v4_pre_topc @ X0 @ sk_A)
% 4.44/4.66          | (v4_pre_topc @ (k9_relat_1 @ sk_C @ X0) @ sk_B)
% 4.44/4.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.44/4.66          | (v2_struct_0 @ sk_B))),
% 4.44/4.66      inference('simplify', [status(thm)], ['208'])).
% 4.44/4.66  thf('210', plain,
% 4.44/4.66      (((v2_struct_0 @ sk_B)
% 4.44/4.66        | (v4_pre_topc @ (k9_relat_1 @ sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A)) @ 
% 4.44/4.66           sk_B)
% 4.44/4.66        | ~ (v4_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A))),
% 4.44/4.66      inference('sup-', [status(thm)], ['186', '209'])).
% 4.44/4.66  thf('211', plain, ((v4_pre_topc @ (sk_D_1 @ sk_C @ sk_B @ sk_A) @ sk_A)),
% 4.44/4.66      inference('clc', [status(thm)], ['178', '179'])).
% 4.44/4.66  thf('212', plain,
% 4.44/4.66      (((v2_struct_0 @ sk_B)
% 4.44/4.66        | (v4_pre_topc @ (k9_relat_1 @ sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A)) @ 
% 4.44/4.66           sk_B))),
% 4.44/4.66      inference('demod', [status(thm)], ['210', '211'])).
% 4.44/4.66  thf('213', plain, (~ (v2_struct_0 @ sk_B)),
% 4.44/4.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.44/4.66  thf('214', plain,
% 4.44/4.66      ((v4_pre_topc @ (k9_relat_1 @ sk_C @ (sk_D_1 @ sk_C @ sk_B @ sk_A)) @ 
% 4.44/4.66        sk_B)),
% 4.44/4.66      inference('clc', [status(thm)], ['212', '213'])).
% 4.44/4.66  thf('215', plain, ($false), inference('demod', [status(thm)], ['185', '214'])).
% 4.44/4.66  
% 4.44/4.66  % SZS output end Refutation
% 4.44/4.66  
% 4.49/4.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
