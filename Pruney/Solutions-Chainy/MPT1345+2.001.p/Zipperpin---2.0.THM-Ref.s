%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LyTAr8y8Fg

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:28 EST 2020

% Result     : Theorem 3.71s
% Output     : Refutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :  517 (675749 expanded)
%              Number of leaves         :   39 (207597 expanded)
%              Depth                    :   48
%              Number of atoms          : 5635 (12871198 expanded)
%              Number of equality atoms :  297 (195204 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v3_tops_2_type,type,(
    v3_tops_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t70_tops_2,conjecture,(
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
               => ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( l1_pre_topc @ B ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( ( v3_tops_2 @ C @ A @ B )
                 => ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t70_tops_2])).

thf('2',plain,(
    ~ ( v3_tops_2 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v3_tops_2 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('5',plain,(
    ! [X23: $i] :
      ( ( l1_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('6',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ~ ( v3_tops_2 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,
    ( ~ ( v3_tops_2 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X23: $i] :
      ( ( l1_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('11',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v3_tops_2 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
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
                  & ( v5_pre_topc @ C @ A @ B )
                  & ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ B @ A ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( v3_tops_2 @ X28 @ X29 @ X27 )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) @ X28 )
        = ( k2_struct_0 @ X29 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( v1_funct_2 @ X28 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('20',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('21',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16','17','18','21','22','23'])).

thf('25',plain,(
    ~ ( v3_tops_2 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['12','24'])).

thf('26',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('27',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['9','10'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(d4_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( k2_tops_2 @ A @ B @ C )
          = ( k2_funct_1 @ C ) ) ) ) )).

thf('32',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X24 @ X26 )
       != X24 )
      | ~ ( v2_funct_1 @ X26 )
      | ( ( k2_tops_2 @ X25 @ X24 @ X26 )
        = ( k2_funct_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X25 @ X24 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('33',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('36',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['9','10'])).

thf('39',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34','39'])).

thf('41',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','40'])).

thf('42',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('43',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16','17','18','21','22','23'])).

thf('45',plain,
    ( ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('48',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v4_relat_1 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('49',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('50',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v4_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k1_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('53',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('54',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['51','54'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('56',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('57',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['46','57'])).

thf('59',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('60',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16','17','18','21','22','23'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('63',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61','63'])).

thf('65',plain,
    ( ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['45','64'])).

thf('66',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('67',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('70',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16','17','18','21','22','23'])).

thf('72',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61','63'])).

thf('74',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( v3_tops_2 @ X28 @ X29 @ X27 )
      | ( v2_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( v1_funct_2 @ X28 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_funct_1 @ X1 )
      | ~ ( v3_tops_2 @ X1 @ sk_A @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61','63'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_funct_1 @ X1 )
      | ~ ( v3_tops_2 @ X1 @ sk_A @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['72','78'])).

thf('80',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('83',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('86',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16','17','18','21','22','23'])).

thf('88',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['79','80','81','88','89'])).

thf('91',plain,
    ( ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['65','90'])).

thf('92',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('93',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('94',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61','63'])).

thf('95',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( v3_tops_2 @ X28 @ X29 @ X27 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) @ X28 )
        = ( k2_struct_0 @ X27 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( v1_funct_2 @ X28 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) @ X1 )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( v3_tops_2 @ X1 @ sk_A @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61','63'])).

thf('99',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61','63'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ X1 )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( v3_tops_2 @ X1 @ sk_A @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['96','97','98','99'])).

thf('101',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['93','100'])).

thf('102',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('105',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['101','102','103','104','105'])).

thf('107',plain,
    ( ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['92','106'])).

thf('108',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['9','10'])).

thf('109',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['91','109'])).

thf('111',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ~ ( v3_tops_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['25','111'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('113',plain,(
    ! [X8: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('114',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('115',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('116',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['9','10'])).

thf('118',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf(t31_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf('119',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k2_relset_1 @ X21 @ X20 @ X19 )
       != X20 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X19 @ X21 @ X20 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('120',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('123',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('124',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['9','10'])).

thf('126',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['120','121','126'])).

thf('128',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16','17','18','21','22','23'])).

thf('129',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16','17','18','21','22','23'])).

thf('130',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('131',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['79','80','81','88','89'])).

thf('132',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('134',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X24 @ X26 )
       != X24 )
      | ~ ( v2_funct_1 @ X26 )
      | ( ( k2_tops_2 @ X25 @ X24 @ X26 )
        = ( k2_funct_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X25 @ X24 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('137',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('139',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('140',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k2_relset_1 @ X21 @ X20 @ X19 )
       != X20 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X19 @ X21 @ X20 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('141',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('144',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('145',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16','17','18','21','22','23'])).

thf('146',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['79','80','81','88','89'])).

thf('148',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['101','102','103','104','105'])).

thf('150',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['138','150'])).

thf('152',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['9','10'])).

thf('153',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('156',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k2_relset_1 @ X21 @ X20 @ X19 )
       != X20 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X19 ) @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X19 @ X21 @ X20 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('157',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('160',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['157','158','159'])).

thf('161',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16','17','18','21','22','23'])).

thf('162',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16','17','18','21','22','23'])).

thf('163',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['160','161','162'])).

thf('164',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['79','80','81','88','89'])).

thf('165',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('167',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['137','154','168'])).

thf('170',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('171',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16','17','18','21','22','23'])).

thf('172',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['170','171'])).

thf('173',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('174',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('175',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('176',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k2_relset_1 @ X21 @ X20 @ X19 )
       != X20 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X19 @ X21 @ X20 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('178',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['178','179','180'])).

thf('182',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( v2_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['175','181'])).

thf('183',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('184',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['182','183'])).

thf('185',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16','17','18','21','22','23'])).

thf('186',plain,
    ( ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['184','185'])).

thf('187',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61','63'])).

thf('188',plain,
    ( ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['79','80','81','88','89'])).

thf('190',plain,
    ( ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['101','102','103','104','105'])).

thf('192',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['190','191'])).

thf('193',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['174','192'])).

thf('194',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['9','10'])).

thf('195',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['193','194'])).

thf('196',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['195'])).

thf('197',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v4_relat_1 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('198',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v4_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k1_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('200',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('202',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('203',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['200','203'])).

thf('205',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('206',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ sk_B )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['173','206'])).

thf('208',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['9','10'])).

thf('209',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['207','208'])).

thf('210',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('211',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61','63'])).

thf(t62_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_struct_0 @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v2_funct_1 @ C ) )
               => ( ( ( k1_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                    = ( k2_struct_0 @ B ) )
                  & ( ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                    = ( k2_struct_0 @ A ) ) ) ) ) ) ) )).

thf('212',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( l1_struct_0 @ X30 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X30 ) @ X32 )
       != ( k2_struct_0 @ X30 ) )
      | ~ ( v2_funct_1 @ X32 )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X31 ) @ ( k2_tops_2 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X30 ) @ X32 ) )
        = ( k2_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_2])).

thf('213',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) @ X1 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) @ X1 )
       != ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('215',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61','63'])).

thf('216',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61','63'])).

thf('217',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61','63'])).

thf('218',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61','63'])).

thf('219',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ X1 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ X1 )
       != ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['213','214','215','216','217','218'])).

thf('220',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['210','219'])).

thf('221',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['9','10'])).

thf('222',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['101','102','103','104','105'])).

thf('223',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['79','80','81','88','89'])).

thf('224',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('225',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('226',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X24 @ X26 )
       != X24 )
      | ~ ( v2_funct_1 @ X26 )
      | ( ( k2_tops_2 @ X25 @ X24 @ X26 )
        = ( k2_funct_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X25 @ X24 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('228',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['226','227'])).

thf('229',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['228','229','230'])).

thf('232',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['225','231'])).

thf('233',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('234',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['232','233'])).

thf('235',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16','17','18','21','22','23'])).

thf('236',plain,
    ( ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['234','235'])).

thf('237',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61','63'])).

thf('238',plain,
    ( ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['236','237'])).

thf('239',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['79','80','81','88','89'])).

thf('240',plain,
    ( ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['238','239'])).

thf('241',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['101','102','103','104','105'])).

thf('242',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['240','241'])).

thf('243',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['224','242'])).

thf('244',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['9','10'])).

thf('245',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['243','244'])).

thf('246',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['245'])).

thf('247',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['195'])).

thf('248',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('249',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['247','248'])).

thf('250',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('251',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['220','221','222','223','246','249','250','251'])).

thf('253',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['252'])).

thf('254',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['253','254'])).

thf('256',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['62'])).

thf('257',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['253','254'])).

thf('258',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['209','255','256','257'])).

thf('259',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61','63'])).

thf('260',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( l1_struct_0 @ X30 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X30 ) @ X32 )
       != ( k2_struct_0 @ X30 ) )
      | ~ ( v2_funct_1 @ X32 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X31 ) @ ( k2_tops_2 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X30 ) @ X32 ) )
        = ( k2_struct_0 @ X31 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X30 ) ) ) )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_2])).

thf('261',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) @ X1 ) )
        = ( k2_struct_0 @ sk_A ) )
      | ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) @ X1 )
       != ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['259','260'])).

thf('262',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('263',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61','63'])).

thf('264',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61','63'])).

thf('265',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61','63'])).

thf('266',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16','17','18','21','22','23'])).

thf('267',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61','63'])).

thf('268',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ X1 ) )
        = ( k1_relat_1 @ sk_C ) )
      | ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ X1 )
       != ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['261','262','263','264','265','266','267'])).

thf('269',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_B )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ X0 )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ X0 ) )
        = ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['258','268'])).

thf('270',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['9','10'])).

thf('271',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['209','255','256','257'])).

thf('272',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['209','255','256','257'])).

thf('273',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['209','255','256','257'])).

thf('274',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['209','255','256','257'])).

thf('275',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ X0 )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ X0 ) )
        = ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['269','270','271','272','273','274'])).

thf('276',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['172','275'])).

thf('277',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('278',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('279',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16','17','18','21','22','23'])).

thf('280',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['278','279'])).

thf('281',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['110'])).

thf('282',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['79','80','81','88','89'])).

thf('283',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('284',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['276','277','280','281','282','283'])).

thf('285',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['284'])).

thf('286',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('287',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['285','286'])).

thf('288',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['169','287'])).

thf('289',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['288'])).

thf('290',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['113','289'])).

thf('291',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['52','53'])).

thf('292',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('293',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['79','80','81','88','89'])).

thf('294',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['290','291','292','293'])).

thf('295',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['209','255','256','257'])).

thf('296',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61','63'])).

thf('297',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) @ X28 )
       != ( k2_struct_0 @ X29 ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) @ X28 )
       != ( k2_struct_0 @ X27 ) )
      | ~ ( v2_funct_1 @ X28 )
      | ~ ( v5_pre_topc @ X28 @ X29 @ X27 )
      | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) @ X28 ) @ X27 @ X29 )
      | ( v3_tops_2 @ X28 @ X29 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( v1_funct_2 @ X28 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('298',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( k1_relat_1 @ sk_C ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v3_tops_2 @ X1 @ X0 @ sk_A )
      | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ X1 ) @ sk_A @ X0 )
      | ~ ( v5_pre_topc @ X1 @ X0 @ sk_A )
      | ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ X1 )
       != ( k2_struct_0 @ sk_A ) )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ X1 )
       != ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['296','297'])).

thf('299',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61','63'])).

thf('300',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61','63'])).

thf('301',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61','63'])).

thf('302',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16','17','18','21','22','23'])).

thf('303',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61','63'])).

thf('304',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('305',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( k1_relat_1 @ sk_C ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( k1_relat_1 @ sk_C ) )
      | ( v3_tops_2 @ X1 @ X0 @ sk_A )
      | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ X0 ) @ ( k1_relat_1 @ sk_C ) @ X1 ) @ sk_A @ X0 )
      | ~ ( v5_pre_topc @ X1 @ X0 @ sk_A )
      | ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_relat_1 @ sk_C ) @ X1 )
       != ( k1_relat_1 @ sk_C ) )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_relat_1 @ sk_C ) @ X1 )
       != ( k2_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['298','299','300','301','302','303','304'])).

thf('306',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
      | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ X0 )
       != ( k2_struct_0 @ sk_B ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ X0 )
       != ( k1_relat_1 @ sk_C ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v5_pre_topc @ X0 @ sk_B @ sk_A )
      | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ X0 ) @ sk_A @ sk_B )
      | ( v3_tops_2 @ X0 @ sk_B @ sk_A )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['295','305'])).

thf('307',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['209','255','256','257'])).

thf('308',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['209','255','256','257'])).

thf('309',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['209','255','256','257'])).

thf('310',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['209','255','256','257'])).

thf('311',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('312',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
      | ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ X0 )
       != ( k2_struct_0 @ sk_B ) )
      | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ X0 )
       != ( k1_relat_1 @ sk_C ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v5_pre_topc @ X0 @ sk_B @ sk_A )
      | ~ ( v5_pre_topc @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ X0 ) @ sk_A @ sk_B )
      | ( v3_tops_2 @ X0 @ sk_B @ sk_A )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['306','307','308','309','310','311'])).

thf('313',plain,
    ( ~ ( v5_pre_topc @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( v3_tops_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v5_pre_topc @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['294','312'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('314',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X9 ) )
        = X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('315',plain,(
    ! [X8: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('316',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('317',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k2_relset_1 @ X21 @ X20 @ X19 )
       != X20 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X19 @ X21 @ X20 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('318',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['316','317'])).

thf('319',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['153'])).

thf('320',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['167'])).

thf('321',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['318','319','320'])).

thf('322',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['285','286'])).

thf('323',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['321','322'])).

thf('324',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['323'])).

thf('325',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['315','324'])).

thf('326',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['52','53'])).

thf('327',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('328',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['79','80','81','88','89'])).

thf('329',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['325','326','327','328'])).

thf('330',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61','63'])).

thf('331',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('332',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( v3_tops_2 @ X28 @ X29 @ X27 )
      | ( v5_pre_topc @ X28 @ X29 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( v1_funct_2 @ X28 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('333',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( v5_pre_topc @ X2 @ X1 @ X0 )
      | ~ ( v3_tops_2 @ X2 @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['331','332'])).

thf('334',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tops_2 @ X1 @ sk_A @ X0 )
      | ( v5_pre_topc @ X1 @ sk_A @ X0 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['330','333'])).

thf('335',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61','63'])).

thf('336',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('337',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tops_2 @ X1 @ sk_A @ X0 )
      | ( v5_pre_topc @ X1 @ sk_A @ X0 )
      | ~ ( v1_funct_2 @ X1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['334','335','336'])).

thf('338',plain,
    ( ~ ( l1_struct_0 @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A @ sk_B )
    | ~ ( v3_tops_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['329','337'])).

thf('339',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['9','10'])).

thf('340',plain,(
    ! [X8: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('341',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('342',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k2_relset_1 @ X21 @ X20 @ X19 )
       != X20 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X19 @ X21 @ X20 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('343',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['341','342'])).

thf('344',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['153'])).

thf('345',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['167'])).

thf('346',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['343','344','345'])).

thf('347',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['285','286'])).

thf('348',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['346','347'])).

thf('349',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['348'])).

thf('350',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['340','349'])).

thf('351',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['52','53'])).

thf('352',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('353',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['79','80','81','88','89'])).

thf('354',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['350','351','352','353'])).

thf('355',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['209','255','256','257'])).

thf('356',plain,(
    ! [X8: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('357',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('358',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k2_relset_1 @ X21 @ X20 @ X19 )
       != X20 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X19 ) @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X19 @ X21 @ X20 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('359',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['357','358'])).

thf('360',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['153'])).

thf('361',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['167'])).

thf('362',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['359','360','361'])).

thf('363',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['285','286'])).

thf('364',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['362','363'])).

thf('365',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['364'])).

thf('366',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['356','365'])).

thf('367',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['52','53'])).

thf('368',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('369',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['79','80','81','88','89'])).

thf('370',plain,(
    v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['366','367','368','369'])).

thf('371',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('372',plain,
    ( ( v5_pre_topc @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A @ sk_B )
    | ~ ( v3_tops_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['338','339','354','355','370','371'])).

thf('373',plain,
    ( ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v5_pre_topc @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['314','372'])).

thf('374',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('375',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['52','53'])).

thf('376',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('377',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['79','80','81','88','89'])).

thf('378',plain,(
    v5_pre_topc @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['373','374','375','376','377'])).

thf('379',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['153'])).

thf('380',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['167'])).

thf('381',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('382',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61','63'])).

thf('383',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( v3_tops_2 @ X28 @ X29 @ X27 )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) @ X28 ) @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( v1_funct_2 @ X28 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('384',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 @ sk_A )
      | ~ ( v3_tops_2 @ X1 @ sk_A @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['382','383'])).

thf('385',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('386',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61','63'])).

thf('387',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61','63'])).

thf('388',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ( v5_pre_topc @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 @ sk_A )
      | ~ ( v3_tops_2 @ X1 @ sk_A @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['384','385','386','387'])).

thf('389',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ( v5_pre_topc @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['381','388'])).

thf('390',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('391',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('392',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['245'])).

thf('393',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('394',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('395',plain,(
    v5_pre_topc @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['389','390','391','392','393','394'])).

thf('396',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X9 ) )
        = X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('397',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['325','326','327','328'])).

thf('398',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X24 @ X26 )
       != X24 )
      | ~ ( v2_funct_1 @ X26 )
      | ( ( k2_tops_2 @ X25 @ X24 @ X26 )
        = ( k2_funct_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X25 @ X24 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('399',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['397','398'])).

thf('400',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['350','351','352','353'])).

thf('401',plain,(
    v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['366','367','368','369'])).

thf('402',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['399','400','401'])).

thf('403',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X9 ) )
        = X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('404',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['325','326','327','328'])).

thf('405',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61','63'])).

thf('406',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('407',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( v3_tops_2 @ X28 @ X29 @ X27 )
      | ( v2_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( v1_funct_2 @ X28 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('408',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_funct_1 @ X2 )
      | ~ ( v3_tops_2 @ X2 @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['406','407'])).

thf('409',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tops_2 @ X1 @ sk_A @ X0 )
      | ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['405','408'])).

thf('410',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61','63'])).

thf('411',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('412',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tops_2 @ X1 @ sk_A @ X0 )
      | ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['409','410','411'])).

thf('413',plain,
    ( ~ ( l1_struct_0 @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v3_tops_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['404','412'])).

thf('414',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['9','10'])).

thf('415',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['350','351','352','353'])).

thf('416',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['209','255','256','257'])).

thf('417',plain,(
    v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['366','367','368','369'])).

thf('418',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('419',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v3_tops_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['413','414','415','416','417','418'])).

thf('420',plain,
    ( ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['403','419'])).

thf('421',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('422',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['52','53'])).

thf('423',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('424',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['79','80','81','88','89'])).

thf('425',plain,(
    v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['420','421','422','423','424'])).

thf('426',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X9 ) )
        = X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('427',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['325','326','327','328'])).

thf('428',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61','63'])).

thf('429',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('430',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( v3_tops_2 @ X28 @ X29 @ X27 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) @ X28 )
        = ( k2_struct_0 @ X27 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( v1_funct_2 @ X28 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_2])).

thf('431',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ X2 )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( v3_tops_2 @ X2 @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['429','430'])).

thf('432',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tops_2 @ X1 @ sk_A @ X0 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) @ X1 )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['428','431'])).

thf('433',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61','63'])).

thf('434',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61','63'])).

thf('435',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('436',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tops_2 @ X1 @ sk_A @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ X1 )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ X1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['432','433','434','435'])).

thf('437',plain,
    ( ~ ( l1_struct_0 @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( v3_tops_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['427','436'])).

thf('438',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['9','10'])).

thf('439',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['350','351','352','353'])).

thf('440',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['209','255','256','257'])).

thf('441',plain,(
    v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['366','367','368','369'])).

thf('442',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['209','255','256','257'])).

thf('443',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('444',plain,
    ( ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( v3_tops_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['437','438','439','440','441','442','443'])).

thf('445',plain,
    ( ~ ( v3_tops_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['426','444'])).

thf('446',plain,(
    v3_tops_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('447',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['52','53'])).

thf('448',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('449',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['79','80','81','88','89'])).

thf('450',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['445','446','447','448','449'])).

thf('451',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['402','425','450'])).

thf('452',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['451'])).

thf('453',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['396','452'])).

thf('454',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['110'])).

thf('455',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['52','53'])).

thf('456',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('457',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['79','80','81','88','89'])).

thf('458',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['453','454','455','456','457'])).

thf('459',plain,(
    ! [X8: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('460',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['458','459'])).

thf('461',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['325','326','327','328'])).

thf('462',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('463',plain,(
    v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['461','462'])).

thf('464',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['350','351','352','353'])).

thf('465',plain,(
    v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['420','421','422','423','424'])).

thf('466',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['460','463','464','465'])).

thf('467',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['285','286'])).

thf('468',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('469',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('470',plain,
    ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['468','469'])).

thf('471',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['253','254'])).

thf('472',plain,
    ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['470','471'])).

thf('473',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('474',plain,
    ( ( v3_tops_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['313','378','379','380','395','466','467','472','473'])).

thf('475',plain,(
    v3_tops_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['474'])).

thf('476',plain,(
    $false ),
    inference(demod,[status(thm)],['112','475'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LyTAr8y8Fg
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:19:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 3.71/3.89  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.71/3.89  % Solved by: fo/fo7.sh
% 3.71/3.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.71/3.89  % done 3783 iterations in 3.438s
% 3.71/3.89  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.71/3.89  % SZS output start Refutation
% 3.71/3.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.71/3.89  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.71/3.89  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 3.71/3.89  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.71/3.89  thf(sk_C_type, type, sk_C: $i).
% 3.71/3.89  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 3.71/3.89  thf(sk_B_type, type, sk_B: $i).
% 3.71/3.89  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 3.71/3.89  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.71/3.89  thf(sk_A_type, type, sk_A: $i).
% 3.71/3.89  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.71/3.89  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 3.71/3.89  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.71/3.89  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.71/3.89  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.71/3.89  thf(v3_tops_2_type, type, v3_tops_2: $i > $i > $i > $o).
% 3.71/3.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.71/3.89  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 3.71/3.89  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.71/3.89  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.71/3.89  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.71/3.89  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 3.71/3.89  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.71/3.89  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.71/3.89  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.71/3.89  thf(d3_struct_0, axiom,
% 3.71/3.89    (![A:$i]:
% 3.71/3.89     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 3.71/3.89  thf('0', plain,
% 3.71/3.89      (![X22 : $i]:
% 3.71/3.89         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 3.71/3.89      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.71/3.89  thf('1', plain,
% 3.71/3.89      (![X22 : $i]:
% 3.71/3.89         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 3.71/3.89      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.71/3.89  thf(t70_tops_2, conjecture,
% 3.71/3.89    (![A:$i]:
% 3.71/3.89     ( ( l1_pre_topc @ A ) =>
% 3.71/3.89       ( ![B:$i]:
% 3.71/3.89         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_pre_topc @ B ) ) =>
% 3.71/3.89           ( ![C:$i]:
% 3.71/3.89             ( ( ( v1_funct_1 @ C ) & 
% 3.71/3.89                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 3.71/3.89                 ( m1_subset_1 @
% 3.71/3.89                   C @ 
% 3.71/3.89                   ( k1_zfmisc_1 @
% 3.71/3.89                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.71/3.89               ( ( v3_tops_2 @ C @ A @ B ) =>
% 3.71/3.89                 ( v3_tops_2 @
% 3.71/3.89                   ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 3.71/3.89                   B @ A ) ) ) ) ) ) ))).
% 3.71/3.89  thf(zf_stmt_0, negated_conjecture,
% 3.71/3.89    (~( ![A:$i]:
% 3.71/3.89        ( ( l1_pre_topc @ A ) =>
% 3.71/3.89          ( ![B:$i]:
% 3.71/3.89            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_pre_topc @ B ) ) =>
% 3.71/3.89              ( ![C:$i]:
% 3.71/3.89                ( ( ( v1_funct_1 @ C ) & 
% 3.71/3.89                    ( v1_funct_2 @
% 3.71/3.89                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 3.71/3.89                    ( m1_subset_1 @
% 3.71/3.89                      C @ 
% 3.71/3.89                      ( k1_zfmisc_1 @
% 3.71/3.89                        ( k2_zfmisc_1 @
% 3.71/3.89                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.71/3.89                  ( ( v3_tops_2 @ C @ A @ B ) =>
% 3.71/3.89                    ( v3_tops_2 @
% 3.71/3.89                      ( k2_tops_2 @
% 3.71/3.89                        ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 3.71/3.89                      B @ A ) ) ) ) ) ) ) )),
% 3.71/3.89    inference('cnf.neg', [status(esa)], [t70_tops_2])).
% 3.71/3.89  thf('2', plain,
% 3.71/3.89      (~ (v3_tops_2 @ 
% 3.71/3.89          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 3.71/3.89          sk_B @ sk_A)),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf('3', plain,
% 3.71/3.89      ((~ (v3_tops_2 @ 
% 3.71/3.89           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 3.71/3.89           sk_B @ sk_A)
% 3.71/3.89        | ~ (l1_struct_0 @ sk_A))),
% 3.71/3.89      inference('sup-', [status(thm)], ['1', '2'])).
% 3.71/3.89  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf(dt_l1_pre_topc, axiom,
% 3.71/3.89    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 3.71/3.89  thf('5', plain, (![X23 : $i]: ((l1_struct_0 @ X23) | ~ (l1_pre_topc @ X23))),
% 3.71/3.89      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 3.71/3.89  thf('6', plain, ((l1_struct_0 @ sk_A)),
% 3.71/3.89      inference('sup-', [status(thm)], ['4', '5'])).
% 3.71/3.89  thf('7', plain,
% 3.71/3.89      (~ (v3_tops_2 @ 
% 3.71/3.89          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 3.71/3.89          sk_B @ sk_A)),
% 3.71/3.89      inference('demod', [status(thm)], ['3', '6'])).
% 3.71/3.89  thf('8', plain,
% 3.71/3.89      ((~ (v3_tops_2 @ 
% 3.71/3.89           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C) @ 
% 3.71/3.89           sk_B @ sk_A)
% 3.71/3.89        | ~ (l1_struct_0 @ sk_B))),
% 3.71/3.89      inference('sup-', [status(thm)], ['0', '7'])).
% 3.71/3.89  thf('9', plain, ((l1_pre_topc @ sk_B)),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf('10', plain,
% 3.71/3.89      (![X23 : $i]: ((l1_struct_0 @ X23) | ~ (l1_pre_topc @ X23))),
% 3.71/3.89      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 3.71/3.89  thf('11', plain, ((l1_struct_0 @ sk_B)),
% 3.71/3.89      inference('sup-', [status(thm)], ['9', '10'])).
% 3.71/3.89  thf('12', plain,
% 3.71/3.89      (~ (v3_tops_2 @ 
% 3.71/3.89          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C) @ 
% 3.71/3.89          sk_B @ sk_A)),
% 3.71/3.89      inference('demod', [status(thm)], ['8', '11'])).
% 3.71/3.89  thf('13', plain,
% 3.71/3.89      ((m1_subset_1 @ sk_C @ 
% 3.71/3.89        (k1_zfmisc_1 @ 
% 3.71/3.89         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf(d5_tops_2, axiom,
% 3.71/3.89    (![A:$i]:
% 3.71/3.89     ( ( l1_pre_topc @ A ) =>
% 3.71/3.89       ( ![B:$i]:
% 3.71/3.89         ( ( l1_pre_topc @ B ) =>
% 3.71/3.89           ( ![C:$i]:
% 3.71/3.89             ( ( ( v1_funct_1 @ C ) & 
% 3.71/3.89                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 3.71/3.89                 ( m1_subset_1 @
% 3.71/3.89                   C @ 
% 3.71/3.89                   ( k1_zfmisc_1 @
% 3.71/3.89                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.71/3.89               ( ( v3_tops_2 @ C @ A @ B ) <=>
% 3.71/3.89                 ( ( ( k1_relset_1 @
% 3.71/3.89                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 3.71/3.89                     ( k2_struct_0 @ A ) ) & 
% 3.71/3.89                   ( ( k2_relset_1 @
% 3.71/3.89                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 3.71/3.89                     ( k2_struct_0 @ B ) ) & 
% 3.71/3.89                   ( v2_funct_1 @ C ) & ( v5_pre_topc @ C @ A @ B ) & 
% 3.71/3.89                   ( v5_pre_topc @
% 3.71/3.89                     ( k2_tops_2 @
% 3.71/3.89                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) @ 
% 3.71/3.89                     B @ A ) ) ) ) ) ) ) ))).
% 3.71/3.89  thf('14', plain,
% 3.71/3.89      (![X27 : $i, X28 : $i, X29 : $i]:
% 3.71/3.89         (~ (l1_pre_topc @ X27)
% 3.71/3.89          | ~ (v3_tops_2 @ X28 @ X29 @ X27)
% 3.71/3.89          | ((k1_relset_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27) @ X28)
% 3.71/3.89              = (k2_struct_0 @ X29))
% 3.71/3.89          | ~ (m1_subset_1 @ X28 @ 
% 3.71/3.89               (k1_zfmisc_1 @ 
% 3.71/3.89                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27))))
% 3.71/3.89          | ~ (v1_funct_2 @ X28 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27))
% 3.71/3.89          | ~ (v1_funct_1 @ X28)
% 3.71/3.89          | ~ (l1_pre_topc @ X29))),
% 3.71/3.89      inference('cnf', [status(esa)], [d5_tops_2])).
% 3.71/3.89  thf('15', plain,
% 3.71/3.89      ((~ (l1_pre_topc @ sk_A)
% 3.71/3.89        | ~ (v1_funct_1 @ sk_C)
% 3.71/3.89        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.71/3.89        | ((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.71/3.89            = (k2_struct_0 @ sk_A))
% 3.71/3.89        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 3.71/3.89        | ~ (l1_pre_topc @ sk_B))),
% 3.71/3.89      inference('sup-', [status(thm)], ['13', '14'])).
% 3.71/3.89  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf('18', plain,
% 3.71/3.89      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf('19', plain,
% 3.71/3.89      ((m1_subset_1 @ sk_C @ 
% 3.71/3.89        (k1_zfmisc_1 @ 
% 3.71/3.89         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.71/3.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.89  thf(redefinition_k1_relset_1, axiom,
% 3.71/3.89    (![A:$i,B:$i,C:$i]:
% 3.71/3.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.71/3.89       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.71/3.89  thf('20', plain,
% 3.71/3.89      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.71/3.89         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 3.71/3.90          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 3.71/3.90      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.71/3.90  thf('21', plain,
% 3.71/3.90      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90         = (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('sup-', [status(thm)], ['19', '20'])).
% 3.71/3.90  thf('22', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('23', plain, ((l1_pre_topc @ sk_B)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('24', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 3.71/3.90      inference('demod', [status(thm)],
% 3.71/3.90                ['15', '16', '17', '18', '21', '22', '23'])).
% 3.71/3.90  thf('25', plain,
% 3.71/3.90      (~ (v3_tops_2 @ 
% 3.71/3.90          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C) @ 
% 3.71/3.90          sk_B @ sk_A)),
% 3.71/3.90      inference('demod', [status(thm)], ['12', '24'])).
% 3.71/3.90  thf('26', plain,
% 3.71/3.90      (![X22 : $i]:
% 3.71/3.90         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 3.71/3.90      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.71/3.90  thf('27', plain,
% 3.71/3.90      (![X22 : $i]:
% 3.71/3.90         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 3.71/3.90      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.71/3.90  thf('28', plain,
% 3.71/3.90      ((m1_subset_1 @ sk_C @ 
% 3.71/3.90        (k1_zfmisc_1 @ 
% 3.71/3.90         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('29', plain,
% 3.71/3.90      (((m1_subset_1 @ sk_C @ 
% 3.71/3.90         (k1_zfmisc_1 @ 
% 3.71/3.90          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 3.71/3.90        | ~ (l1_struct_0 @ sk_B))),
% 3.71/3.90      inference('sup+', [status(thm)], ['27', '28'])).
% 3.71/3.90  thf('30', plain, ((l1_struct_0 @ sk_B)),
% 3.71/3.90      inference('sup-', [status(thm)], ['9', '10'])).
% 3.71/3.90  thf('31', plain,
% 3.71/3.90      ((m1_subset_1 @ sk_C @ 
% 3.71/3.90        (k1_zfmisc_1 @ 
% 3.71/3.90         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 3.71/3.90      inference('demod', [status(thm)], ['29', '30'])).
% 3.71/3.90  thf(d4_tops_2, axiom,
% 3.71/3.90    (![A:$i,B:$i,C:$i]:
% 3.71/3.90     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.71/3.90         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.71/3.90       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 3.71/3.90         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 3.71/3.90  thf('32', plain,
% 3.71/3.90      (![X24 : $i, X25 : $i, X26 : $i]:
% 3.71/3.90         (((k2_relset_1 @ X25 @ X24 @ X26) != (X24))
% 3.71/3.90          | ~ (v2_funct_1 @ X26)
% 3.71/3.90          | ((k2_tops_2 @ X25 @ X24 @ X26) = (k2_funct_1 @ X26))
% 3.71/3.90          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24)))
% 3.71/3.90          | ~ (v1_funct_2 @ X26 @ X25 @ X24)
% 3.71/3.90          | ~ (v1_funct_1 @ X26))),
% 3.71/3.90      inference('cnf', [status(esa)], [d4_tops_2])).
% 3.71/3.90  thf('33', plain,
% 3.71/3.90      ((~ (v1_funct_1 @ sk_C)
% 3.71/3.90        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 3.71/3.90        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90            = (k2_funct_1 @ sk_C))
% 3.71/3.90        | ~ (v2_funct_1 @ sk_C)
% 3.71/3.90        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90            != (k2_struct_0 @ sk_B)))),
% 3.71/3.90      inference('sup-', [status(thm)], ['31', '32'])).
% 3.71/3.90  thf('34', plain, ((v1_funct_1 @ sk_C)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('35', plain,
% 3.71/3.90      (![X22 : $i]:
% 3.71/3.90         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 3.71/3.90      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.71/3.90  thf('36', plain,
% 3.71/3.90      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('37', plain,
% 3.71/3.90      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 3.71/3.90        | ~ (l1_struct_0 @ sk_B))),
% 3.71/3.90      inference('sup+', [status(thm)], ['35', '36'])).
% 3.71/3.90  thf('38', plain, ((l1_struct_0 @ sk_B)),
% 3.71/3.90      inference('sup-', [status(thm)], ['9', '10'])).
% 3.71/3.90  thf('39', plain,
% 3.71/3.90      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['37', '38'])).
% 3.71/3.90  thf('40', plain,
% 3.71/3.90      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90          = (k2_funct_1 @ sk_C))
% 3.71/3.90        | ~ (v2_funct_1 @ sk_C)
% 3.71/3.90        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90            != (k2_struct_0 @ sk_B)))),
% 3.71/3.90      inference('demod', [status(thm)], ['33', '34', '39'])).
% 3.71/3.90  thf('41', plain,
% 3.71/3.90      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90          != (k2_struct_0 @ sk_B))
% 3.71/3.90        | ~ (l1_struct_0 @ sk_A)
% 3.71/3.90        | ~ (v2_funct_1 @ sk_C)
% 3.71/3.90        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90            = (k2_funct_1 @ sk_C)))),
% 3.71/3.90      inference('sup-', [status(thm)], ['26', '40'])).
% 3.71/3.90  thf('42', plain, ((l1_struct_0 @ sk_A)),
% 3.71/3.90      inference('sup-', [status(thm)], ['4', '5'])).
% 3.71/3.90  thf('43', plain,
% 3.71/3.90      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90          != (k2_struct_0 @ sk_B))
% 3.71/3.90        | ~ (v2_funct_1 @ sk_C)
% 3.71/3.90        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90            = (k2_funct_1 @ sk_C)))),
% 3.71/3.90      inference('demod', [status(thm)], ['41', '42'])).
% 3.71/3.90  thf('44', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 3.71/3.90      inference('demod', [status(thm)],
% 3.71/3.90                ['15', '16', '17', '18', '21', '22', '23'])).
% 3.71/3.90  thf('45', plain,
% 3.71/3.90      ((((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90          != (k2_struct_0 @ sk_B))
% 3.71/3.90        | ~ (v2_funct_1 @ sk_C)
% 3.71/3.90        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90            = (k2_funct_1 @ sk_C)))),
% 3.71/3.90      inference('demod', [status(thm)], ['43', '44'])).
% 3.71/3.90  thf('46', plain,
% 3.71/3.90      (![X22 : $i]:
% 3.71/3.90         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 3.71/3.90      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.71/3.90  thf('47', plain,
% 3.71/3.90      ((m1_subset_1 @ sk_C @ 
% 3.71/3.90        (k1_zfmisc_1 @ 
% 3.71/3.90         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf(cc2_relset_1, axiom,
% 3.71/3.90    (![A:$i,B:$i,C:$i]:
% 3.71/3.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.71/3.90       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.71/3.90  thf('48', plain,
% 3.71/3.90      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.71/3.90         ((v4_relat_1 @ X13 @ X14)
% 3.71/3.90          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 3.71/3.90      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.71/3.90  thf('49', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 3.71/3.90      inference('sup-', [status(thm)], ['47', '48'])).
% 3.71/3.90  thf(d18_relat_1, axiom,
% 3.71/3.90    (![A:$i,B:$i]:
% 3.71/3.90     ( ( v1_relat_1 @ B ) =>
% 3.71/3.90       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 3.71/3.90  thf('50', plain,
% 3.71/3.90      (![X6 : $i, X7 : $i]:
% 3.71/3.90         (~ (v4_relat_1 @ X6 @ X7)
% 3.71/3.90          | (r1_tarski @ (k1_relat_1 @ X6) @ X7)
% 3.71/3.90          | ~ (v1_relat_1 @ X6))),
% 3.71/3.90      inference('cnf', [status(esa)], [d18_relat_1])).
% 3.71/3.90  thf('51', plain,
% 3.71/3.90      ((~ (v1_relat_1 @ sk_C)
% 3.71/3.90        | (r1_tarski @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A)))),
% 3.71/3.90      inference('sup-', [status(thm)], ['49', '50'])).
% 3.71/3.90  thf('52', plain,
% 3.71/3.90      ((m1_subset_1 @ sk_C @ 
% 3.71/3.90        (k1_zfmisc_1 @ 
% 3.71/3.90         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf(cc1_relset_1, axiom,
% 3.71/3.90    (![A:$i,B:$i,C:$i]:
% 3.71/3.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.71/3.90       ( v1_relat_1 @ C ) ))).
% 3.71/3.90  thf('53', plain,
% 3.71/3.90      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.71/3.90         ((v1_relat_1 @ X10)
% 3.71/3.90          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 3.71/3.90      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.71/3.90  thf('54', plain, ((v1_relat_1 @ sk_C)),
% 3.71/3.90      inference('sup-', [status(thm)], ['52', '53'])).
% 3.71/3.90  thf('55', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 3.71/3.90      inference('demod', [status(thm)], ['51', '54'])).
% 3.71/3.90  thf(d10_xboole_0, axiom,
% 3.71/3.90    (![A:$i,B:$i]:
% 3.71/3.90     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.71/3.90  thf('56', plain,
% 3.71/3.90      (![X0 : $i, X2 : $i]:
% 3.71/3.90         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.71/3.90      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.71/3.90  thf('57', plain,
% 3.71/3.90      ((~ (r1_tarski @ (u1_struct_0 @ sk_A) @ (k1_relat_1 @ sk_C))
% 3.71/3.90        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 3.71/3.90      inference('sup-', [status(thm)], ['55', '56'])).
% 3.71/3.90  thf('58', plain,
% 3.71/3.90      ((~ (r1_tarski @ (k2_struct_0 @ sk_A) @ (k1_relat_1 @ sk_C))
% 3.71/3.90        | ~ (l1_struct_0 @ sk_A)
% 3.71/3.90        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 3.71/3.90      inference('sup-', [status(thm)], ['46', '57'])).
% 3.71/3.90  thf('59', plain, ((l1_struct_0 @ sk_A)),
% 3.71/3.90      inference('sup-', [status(thm)], ['4', '5'])).
% 3.71/3.90  thf('60', plain,
% 3.71/3.90      ((~ (r1_tarski @ (k2_struct_0 @ sk_A) @ (k1_relat_1 @ sk_C))
% 3.71/3.90        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 3.71/3.90      inference('demod', [status(thm)], ['58', '59'])).
% 3.71/3.90  thf('61', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 3.71/3.90      inference('demod', [status(thm)],
% 3.71/3.90                ['15', '16', '17', '18', '21', '22', '23'])).
% 3.71/3.90  thf('62', plain,
% 3.71/3.90      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 3.71/3.90      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.71/3.90  thf('63', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.71/3.90      inference('simplify', [status(thm)], ['62'])).
% 3.71/3.90  thf('64', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('demod', [status(thm)], ['60', '61', '63'])).
% 3.71/3.90  thf('65', plain,
% 3.71/3.90      ((((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90          != (k2_struct_0 @ sk_B))
% 3.71/3.90        | ~ (v2_funct_1 @ sk_C)
% 3.71/3.90        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90            = (k2_funct_1 @ sk_C)))),
% 3.71/3.90      inference('demod', [status(thm)], ['45', '64'])).
% 3.71/3.90  thf('66', plain,
% 3.71/3.90      (![X22 : $i]:
% 3.71/3.90         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 3.71/3.90      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.71/3.90  thf('67', plain,
% 3.71/3.90      ((m1_subset_1 @ sk_C @ 
% 3.71/3.90        (k1_zfmisc_1 @ 
% 3.71/3.90         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('68', plain,
% 3.71/3.90      (((m1_subset_1 @ sk_C @ 
% 3.71/3.90         (k1_zfmisc_1 @ 
% 3.71/3.90          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 3.71/3.90        | ~ (l1_struct_0 @ sk_A))),
% 3.71/3.90      inference('sup+', [status(thm)], ['66', '67'])).
% 3.71/3.90  thf('69', plain, ((l1_struct_0 @ sk_A)),
% 3.71/3.90      inference('sup-', [status(thm)], ['4', '5'])).
% 3.71/3.90  thf('70', plain,
% 3.71/3.90      ((m1_subset_1 @ sk_C @ 
% 3.71/3.90        (k1_zfmisc_1 @ 
% 3.71/3.90         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.71/3.90      inference('demod', [status(thm)], ['68', '69'])).
% 3.71/3.90  thf('71', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 3.71/3.90      inference('demod', [status(thm)],
% 3.71/3.90                ['15', '16', '17', '18', '21', '22', '23'])).
% 3.71/3.90  thf('72', plain,
% 3.71/3.90      ((m1_subset_1 @ sk_C @ 
% 3.71/3.90        (k1_zfmisc_1 @ 
% 3.71/3.90         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 3.71/3.90      inference('demod', [status(thm)], ['70', '71'])).
% 3.71/3.90  thf('73', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('demod', [status(thm)], ['60', '61', '63'])).
% 3.71/3.90  thf('74', plain,
% 3.71/3.90      (![X27 : $i, X28 : $i, X29 : $i]:
% 3.71/3.90         (~ (l1_pre_topc @ X27)
% 3.71/3.90          | ~ (v3_tops_2 @ X28 @ X29 @ X27)
% 3.71/3.90          | (v2_funct_1 @ X28)
% 3.71/3.90          | ~ (m1_subset_1 @ X28 @ 
% 3.71/3.90               (k1_zfmisc_1 @ 
% 3.71/3.90                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27))))
% 3.71/3.90          | ~ (v1_funct_2 @ X28 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27))
% 3.71/3.90          | ~ (v1_funct_1 @ X28)
% 3.71/3.90          | ~ (l1_pre_topc @ X29))),
% 3.71/3.90      inference('cnf', [status(esa)], [d5_tops_2])).
% 3.71/3.90  thf('75', plain,
% 3.71/3.90      (![X0 : $i, X1 : $i]:
% 3.71/3.90         (~ (m1_subset_1 @ X1 @ 
% 3.71/3.90             (k1_zfmisc_1 @ 
% 3.71/3.90              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ X0))))
% 3.71/3.90          | ~ (l1_pre_topc @ sk_A)
% 3.71/3.90          | ~ (v1_funct_1 @ X1)
% 3.71/3.90          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 3.71/3.90          | (v2_funct_1 @ X1)
% 3.71/3.90          | ~ (v3_tops_2 @ X1 @ sk_A @ X0)
% 3.71/3.90          | ~ (l1_pre_topc @ X0))),
% 3.71/3.90      inference('sup-', [status(thm)], ['73', '74'])).
% 3.71/3.90  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('77', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('demod', [status(thm)], ['60', '61', '63'])).
% 3.71/3.90  thf('78', plain,
% 3.71/3.90      (![X0 : $i, X1 : $i]:
% 3.71/3.90         (~ (m1_subset_1 @ X1 @ 
% 3.71/3.90             (k1_zfmisc_1 @ 
% 3.71/3.90              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ X0))))
% 3.71/3.90          | ~ (v1_funct_1 @ X1)
% 3.71/3.90          | ~ (v1_funct_2 @ X1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ X0))
% 3.71/3.90          | (v2_funct_1 @ X1)
% 3.71/3.90          | ~ (v3_tops_2 @ X1 @ sk_A @ X0)
% 3.71/3.90          | ~ (l1_pre_topc @ X0))),
% 3.71/3.90      inference('demod', [status(thm)], ['75', '76', '77'])).
% 3.71/3.90  thf('79', plain,
% 3.71/3.90      ((~ (l1_pre_topc @ sk_B)
% 3.71/3.90        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 3.71/3.90        | (v2_funct_1 @ sk_C)
% 3.71/3.90        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 3.71/3.90        | ~ (v1_funct_1 @ sk_C))),
% 3.71/3.90      inference('sup-', [status(thm)], ['72', '78'])).
% 3.71/3.90  thf('80', plain, ((l1_pre_topc @ sk_B)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('81', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('82', plain,
% 3.71/3.90      (![X22 : $i]:
% 3.71/3.90         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 3.71/3.90      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.71/3.90  thf('83', plain,
% 3.71/3.90      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('84', plain,
% 3.71/3.90      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.71/3.90        | ~ (l1_struct_0 @ sk_A))),
% 3.71/3.90      inference('sup+', [status(thm)], ['82', '83'])).
% 3.71/3.90  thf('85', plain, ((l1_struct_0 @ sk_A)),
% 3.71/3.90      inference('sup-', [status(thm)], ['4', '5'])).
% 3.71/3.90  thf('86', plain,
% 3.71/3.90      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['84', '85'])).
% 3.71/3.90  thf('87', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 3.71/3.90      inference('demod', [status(thm)],
% 3.71/3.90                ['15', '16', '17', '18', '21', '22', '23'])).
% 3.71/3.90  thf('88', plain,
% 3.71/3.90      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['86', '87'])).
% 3.71/3.90  thf('89', plain, ((v1_funct_1 @ sk_C)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('90', plain, ((v2_funct_1 @ sk_C)),
% 3.71/3.90      inference('demod', [status(thm)], ['79', '80', '81', '88', '89'])).
% 3.71/3.90  thf('91', plain,
% 3.71/3.90      ((((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90          != (k2_struct_0 @ sk_B))
% 3.71/3.90        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90            = (k2_funct_1 @ sk_C)))),
% 3.71/3.90      inference('demod', [status(thm)], ['65', '90'])).
% 3.71/3.90  thf('92', plain,
% 3.71/3.90      (![X22 : $i]:
% 3.71/3.90         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 3.71/3.90      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.71/3.90  thf('93', plain,
% 3.71/3.90      ((m1_subset_1 @ sk_C @ 
% 3.71/3.90        (k1_zfmisc_1 @ 
% 3.71/3.90         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 3.71/3.90      inference('demod', [status(thm)], ['70', '71'])).
% 3.71/3.90  thf('94', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('demod', [status(thm)], ['60', '61', '63'])).
% 3.71/3.90  thf('95', plain,
% 3.71/3.90      (![X27 : $i, X28 : $i, X29 : $i]:
% 3.71/3.90         (~ (l1_pre_topc @ X27)
% 3.71/3.90          | ~ (v3_tops_2 @ X28 @ X29 @ X27)
% 3.71/3.90          | ((k2_relset_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27) @ X28)
% 3.71/3.90              = (k2_struct_0 @ X27))
% 3.71/3.90          | ~ (m1_subset_1 @ X28 @ 
% 3.71/3.90               (k1_zfmisc_1 @ 
% 3.71/3.90                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27))))
% 3.71/3.90          | ~ (v1_funct_2 @ X28 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27))
% 3.71/3.90          | ~ (v1_funct_1 @ X28)
% 3.71/3.90          | ~ (l1_pre_topc @ X29))),
% 3.71/3.90      inference('cnf', [status(esa)], [d5_tops_2])).
% 3.71/3.90  thf('96', plain,
% 3.71/3.90      (![X0 : $i, X1 : $i]:
% 3.71/3.90         (~ (m1_subset_1 @ X1 @ 
% 3.71/3.90             (k1_zfmisc_1 @ 
% 3.71/3.90              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ X0))))
% 3.71/3.90          | ~ (l1_pre_topc @ sk_A)
% 3.71/3.90          | ~ (v1_funct_1 @ X1)
% 3.71/3.90          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 3.71/3.90          | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0) @ X1)
% 3.71/3.90              = (k2_struct_0 @ X0))
% 3.71/3.90          | ~ (v3_tops_2 @ X1 @ sk_A @ X0)
% 3.71/3.90          | ~ (l1_pre_topc @ X0))),
% 3.71/3.90      inference('sup-', [status(thm)], ['94', '95'])).
% 3.71/3.90  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('98', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('demod', [status(thm)], ['60', '61', '63'])).
% 3.71/3.90  thf('99', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('demod', [status(thm)], ['60', '61', '63'])).
% 3.71/3.90  thf('100', plain,
% 3.71/3.90      (![X0 : $i, X1 : $i]:
% 3.71/3.90         (~ (m1_subset_1 @ X1 @ 
% 3.71/3.90             (k1_zfmisc_1 @ 
% 3.71/3.90              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ X0))))
% 3.71/3.90          | ~ (v1_funct_1 @ X1)
% 3.71/3.90          | ~ (v1_funct_2 @ X1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ X0))
% 3.71/3.90          | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ X0) @ X1)
% 3.71/3.90              = (k2_struct_0 @ X0))
% 3.71/3.90          | ~ (v3_tops_2 @ X1 @ sk_A @ X0)
% 3.71/3.90          | ~ (l1_pre_topc @ X0))),
% 3.71/3.90      inference('demod', [status(thm)], ['96', '97', '98', '99'])).
% 3.71/3.90  thf('101', plain,
% 3.71/3.90      ((~ (l1_pre_topc @ sk_B)
% 3.71/3.90        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 3.71/3.90        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90            = (k2_struct_0 @ sk_B))
% 3.71/3.90        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 3.71/3.90        | ~ (v1_funct_1 @ sk_C))),
% 3.71/3.90      inference('sup-', [status(thm)], ['93', '100'])).
% 3.71/3.90  thf('102', plain, ((l1_pre_topc @ sk_B)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('103', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('104', plain,
% 3.71/3.90      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['86', '87'])).
% 3.71/3.90  thf('105', plain, ((v1_funct_1 @ sk_C)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('106', plain,
% 3.71/3.90      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90         = (k2_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['101', '102', '103', '104', '105'])).
% 3.71/3.90  thf('107', plain,
% 3.71/3.90      ((((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90          = (k2_struct_0 @ sk_B))
% 3.71/3.90        | ~ (l1_struct_0 @ sk_B))),
% 3.71/3.90      inference('sup+', [status(thm)], ['92', '106'])).
% 3.71/3.90  thf('108', plain, ((l1_struct_0 @ sk_B)),
% 3.71/3.90      inference('sup-', [status(thm)], ['9', '10'])).
% 3.71/3.90  thf('109', plain,
% 3.71/3.90      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90         = (k2_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['107', '108'])).
% 3.71/3.90  thf('110', plain,
% 3.71/3.90      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 3.71/3.90        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90            = (k2_funct_1 @ sk_C)))),
% 3.71/3.90      inference('demod', [status(thm)], ['91', '109'])).
% 3.71/3.90  thf('111', plain,
% 3.71/3.90      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90         = (k2_funct_1 @ sk_C))),
% 3.71/3.90      inference('simplify', [status(thm)], ['110'])).
% 3.71/3.90  thf('112', plain, (~ (v3_tops_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 3.71/3.90      inference('demod', [status(thm)], ['25', '111'])).
% 3.71/3.90  thf(fc6_funct_1, axiom,
% 3.71/3.90    (![A:$i]:
% 3.71/3.90     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 3.71/3.90       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 3.71/3.90         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 3.71/3.90         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 3.71/3.90  thf('113', plain,
% 3.71/3.90      (![X8 : $i]:
% 3.71/3.90         ((v2_funct_1 @ (k2_funct_1 @ X8))
% 3.71/3.90          | ~ (v2_funct_1 @ X8)
% 3.71/3.90          | ~ (v1_funct_1 @ X8)
% 3.71/3.90          | ~ (v1_relat_1 @ X8))),
% 3.71/3.90      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.71/3.90  thf('114', plain,
% 3.71/3.90      (![X22 : $i]:
% 3.71/3.90         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 3.71/3.90      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.71/3.90  thf('115', plain,
% 3.71/3.90      ((m1_subset_1 @ sk_C @ 
% 3.71/3.90        (k1_zfmisc_1 @ 
% 3.71/3.90         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.71/3.90      inference('demod', [status(thm)], ['68', '69'])).
% 3.71/3.90  thf('116', plain,
% 3.71/3.90      (((m1_subset_1 @ sk_C @ 
% 3.71/3.90         (k1_zfmisc_1 @ 
% 3.71/3.90          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 3.71/3.90        | ~ (l1_struct_0 @ sk_B))),
% 3.71/3.90      inference('sup+', [status(thm)], ['114', '115'])).
% 3.71/3.90  thf('117', plain, ((l1_struct_0 @ sk_B)),
% 3.71/3.90      inference('sup-', [status(thm)], ['9', '10'])).
% 3.71/3.90  thf('118', plain,
% 3.71/3.90      ((m1_subset_1 @ sk_C @ 
% 3.71/3.90        (k1_zfmisc_1 @ 
% 3.71/3.90         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 3.71/3.90      inference('demod', [status(thm)], ['116', '117'])).
% 3.71/3.90  thf(t31_funct_2, axiom,
% 3.71/3.90    (![A:$i,B:$i,C:$i]:
% 3.71/3.90     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.71/3.90         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.71/3.90       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 3.71/3.90         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 3.71/3.90           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 3.71/3.90           ( m1_subset_1 @
% 3.71/3.90             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 3.71/3.90  thf('119', plain,
% 3.71/3.90      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.71/3.90         (~ (v2_funct_1 @ X19)
% 3.71/3.90          | ((k2_relset_1 @ X21 @ X20 @ X19) != (X20))
% 3.71/3.90          | (m1_subset_1 @ (k2_funct_1 @ X19) @ 
% 3.71/3.90             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 3.71/3.90          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20)))
% 3.71/3.90          | ~ (v1_funct_2 @ X19 @ X21 @ X20)
% 3.71/3.90          | ~ (v1_funct_1 @ X19))),
% 3.71/3.90      inference('cnf', [status(esa)], [t31_funct_2])).
% 3.71/3.90  thf('120', plain,
% 3.71/3.90      ((~ (v1_funct_1 @ sk_C)
% 3.71/3.90        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 3.71/3.90        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.71/3.90           (k1_zfmisc_1 @ 
% 3.71/3.90            (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 3.71/3.90        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90            != (k2_struct_0 @ sk_B))
% 3.71/3.90        | ~ (v2_funct_1 @ sk_C))),
% 3.71/3.90      inference('sup-', [status(thm)], ['118', '119'])).
% 3.71/3.90  thf('121', plain, ((v1_funct_1 @ sk_C)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('122', plain,
% 3.71/3.90      (![X22 : $i]:
% 3.71/3.90         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 3.71/3.90      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.71/3.90  thf('123', plain,
% 3.71/3.90      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['84', '85'])).
% 3.71/3.90  thf('124', plain,
% 3.71/3.90      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 3.71/3.90        | ~ (l1_struct_0 @ sk_B))),
% 3.71/3.90      inference('sup+', [status(thm)], ['122', '123'])).
% 3.71/3.90  thf('125', plain, ((l1_struct_0 @ sk_B)),
% 3.71/3.90      inference('sup-', [status(thm)], ['9', '10'])).
% 3.71/3.90  thf('126', plain,
% 3.71/3.90      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['124', '125'])).
% 3.71/3.90  thf('127', plain,
% 3.71/3.90      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.71/3.90         (k1_zfmisc_1 @ 
% 3.71/3.90          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 3.71/3.90        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90            != (k2_struct_0 @ sk_B))
% 3.71/3.90        | ~ (v2_funct_1 @ sk_C))),
% 3.71/3.90      inference('demod', [status(thm)], ['120', '121', '126'])).
% 3.71/3.90  thf('128', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 3.71/3.90      inference('demod', [status(thm)],
% 3.71/3.90                ['15', '16', '17', '18', '21', '22', '23'])).
% 3.71/3.90  thf('129', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 3.71/3.90      inference('demod', [status(thm)],
% 3.71/3.90                ['15', '16', '17', '18', '21', '22', '23'])).
% 3.71/3.90  thf('130', plain,
% 3.71/3.90      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.71/3.90         (k1_zfmisc_1 @ 
% 3.71/3.90          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 3.71/3.90        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90            != (k2_struct_0 @ sk_B))
% 3.71/3.90        | ~ (v2_funct_1 @ sk_C))),
% 3.71/3.90      inference('demod', [status(thm)], ['127', '128', '129'])).
% 3.71/3.90  thf('131', plain, ((v2_funct_1 @ sk_C)),
% 3.71/3.90      inference('demod', [status(thm)], ['79', '80', '81', '88', '89'])).
% 3.71/3.90  thf('132', plain,
% 3.71/3.90      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.71/3.90         (k1_zfmisc_1 @ 
% 3.71/3.90          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 3.71/3.90        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90            != (k2_struct_0 @ sk_B)))),
% 3.71/3.90      inference('demod', [status(thm)], ['130', '131'])).
% 3.71/3.90  thf('133', plain,
% 3.71/3.90      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90         = (k2_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['107', '108'])).
% 3.71/3.90  thf('134', plain,
% 3.71/3.90      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.71/3.90         (k1_zfmisc_1 @ 
% 3.71/3.90          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 3.71/3.90        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 3.71/3.90      inference('demod', [status(thm)], ['132', '133'])).
% 3.71/3.90  thf('135', plain,
% 3.71/3.90      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.71/3.90        (k1_zfmisc_1 @ 
% 3.71/3.90         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 3.71/3.90      inference('simplify', [status(thm)], ['134'])).
% 3.71/3.90  thf('136', plain,
% 3.71/3.90      (![X24 : $i, X25 : $i, X26 : $i]:
% 3.71/3.90         (((k2_relset_1 @ X25 @ X24 @ X26) != (X24))
% 3.71/3.90          | ~ (v2_funct_1 @ X26)
% 3.71/3.90          | ((k2_tops_2 @ X25 @ X24 @ X26) = (k2_funct_1 @ X26))
% 3.71/3.90          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24)))
% 3.71/3.90          | ~ (v1_funct_2 @ X26 @ X25 @ X24)
% 3.71/3.90          | ~ (v1_funct_1 @ X26))),
% 3.71/3.90      inference('cnf', [status(esa)], [d4_tops_2])).
% 3.71/3.90  thf('137', plain,
% 3.71/3.90      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.71/3.90        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.71/3.90             (k1_relat_1 @ sk_C))
% 3.71/3.90        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 3.71/3.90            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.71/3.90        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 3.71/3.90        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 3.71/3.90            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 3.71/3.90      inference('sup-', [status(thm)], ['135', '136'])).
% 3.71/3.90  thf('138', plain,
% 3.71/3.90      (![X22 : $i]:
% 3.71/3.90         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 3.71/3.90      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.71/3.90  thf('139', plain,
% 3.71/3.90      ((m1_subset_1 @ sk_C @ 
% 3.71/3.90        (k1_zfmisc_1 @ 
% 3.71/3.90         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.71/3.90      inference('demod', [status(thm)], ['68', '69'])).
% 3.71/3.90  thf('140', plain,
% 3.71/3.90      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.71/3.90         (~ (v2_funct_1 @ X19)
% 3.71/3.90          | ((k2_relset_1 @ X21 @ X20 @ X19) != (X20))
% 3.71/3.90          | (v1_funct_1 @ (k2_funct_1 @ X19))
% 3.71/3.90          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20)))
% 3.71/3.90          | ~ (v1_funct_2 @ X19 @ X21 @ X20)
% 3.71/3.90          | ~ (v1_funct_1 @ X19))),
% 3.71/3.90      inference('cnf', [status(esa)], [t31_funct_2])).
% 3.71/3.90  thf('141', plain,
% 3.71/3.90      ((~ (v1_funct_1 @ sk_C)
% 3.71/3.90        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.71/3.90        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.71/3.90        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90            != (u1_struct_0 @ sk_B))
% 3.71/3.90        | ~ (v2_funct_1 @ sk_C))),
% 3.71/3.90      inference('sup-', [status(thm)], ['139', '140'])).
% 3.71/3.90  thf('142', plain, ((v1_funct_1 @ sk_C)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('143', plain,
% 3.71/3.90      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['84', '85'])).
% 3.71/3.90  thf('144', plain,
% 3.71/3.90      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.71/3.90        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90            != (u1_struct_0 @ sk_B))
% 3.71/3.90        | ~ (v2_funct_1 @ sk_C))),
% 3.71/3.90      inference('demod', [status(thm)], ['141', '142', '143'])).
% 3.71/3.90  thf('145', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 3.71/3.90      inference('demod', [status(thm)],
% 3.71/3.90                ['15', '16', '17', '18', '21', '22', '23'])).
% 3.71/3.90  thf('146', plain,
% 3.71/3.90      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.71/3.90        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90            != (u1_struct_0 @ sk_B))
% 3.71/3.90        | ~ (v2_funct_1 @ sk_C))),
% 3.71/3.90      inference('demod', [status(thm)], ['144', '145'])).
% 3.71/3.90  thf('147', plain, ((v2_funct_1 @ sk_C)),
% 3.71/3.90      inference('demod', [status(thm)], ['79', '80', '81', '88', '89'])).
% 3.71/3.90  thf('148', plain,
% 3.71/3.90      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.71/3.90        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90            != (u1_struct_0 @ sk_B)))),
% 3.71/3.90      inference('demod', [status(thm)], ['146', '147'])).
% 3.71/3.90  thf('149', plain,
% 3.71/3.90      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90         = (k2_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['101', '102', '103', '104', '105'])).
% 3.71/3.90  thf('150', plain,
% 3.71/3.90      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.71/3.90        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 3.71/3.90      inference('demod', [status(thm)], ['148', '149'])).
% 3.71/3.90  thf('151', plain,
% 3.71/3.90      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 3.71/3.90        | ~ (l1_struct_0 @ sk_B)
% 3.71/3.90        | (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.71/3.90      inference('sup-', [status(thm)], ['138', '150'])).
% 3.71/3.90  thf('152', plain, ((l1_struct_0 @ sk_B)),
% 3.71/3.90      inference('sup-', [status(thm)], ['9', '10'])).
% 3.71/3.90  thf('153', plain,
% 3.71/3.90      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 3.71/3.90        | (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.71/3.90      inference('demod', [status(thm)], ['151', '152'])).
% 3.71/3.90  thf('154', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 3.71/3.90      inference('simplify', [status(thm)], ['153'])).
% 3.71/3.90  thf('155', plain,
% 3.71/3.90      ((m1_subset_1 @ sk_C @ 
% 3.71/3.90        (k1_zfmisc_1 @ 
% 3.71/3.90         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 3.71/3.90      inference('demod', [status(thm)], ['116', '117'])).
% 3.71/3.90  thf('156', plain,
% 3.71/3.90      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.71/3.90         (~ (v2_funct_1 @ X19)
% 3.71/3.90          | ((k2_relset_1 @ X21 @ X20 @ X19) != (X20))
% 3.71/3.90          | (v1_funct_2 @ (k2_funct_1 @ X19) @ X20 @ X21)
% 3.71/3.90          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20)))
% 3.71/3.90          | ~ (v1_funct_2 @ X19 @ X21 @ X20)
% 3.71/3.90          | ~ (v1_funct_1 @ X19))),
% 3.71/3.90      inference('cnf', [status(esa)], [t31_funct_2])).
% 3.71/3.90  thf('157', plain,
% 3.71/3.90      ((~ (v1_funct_1 @ sk_C)
% 3.71/3.90        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 3.71/3.90        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.71/3.90           (k2_struct_0 @ sk_A))
% 3.71/3.90        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90            != (k2_struct_0 @ sk_B))
% 3.71/3.90        | ~ (v2_funct_1 @ sk_C))),
% 3.71/3.90      inference('sup-', [status(thm)], ['155', '156'])).
% 3.71/3.90  thf('158', plain, ((v1_funct_1 @ sk_C)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('159', plain,
% 3.71/3.90      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['124', '125'])).
% 3.71/3.90  thf('160', plain,
% 3.71/3.90      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.71/3.90         (k2_struct_0 @ sk_A))
% 3.71/3.90        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90            != (k2_struct_0 @ sk_B))
% 3.71/3.90        | ~ (v2_funct_1 @ sk_C))),
% 3.71/3.90      inference('demod', [status(thm)], ['157', '158', '159'])).
% 3.71/3.90  thf('161', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 3.71/3.90      inference('demod', [status(thm)],
% 3.71/3.90                ['15', '16', '17', '18', '21', '22', '23'])).
% 3.71/3.90  thf('162', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 3.71/3.90      inference('demod', [status(thm)],
% 3.71/3.90                ['15', '16', '17', '18', '21', '22', '23'])).
% 3.71/3.90  thf('163', plain,
% 3.71/3.90      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.71/3.90         (k1_relat_1 @ sk_C))
% 3.71/3.90        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90            != (k2_struct_0 @ sk_B))
% 3.71/3.90        | ~ (v2_funct_1 @ sk_C))),
% 3.71/3.90      inference('demod', [status(thm)], ['160', '161', '162'])).
% 3.71/3.90  thf('164', plain, ((v2_funct_1 @ sk_C)),
% 3.71/3.90      inference('demod', [status(thm)], ['79', '80', '81', '88', '89'])).
% 3.71/3.90  thf('165', plain,
% 3.71/3.90      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.71/3.90         (k1_relat_1 @ sk_C))
% 3.71/3.90        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90            != (k2_struct_0 @ sk_B)))),
% 3.71/3.90      inference('demod', [status(thm)], ['163', '164'])).
% 3.71/3.90  thf('166', plain,
% 3.71/3.90      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90         = (k2_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['107', '108'])).
% 3.71/3.90  thf('167', plain,
% 3.71/3.90      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.71/3.90         (k1_relat_1 @ sk_C))
% 3.71/3.90        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 3.71/3.90      inference('demod', [status(thm)], ['165', '166'])).
% 3.71/3.90  thf('168', plain,
% 3.71/3.90      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.71/3.90        (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('simplify', [status(thm)], ['167'])).
% 3.71/3.90  thf('169', plain,
% 3.71/3.90      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 3.71/3.90          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.71/3.90        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 3.71/3.90        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 3.71/3.90            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 3.71/3.90      inference('demod', [status(thm)], ['137', '154', '168'])).
% 3.71/3.90  thf('170', plain,
% 3.71/3.90      ((m1_subset_1 @ sk_C @ 
% 3.71/3.90        (k1_zfmisc_1 @ 
% 3.71/3.90         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 3.71/3.90      inference('demod', [status(thm)], ['116', '117'])).
% 3.71/3.90  thf('171', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 3.71/3.90      inference('demod', [status(thm)],
% 3.71/3.90                ['15', '16', '17', '18', '21', '22', '23'])).
% 3.71/3.90  thf('172', plain,
% 3.71/3.90      ((m1_subset_1 @ sk_C @ 
% 3.71/3.90        (k1_zfmisc_1 @ 
% 3.71/3.90         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))))),
% 3.71/3.90      inference('demod', [status(thm)], ['170', '171'])).
% 3.71/3.90  thf('173', plain,
% 3.71/3.90      (![X22 : $i]:
% 3.71/3.90         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 3.71/3.90      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.71/3.90  thf('174', plain,
% 3.71/3.90      (![X22 : $i]:
% 3.71/3.90         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 3.71/3.90      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.71/3.90  thf('175', plain,
% 3.71/3.90      (![X22 : $i]:
% 3.71/3.90         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 3.71/3.90      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.71/3.90  thf('176', plain,
% 3.71/3.90      ((m1_subset_1 @ sk_C @ 
% 3.71/3.90        (k1_zfmisc_1 @ 
% 3.71/3.90         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('177', plain,
% 3.71/3.90      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.71/3.90         (~ (v2_funct_1 @ X19)
% 3.71/3.90          | ((k2_relset_1 @ X21 @ X20 @ X19) != (X20))
% 3.71/3.90          | (m1_subset_1 @ (k2_funct_1 @ X19) @ 
% 3.71/3.90             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 3.71/3.90          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20)))
% 3.71/3.90          | ~ (v1_funct_2 @ X19 @ X21 @ X20)
% 3.71/3.90          | ~ (v1_funct_1 @ X19))),
% 3.71/3.90      inference('cnf', [status(esa)], [t31_funct_2])).
% 3.71/3.90  thf('178', plain,
% 3.71/3.90      ((~ (v1_funct_1 @ sk_C)
% 3.71/3.90        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.71/3.90        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.71/3.90           (k1_zfmisc_1 @ 
% 3.71/3.90            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 3.71/3.90        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90            != (u1_struct_0 @ sk_B))
% 3.71/3.90        | ~ (v2_funct_1 @ sk_C))),
% 3.71/3.90      inference('sup-', [status(thm)], ['176', '177'])).
% 3.71/3.90  thf('179', plain, ((v1_funct_1 @ sk_C)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('180', plain,
% 3.71/3.90      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('181', plain,
% 3.71/3.90      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.71/3.90         (k1_zfmisc_1 @ 
% 3.71/3.90          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 3.71/3.90        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90            != (u1_struct_0 @ sk_B))
% 3.71/3.90        | ~ (v2_funct_1 @ sk_C))),
% 3.71/3.90      inference('demod', [status(thm)], ['178', '179', '180'])).
% 3.71/3.90  thf('182', plain,
% 3.71/3.90      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90          != (u1_struct_0 @ sk_B))
% 3.71/3.90        | ~ (l1_struct_0 @ sk_A)
% 3.71/3.90        | ~ (v2_funct_1 @ sk_C)
% 3.71/3.90        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.71/3.90           (k1_zfmisc_1 @ 
% 3.71/3.90            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 3.71/3.90      inference('sup-', [status(thm)], ['175', '181'])).
% 3.71/3.90  thf('183', plain, ((l1_struct_0 @ sk_A)),
% 3.71/3.90      inference('sup-', [status(thm)], ['4', '5'])).
% 3.71/3.90  thf('184', plain,
% 3.71/3.90      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90          != (u1_struct_0 @ sk_B))
% 3.71/3.90        | ~ (v2_funct_1 @ sk_C)
% 3.71/3.90        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.71/3.90           (k1_zfmisc_1 @ 
% 3.71/3.90            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 3.71/3.90      inference('demod', [status(thm)], ['182', '183'])).
% 3.71/3.90  thf('185', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 3.71/3.90      inference('demod', [status(thm)],
% 3.71/3.90                ['15', '16', '17', '18', '21', '22', '23'])).
% 3.71/3.90  thf('186', plain,
% 3.71/3.90      ((((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90          != (u1_struct_0 @ sk_B))
% 3.71/3.90        | ~ (v2_funct_1 @ sk_C)
% 3.71/3.90        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.71/3.90           (k1_zfmisc_1 @ 
% 3.71/3.90            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 3.71/3.90      inference('demod', [status(thm)], ['184', '185'])).
% 3.71/3.90  thf('187', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('demod', [status(thm)], ['60', '61', '63'])).
% 3.71/3.90  thf('188', plain,
% 3.71/3.90      ((((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90          != (u1_struct_0 @ sk_B))
% 3.71/3.90        | ~ (v2_funct_1 @ sk_C)
% 3.71/3.90        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.71/3.90           (k1_zfmisc_1 @ 
% 3.71/3.90            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 3.71/3.90      inference('demod', [status(thm)], ['186', '187'])).
% 3.71/3.90  thf('189', plain, ((v2_funct_1 @ sk_C)),
% 3.71/3.90      inference('demod', [status(thm)], ['79', '80', '81', '88', '89'])).
% 3.71/3.90  thf('190', plain,
% 3.71/3.90      ((((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90          != (u1_struct_0 @ sk_B))
% 3.71/3.90        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.71/3.90           (k1_zfmisc_1 @ 
% 3.71/3.90            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 3.71/3.90      inference('demod', [status(thm)], ['188', '189'])).
% 3.71/3.90  thf('191', plain,
% 3.71/3.90      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90         = (k2_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['101', '102', '103', '104', '105'])).
% 3.71/3.90  thf('192', plain,
% 3.71/3.90      ((((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B))
% 3.71/3.90        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.71/3.90           (k1_zfmisc_1 @ 
% 3.71/3.90            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 3.71/3.90      inference('demod', [status(thm)], ['190', '191'])).
% 3.71/3.90  thf('193', plain,
% 3.71/3.90      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 3.71/3.90        | ~ (l1_struct_0 @ sk_B)
% 3.71/3.90        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.71/3.90           (k1_zfmisc_1 @ 
% 3.71/3.90            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 3.71/3.90      inference('sup-', [status(thm)], ['174', '192'])).
% 3.71/3.90  thf('194', plain, ((l1_struct_0 @ sk_B)),
% 3.71/3.90      inference('sup-', [status(thm)], ['9', '10'])).
% 3.71/3.90  thf('195', plain,
% 3.71/3.90      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 3.71/3.90        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.71/3.90           (k1_zfmisc_1 @ 
% 3.71/3.90            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 3.71/3.90      inference('demod', [status(thm)], ['193', '194'])).
% 3.71/3.90  thf('196', plain,
% 3.71/3.90      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.71/3.90        (k1_zfmisc_1 @ 
% 3.71/3.90         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 3.71/3.90      inference('simplify', [status(thm)], ['195'])).
% 3.71/3.90  thf('197', plain,
% 3.71/3.90      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.71/3.90         ((v4_relat_1 @ X13 @ X14)
% 3.71/3.90          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 3.71/3.90      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.71/3.90  thf('198', plain,
% 3.71/3.90      ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 3.71/3.90      inference('sup-', [status(thm)], ['196', '197'])).
% 3.71/3.90  thf('199', plain,
% 3.71/3.90      (![X6 : $i, X7 : $i]:
% 3.71/3.90         (~ (v4_relat_1 @ X6 @ X7)
% 3.71/3.90          | (r1_tarski @ (k1_relat_1 @ X6) @ X7)
% 3.71/3.90          | ~ (v1_relat_1 @ X6))),
% 3.71/3.90      inference('cnf', [status(esa)], [d18_relat_1])).
% 3.71/3.90  thf('200', plain,
% 3.71/3.90      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 3.71/3.90        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.71/3.90           (u1_struct_0 @ sk_B)))),
% 3.71/3.90      inference('sup-', [status(thm)], ['198', '199'])).
% 3.71/3.90  thf('201', plain,
% 3.71/3.90      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.71/3.90        (k1_zfmisc_1 @ 
% 3.71/3.90         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 3.71/3.90      inference('simplify', [status(thm)], ['134'])).
% 3.71/3.90  thf('202', plain,
% 3.71/3.90      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.71/3.90         ((v1_relat_1 @ X10)
% 3.71/3.90          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 3.71/3.90      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.71/3.90  thf('203', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 3.71/3.90      inference('sup-', [status(thm)], ['201', '202'])).
% 3.71/3.90  thf('204', plain,
% 3.71/3.90      ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ (u1_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['200', '203'])).
% 3.71/3.90  thf('205', plain,
% 3.71/3.90      (![X0 : $i, X2 : $i]:
% 3.71/3.90         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.71/3.90      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.71/3.90  thf('206', plain,
% 3.71/3.90      ((~ (r1_tarski @ (u1_struct_0 @ sk_B) @ 
% 3.71/3.90           (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 3.71/3.90        | ((u1_struct_0 @ sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 3.71/3.90      inference('sup-', [status(thm)], ['204', '205'])).
% 3.71/3.90  thf('207', plain,
% 3.71/3.90      ((~ (r1_tarski @ (k2_struct_0 @ sk_B) @ 
% 3.71/3.90           (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 3.71/3.90        | ~ (l1_struct_0 @ sk_B)
% 3.71/3.90        | ((u1_struct_0 @ sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 3.71/3.90      inference('sup-', [status(thm)], ['173', '206'])).
% 3.71/3.90  thf('208', plain, ((l1_struct_0 @ sk_B)),
% 3.71/3.90      inference('sup-', [status(thm)], ['9', '10'])).
% 3.71/3.90  thf('209', plain,
% 3.71/3.90      ((~ (r1_tarski @ (k2_struct_0 @ sk_B) @ 
% 3.71/3.90           (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 3.71/3.90        | ((u1_struct_0 @ sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 3.71/3.90      inference('demod', [status(thm)], ['207', '208'])).
% 3.71/3.90  thf('210', plain,
% 3.71/3.90      ((m1_subset_1 @ sk_C @ 
% 3.71/3.90        (k1_zfmisc_1 @ 
% 3.71/3.90         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 3.71/3.90      inference('demod', [status(thm)], ['70', '71'])).
% 3.71/3.90  thf('211', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('demod', [status(thm)], ['60', '61', '63'])).
% 3.71/3.90  thf(t62_tops_2, axiom,
% 3.71/3.90    (![A:$i]:
% 3.71/3.90     ( ( l1_struct_0 @ A ) =>
% 3.71/3.90       ( ![B:$i]:
% 3.71/3.90         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 3.71/3.90           ( ![C:$i]:
% 3.71/3.90             ( ( ( v1_funct_1 @ C ) & 
% 3.71/3.90                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 3.71/3.90                 ( m1_subset_1 @
% 3.71/3.90                   C @ 
% 3.71/3.90                   ( k1_zfmisc_1 @
% 3.71/3.90                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.71/3.90               ( ( ( ( k2_relset_1 @
% 3.71/3.90                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 3.71/3.90                     ( k2_struct_0 @ B ) ) & 
% 3.71/3.90                   ( v2_funct_1 @ C ) ) =>
% 3.71/3.90                 ( ( ( k1_relset_1 @
% 3.71/3.90                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 3.71/3.90                       ( k2_tops_2 @
% 3.71/3.90                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 3.71/3.90                     ( k2_struct_0 @ B ) ) & 
% 3.71/3.90                   ( ( k2_relset_1 @
% 3.71/3.90                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 3.71/3.90                       ( k2_tops_2 @
% 3.71/3.90                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 3.71/3.90                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 3.71/3.90  thf('212', plain,
% 3.71/3.90      (![X30 : $i, X31 : $i, X32 : $i]:
% 3.71/3.90         ((v2_struct_0 @ X30)
% 3.71/3.90          | ~ (l1_struct_0 @ X30)
% 3.71/3.90          | ((k2_relset_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30) @ X32)
% 3.71/3.90              != (k2_struct_0 @ X30))
% 3.71/3.90          | ~ (v2_funct_1 @ X32)
% 3.71/3.90          | ((k1_relset_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X31) @ 
% 3.71/3.90              (k2_tops_2 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30) @ X32))
% 3.71/3.90              = (k2_struct_0 @ X30))
% 3.71/3.90          | ~ (m1_subset_1 @ X32 @ 
% 3.71/3.90               (k1_zfmisc_1 @ 
% 3.71/3.90                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30))))
% 3.71/3.90          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30))
% 3.71/3.90          | ~ (v1_funct_1 @ X32)
% 3.71/3.90          | ~ (l1_struct_0 @ X31))),
% 3.71/3.90      inference('cnf', [status(esa)], [t62_tops_2])).
% 3.71/3.90  thf('213', plain,
% 3.71/3.90      (![X0 : $i, X1 : $i]:
% 3.71/3.90         (~ (m1_subset_1 @ X1 @ 
% 3.71/3.90             (k1_zfmisc_1 @ 
% 3.71/3.90              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ X0))))
% 3.71/3.90          | ~ (l1_struct_0 @ sk_A)
% 3.71/3.90          | ~ (v1_funct_1 @ X1)
% 3.71/3.90          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 3.71/3.90          | ((k1_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 3.71/3.90              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0) @ X1))
% 3.71/3.90              = (k2_struct_0 @ X0))
% 3.71/3.90          | ~ (v2_funct_1 @ X1)
% 3.71/3.90          | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0) @ X1)
% 3.71/3.90              != (k2_struct_0 @ X0))
% 3.71/3.90          | ~ (l1_struct_0 @ X0)
% 3.71/3.90          | (v2_struct_0 @ X0))),
% 3.71/3.90      inference('sup-', [status(thm)], ['211', '212'])).
% 3.71/3.90  thf('214', plain, ((l1_struct_0 @ sk_A)),
% 3.71/3.90      inference('sup-', [status(thm)], ['4', '5'])).
% 3.71/3.90  thf('215', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('demod', [status(thm)], ['60', '61', '63'])).
% 3.71/3.90  thf('216', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('demod', [status(thm)], ['60', '61', '63'])).
% 3.71/3.90  thf('217', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('demod', [status(thm)], ['60', '61', '63'])).
% 3.71/3.90  thf('218', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('demod', [status(thm)], ['60', '61', '63'])).
% 3.71/3.90  thf('219', plain,
% 3.71/3.90      (![X0 : $i, X1 : $i]:
% 3.71/3.90         (~ (m1_subset_1 @ X1 @ 
% 3.71/3.90             (k1_zfmisc_1 @ 
% 3.71/3.90              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ X0))))
% 3.71/3.90          | ~ (v1_funct_1 @ X1)
% 3.71/3.90          | ~ (v1_funct_2 @ X1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ X0))
% 3.71/3.90          | ((k1_relset_1 @ (u1_struct_0 @ X0) @ (k1_relat_1 @ sk_C) @ 
% 3.71/3.90              (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ X0) @ X1))
% 3.71/3.90              = (k2_struct_0 @ X0))
% 3.71/3.90          | ~ (v2_funct_1 @ X1)
% 3.71/3.90          | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ X0) @ X1)
% 3.71/3.90              != (k2_struct_0 @ X0))
% 3.71/3.90          | ~ (l1_struct_0 @ X0)
% 3.71/3.90          | (v2_struct_0 @ X0))),
% 3.71/3.90      inference('demod', [status(thm)],
% 3.71/3.90                ['213', '214', '215', '216', '217', '218'])).
% 3.71/3.90  thf('220', plain,
% 3.71/3.90      (((v2_struct_0 @ sk_B)
% 3.71/3.90        | ~ (l1_struct_0 @ sk_B)
% 3.71/3.90        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90            != (k2_struct_0 @ sk_B))
% 3.71/3.90        | ~ (v2_funct_1 @ sk_C)
% 3.71/3.90        | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 3.71/3.90            (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.71/3.90            = (k2_struct_0 @ sk_B))
% 3.71/3.90        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 3.71/3.90        | ~ (v1_funct_1 @ sk_C))),
% 3.71/3.90      inference('sup-', [status(thm)], ['210', '219'])).
% 3.71/3.90  thf('221', plain, ((l1_struct_0 @ sk_B)),
% 3.71/3.90      inference('sup-', [status(thm)], ['9', '10'])).
% 3.71/3.90  thf('222', plain,
% 3.71/3.90      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90         = (k2_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['101', '102', '103', '104', '105'])).
% 3.71/3.90  thf('223', plain, ((v2_funct_1 @ sk_C)),
% 3.71/3.90      inference('demod', [status(thm)], ['79', '80', '81', '88', '89'])).
% 3.71/3.90  thf('224', plain,
% 3.71/3.90      (![X22 : $i]:
% 3.71/3.90         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 3.71/3.90      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.71/3.90  thf('225', plain,
% 3.71/3.90      (![X22 : $i]:
% 3.71/3.90         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 3.71/3.90      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.71/3.90  thf('226', plain,
% 3.71/3.90      ((m1_subset_1 @ sk_C @ 
% 3.71/3.90        (k1_zfmisc_1 @ 
% 3.71/3.90         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('227', plain,
% 3.71/3.90      (![X24 : $i, X25 : $i, X26 : $i]:
% 3.71/3.90         (((k2_relset_1 @ X25 @ X24 @ X26) != (X24))
% 3.71/3.90          | ~ (v2_funct_1 @ X26)
% 3.71/3.90          | ((k2_tops_2 @ X25 @ X24 @ X26) = (k2_funct_1 @ X26))
% 3.71/3.90          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24)))
% 3.71/3.90          | ~ (v1_funct_2 @ X26 @ X25 @ X24)
% 3.71/3.90          | ~ (v1_funct_1 @ X26))),
% 3.71/3.90      inference('cnf', [status(esa)], [d4_tops_2])).
% 3.71/3.90  thf('228', plain,
% 3.71/3.90      ((~ (v1_funct_1 @ sk_C)
% 3.71/3.90        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.71/3.90        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90            = (k2_funct_1 @ sk_C))
% 3.71/3.90        | ~ (v2_funct_1 @ sk_C)
% 3.71/3.90        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90            != (u1_struct_0 @ sk_B)))),
% 3.71/3.90      inference('sup-', [status(thm)], ['226', '227'])).
% 3.71/3.90  thf('229', plain, ((v1_funct_1 @ sk_C)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('230', plain,
% 3.71/3.90      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('231', plain,
% 3.71/3.90      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90          = (k2_funct_1 @ sk_C))
% 3.71/3.90        | ~ (v2_funct_1 @ sk_C)
% 3.71/3.90        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90            != (u1_struct_0 @ sk_B)))),
% 3.71/3.90      inference('demod', [status(thm)], ['228', '229', '230'])).
% 3.71/3.90  thf('232', plain,
% 3.71/3.90      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90          != (u1_struct_0 @ sk_B))
% 3.71/3.90        | ~ (l1_struct_0 @ sk_A)
% 3.71/3.90        | ~ (v2_funct_1 @ sk_C)
% 3.71/3.90        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90            = (k2_funct_1 @ sk_C)))),
% 3.71/3.90      inference('sup-', [status(thm)], ['225', '231'])).
% 3.71/3.90  thf('233', plain, ((l1_struct_0 @ sk_A)),
% 3.71/3.90      inference('sup-', [status(thm)], ['4', '5'])).
% 3.71/3.90  thf('234', plain,
% 3.71/3.90      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90          != (u1_struct_0 @ sk_B))
% 3.71/3.90        | ~ (v2_funct_1 @ sk_C)
% 3.71/3.90        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90            = (k2_funct_1 @ sk_C)))),
% 3.71/3.90      inference('demod', [status(thm)], ['232', '233'])).
% 3.71/3.90  thf('235', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 3.71/3.90      inference('demod', [status(thm)],
% 3.71/3.90                ['15', '16', '17', '18', '21', '22', '23'])).
% 3.71/3.90  thf('236', plain,
% 3.71/3.90      ((((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90          != (u1_struct_0 @ sk_B))
% 3.71/3.90        | ~ (v2_funct_1 @ sk_C)
% 3.71/3.90        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90            = (k2_funct_1 @ sk_C)))),
% 3.71/3.90      inference('demod', [status(thm)], ['234', '235'])).
% 3.71/3.90  thf('237', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('demod', [status(thm)], ['60', '61', '63'])).
% 3.71/3.90  thf('238', plain,
% 3.71/3.90      ((((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90          != (u1_struct_0 @ sk_B))
% 3.71/3.90        | ~ (v2_funct_1 @ sk_C)
% 3.71/3.90        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90            = (k2_funct_1 @ sk_C)))),
% 3.71/3.90      inference('demod', [status(thm)], ['236', '237'])).
% 3.71/3.90  thf('239', plain, ((v2_funct_1 @ sk_C)),
% 3.71/3.90      inference('demod', [status(thm)], ['79', '80', '81', '88', '89'])).
% 3.71/3.90  thf('240', plain,
% 3.71/3.90      ((((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90          != (u1_struct_0 @ sk_B))
% 3.71/3.90        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90            = (k2_funct_1 @ sk_C)))),
% 3.71/3.90      inference('demod', [status(thm)], ['238', '239'])).
% 3.71/3.90  thf('241', plain,
% 3.71/3.90      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90         = (k2_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['101', '102', '103', '104', '105'])).
% 3.71/3.90  thf('242', plain,
% 3.71/3.90      ((((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B))
% 3.71/3.90        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90            = (k2_funct_1 @ sk_C)))),
% 3.71/3.90      inference('demod', [status(thm)], ['240', '241'])).
% 3.71/3.90  thf('243', plain,
% 3.71/3.90      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 3.71/3.90        | ~ (l1_struct_0 @ sk_B)
% 3.71/3.90        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90            = (k2_funct_1 @ sk_C)))),
% 3.71/3.90      inference('sup-', [status(thm)], ['224', '242'])).
% 3.71/3.90  thf('244', plain, ((l1_struct_0 @ sk_B)),
% 3.71/3.90      inference('sup-', [status(thm)], ['9', '10'])).
% 3.71/3.90  thf('245', plain,
% 3.71/3.90      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 3.71/3.90        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90            = (k2_funct_1 @ sk_C)))),
% 3.71/3.90      inference('demod', [status(thm)], ['243', '244'])).
% 3.71/3.90  thf('246', plain,
% 3.71/3.90      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90         = (k2_funct_1 @ sk_C))),
% 3.71/3.90      inference('simplify', [status(thm)], ['245'])).
% 3.71/3.90  thf('247', plain,
% 3.71/3.90      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.71/3.90        (k1_zfmisc_1 @ 
% 3.71/3.90         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 3.71/3.90      inference('simplify', [status(thm)], ['195'])).
% 3.71/3.90  thf('248', plain,
% 3.71/3.90      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.71/3.90         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 3.71/3.90          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 3.71/3.90      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.71/3.90  thf('249', plain,
% 3.71/3.90      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 3.71/3.90         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 3.71/3.90      inference('sup-', [status(thm)], ['247', '248'])).
% 3.71/3.90  thf('250', plain,
% 3.71/3.90      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['86', '87'])).
% 3.71/3.90  thf('251', plain, ((v1_funct_1 @ sk_C)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('252', plain,
% 3.71/3.90      (((v2_struct_0 @ sk_B)
% 3.71/3.90        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 3.71/3.90        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B)))),
% 3.71/3.90      inference('demod', [status(thm)],
% 3.71/3.90                ['220', '221', '222', '223', '246', '249', '250', '251'])).
% 3.71/3.90  thf('253', plain,
% 3.71/3.90      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B))
% 3.71/3.90        | (v2_struct_0 @ sk_B))),
% 3.71/3.90      inference('simplify', [status(thm)], ['252'])).
% 3.71/3.90  thf('254', plain, (~ (v2_struct_0 @ sk_B)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('255', plain,
% 3.71/3.90      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B))),
% 3.71/3.90      inference('clc', [status(thm)], ['253', '254'])).
% 3.71/3.90  thf('256', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.71/3.90      inference('simplify', [status(thm)], ['62'])).
% 3.71/3.90  thf('257', plain,
% 3.71/3.90      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B))),
% 3.71/3.90      inference('clc', [status(thm)], ['253', '254'])).
% 3.71/3.90  thf('258', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['209', '255', '256', '257'])).
% 3.71/3.90  thf('259', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('demod', [status(thm)], ['60', '61', '63'])).
% 3.71/3.90  thf('260', plain,
% 3.71/3.90      (![X30 : $i, X31 : $i, X32 : $i]:
% 3.71/3.90         ((v2_struct_0 @ X30)
% 3.71/3.90          | ~ (l1_struct_0 @ X30)
% 3.71/3.90          | ((k2_relset_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30) @ X32)
% 3.71/3.90              != (k2_struct_0 @ X30))
% 3.71/3.90          | ~ (v2_funct_1 @ X32)
% 3.71/3.90          | ((k2_relset_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X31) @ 
% 3.71/3.90              (k2_tops_2 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30) @ X32))
% 3.71/3.90              = (k2_struct_0 @ X31))
% 3.71/3.90          | ~ (m1_subset_1 @ X32 @ 
% 3.71/3.90               (k1_zfmisc_1 @ 
% 3.71/3.90                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30))))
% 3.71/3.90          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X30))
% 3.71/3.90          | ~ (v1_funct_1 @ X32)
% 3.71/3.90          | ~ (l1_struct_0 @ X31))),
% 3.71/3.90      inference('cnf', [status(esa)], [t62_tops_2])).
% 3.71/3.90  thf('261', plain,
% 3.71/3.90      (![X0 : $i, X1 : $i]:
% 3.71/3.90         (~ (m1_subset_1 @ X1 @ 
% 3.71/3.90             (k1_zfmisc_1 @ 
% 3.71/3.90              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ X0))))
% 3.71/3.90          | ~ (l1_struct_0 @ sk_A)
% 3.71/3.90          | ~ (v1_funct_1 @ X1)
% 3.71/3.90          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 3.71/3.90          | ((k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ 
% 3.71/3.90              (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0) @ X1))
% 3.71/3.90              = (k2_struct_0 @ sk_A))
% 3.71/3.90          | ~ (v2_funct_1 @ X1)
% 3.71/3.90          | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0) @ X1)
% 3.71/3.90              != (k2_struct_0 @ X0))
% 3.71/3.90          | ~ (l1_struct_0 @ X0)
% 3.71/3.90          | (v2_struct_0 @ X0))),
% 3.71/3.90      inference('sup-', [status(thm)], ['259', '260'])).
% 3.71/3.90  thf('262', plain, ((l1_struct_0 @ sk_A)),
% 3.71/3.90      inference('sup-', [status(thm)], ['4', '5'])).
% 3.71/3.90  thf('263', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('demod', [status(thm)], ['60', '61', '63'])).
% 3.71/3.90  thf('264', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('demod', [status(thm)], ['60', '61', '63'])).
% 3.71/3.90  thf('265', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('demod', [status(thm)], ['60', '61', '63'])).
% 3.71/3.90  thf('266', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 3.71/3.90      inference('demod', [status(thm)],
% 3.71/3.90                ['15', '16', '17', '18', '21', '22', '23'])).
% 3.71/3.90  thf('267', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('demod', [status(thm)], ['60', '61', '63'])).
% 3.71/3.90  thf('268', plain,
% 3.71/3.90      (![X0 : $i, X1 : $i]:
% 3.71/3.90         (~ (m1_subset_1 @ X1 @ 
% 3.71/3.90             (k1_zfmisc_1 @ 
% 3.71/3.90              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ X0))))
% 3.71/3.90          | ~ (v1_funct_1 @ X1)
% 3.71/3.90          | ~ (v1_funct_2 @ X1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ X0))
% 3.71/3.90          | ((k2_relset_1 @ (u1_struct_0 @ X0) @ (k1_relat_1 @ sk_C) @ 
% 3.71/3.90              (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ X0) @ X1))
% 3.71/3.90              = (k1_relat_1 @ sk_C))
% 3.71/3.90          | ~ (v2_funct_1 @ X1)
% 3.71/3.90          | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ X0) @ X1)
% 3.71/3.90              != (k2_struct_0 @ X0))
% 3.71/3.90          | ~ (l1_struct_0 @ X0)
% 3.71/3.90          | (v2_struct_0 @ X0))),
% 3.71/3.90      inference('demod', [status(thm)],
% 3.71/3.90                ['261', '262', '263', '264', '265', '266', '267'])).
% 3.71/3.90  thf('269', plain,
% 3.71/3.90      (![X0 : $i]:
% 3.71/3.90         (~ (m1_subset_1 @ X0 @ 
% 3.71/3.90             (k1_zfmisc_1 @ 
% 3.71/3.90              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))))
% 3.71/3.90          | (v2_struct_0 @ sk_B)
% 3.71/3.90          | ~ (l1_struct_0 @ sk_B)
% 3.71/3.90          | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ X0)
% 3.71/3.90              != (k2_struct_0 @ sk_B))
% 3.71/3.90          | ~ (v2_funct_1 @ X0)
% 3.71/3.90          | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 3.71/3.90              (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ X0))
% 3.71/3.90              = (k1_relat_1 @ sk_C))
% 3.71/3.90          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 3.71/3.90          | ~ (v1_funct_1 @ X0))),
% 3.71/3.90      inference('sup-', [status(thm)], ['258', '268'])).
% 3.71/3.90  thf('270', plain, ((l1_struct_0 @ sk_B)),
% 3.71/3.90      inference('sup-', [status(thm)], ['9', '10'])).
% 3.71/3.90  thf('271', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['209', '255', '256', '257'])).
% 3.71/3.90  thf('272', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['209', '255', '256', '257'])).
% 3.71/3.90  thf('273', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['209', '255', '256', '257'])).
% 3.71/3.90  thf('274', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['209', '255', '256', '257'])).
% 3.71/3.90  thf('275', plain,
% 3.71/3.90      (![X0 : $i]:
% 3.71/3.90         (~ (m1_subset_1 @ X0 @ 
% 3.71/3.90             (k1_zfmisc_1 @ 
% 3.71/3.90              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))))
% 3.71/3.90          | (v2_struct_0 @ sk_B)
% 3.71/3.90          | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ X0)
% 3.71/3.90              != (k2_struct_0 @ sk_B))
% 3.71/3.90          | ~ (v2_funct_1 @ X0)
% 3.71/3.90          | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 3.71/3.90              (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ X0))
% 3.71/3.90              = (k1_relat_1 @ sk_C))
% 3.71/3.90          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 3.71/3.90          | ~ (v1_funct_1 @ X0))),
% 3.71/3.90      inference('demod', [status(thm)],
% 3.71/3.90                ['269', '270', '271', '272', '273', '274'])).
% 3.71/3.90  thf('276', plain,
% 3.71/3.90      ((~ (v1_funct_1 @ sk_C)
% 3.71/3.90        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 3.71/3.90        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 3.71/3.90            (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C))
% 3.71/3.90            = (k1_relat_1 @ sk_C))
% 3.71/3.90        | ~ (v2_funct_1 @ sk_C)
% 3.71/3.90        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90            != (k2_struct_0 @ sk_B))
% 3.71/3.90        | (v2_struct_0 @ sk_B))),
% 3.71/3.90      inference('sup-', [status(thm)], ['172', '275'])).
% 3.71/3.90  thf('277', plain, ((v1_funct_1 @ sk_C)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('278', plain,
% 3.71/3.90      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['124', '125'])).
% 3.71/3.90  thf('279', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 3.71/3.90      inference('demod', [status(thm)],
% 3.71/3.90                ['15', '16', '17', '18', '21', '22', '23'])).
% 3.71/3.90  thf('280', plain,
% 3.71/3.90      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['278', '279'])).
% 3.71/3.90  thf('281', plain,
% 3.71/3.90      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90         = (k2_funct_1 @ sk_C))),
% 3.71/3.90      inference('simplify', [status(thm)], ['110'])).
% 3.71/3.90  thf('282', plain, ((v2_funct_1 @ sk_C)),
% 3.71/3.90      inference('demod', [status(thm)], ['79', '80', '81', '88', '89'])).
% 3.71/3.90  thf('283', plain,
% 3.71/3.90      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90         = (k2_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['107', '108'])).
% 3.71/3.90  thf('284', plain,
% 3.71/3.90      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 3.71/3.90          (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))
% 3.71/3.90        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 3.71/3.90        | (v2_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)],
% 3.71/3.90                ['276', '277', '280', '281', '282', '283'])).
% 3.71/3.90  thf('285', plain,
% 3.71/3.90      (((v2_struct_0 @ sk_B)
% 3.71/3.90        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 3.71/3.90            (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C)))),
% 3.71/3.90      inference('simplify', [status(thm)], ['284'])).
% 3.71/3.90  thf('286', plain, (~ (v2_struct_0 @ sk_B)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('287', plain,
% 3.71/3.90      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 3.71/3.90         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('clc', [status(thm)], ['285', '286'])).
% 3.71/3.90  thf('288', plain,
% 3.71/3.90      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 3.71/3.90          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.71/3.90        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 3.71/3.90        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))),
% 3.71/3.90      inference('demod', [status(thm)], ['169', '287'])).
% 3.71/3.90  thf('289', plain,
% 3.71/3.90      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 3.71/3.90        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 3.71/3.90            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.71/3.90      inference('simplify', [status(thm)], ['288'])).
% 3.71/3.90  thf('290', plain,
% 3.71/3.90      ((~ (v1_relat_1 @ sk_C)
% 3.71/3.90        | ~ (v1_funct_1 @ sk_C)
% 3.71/3.90        | ~ (v2_funct_1 @ sk_C)
% 3.71/3.90        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 3.71/3.90            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.71/3.90      inference('sup-', [status(thm)], ['113', '289'])).
% 3.71/3.90  thf('291', plain, ((v1_relat_1 @ sk_C)),
% 3.71/3.90      inference('sup-', [status(thm)], ['52', '53'])).
% 3.71/3.90  thf('292', plain, ((v1_funct_1 @ sk_C)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('293', plain, ((v2_funct_1 @ sk_C)),
% 3.71/3.90      inference('demod', [status(thm)], ['79', '80', '81', '88', '89'])).
% 3.71/3.90  thf('294', plain,
% 3.71/3.90      (((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 3.71/3.90         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.71/3.90      inference('demod', [status(thm)], ['290', '291', '292', '293'])).
% 3.71/3.90  thf('295', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['209', '255', '256', '257'])).
% 3.71/3.90  thf('296', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('demod', [status(thm)], ['60', '61', '63'])).
% 3.71/3.90  thf('297', plain,
% 3.71/3.90      (![X27 : $i, X28 : $i, X29 : $i]:
% 3.71/3.90         (~ (l1_pre_topc @ X27)
% 3.71/3.90          | ((k1_relset_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27) @ X28)
% 3.71/3.90              != (k2_struct_0 @ X29))
% 3.71/3.90          | ((k2_relset_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27) @ X28)
% 3.71/3.90              != (k2_struct_0 @ X27))
% 3.71/3.90          | ~ (v2_funct_1 @ X28)
% 3.71/3.90          | ~ (v5_pre_topc @ X28 @ X29 @ X27)
% 3.71/3.90          | ~ (v5_pre_topc @ 
% 3.71/3.90               (k2_tops_2 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27) @ X28) @ 
% 3.71/3.90               X27 @ X29)
% 3.71/3.90          | (v3_tops_2 @ X28 @ X29 @ X27)
% 3.71/3.90          | ~ (m1_subset_1 @ X28 @ 
% 3.71/3.90               (k1_zfmisc_1 @ 
% 3.71/3.90                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27))))
% 3.71/3.90          | ~ (v1_funct_2 @ X28 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27))
% 3.71/3.90          | ~ (v1_funct_1 @ X28)
% 3.71/3.90          | ~ (l1_pre_topc @ X29))),
% 3.71/3.90      inference('cnf', [status(esa)], [d5_tops_2])).
% 3.71/3.90  thf('298', plain,
% 3.71/3.90      (![X0 : $i, X1 : $i]:
% 3.71/3.90         (~ (m1_subset_1 @ X1 @ 
% 3.71/3.90             (k1_zfmisc_1 @ 
% 3.71/3.90              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (k1_relat_1 @ sk_C))))
% 3.71/3.90          | ~ (l1_pre_topc @ X0)
% 3.71/3.90          | ~ (v1_funct_1 @ X1)
% 3.71/3.90          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 3.71/3.90          | (v3_tops_2 @ X1 @ X0 @ sk_A)
% 3.71/3.90          | ~ (v5_pre_topc @ 
% 3.71/3.90               (k2_tops_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ X1) @ 
% 3.71/3.90               sk_A @ X0)
% 3.71/3.90          | ~ (v5_pre_topc @ X1 @ X0 @ sk_A)
% 3.71/3.90          | ~ (v2_funct_1 @ X1)
% 3.71/3.90          | ((k2_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ X1)
% 3.71/3.90              != (k2_struct_0 @ sk_A))
% 3.71/3.90          | ((k1_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A) @ X1)
% 3.71/3.90              != (k2_struct_0 @ X0))
% 3.71/3.90          | ~ (l1_pre_topc @ sk_A))),
% 3.71/3.90      inference('sup-', [status(thm)], ['296', '297'])).
% 3.71/3.90  thf('299', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('demod', [status(thm)], ['60', '61', '63'])).
% 3.71/3.90  thf('300', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('demod', [status(thm)], ['60', '61', '63'])).
% 3.71/3.90  thf('301', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('demod', [status(thm)], ['60', '61', '63'])).
% 3.71/3.90  thf('302', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 3.71/3.90      inference('demod', [status(thm)],
% 3.71/3.90                ['15', '16', '17', '18', '21', '22', '23'])).
% 3.71/3.90  thf('303', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('demod', [status(thm)], ['60', '61', '63'])).
% 3.71/3.90  thf('304', plain, ((l1_pre_topc @ sk_A)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('305', plain,
% 3.71/3.90      (![X0 : $i, X1 : $i]:
% 3.71/3.90         (~ (m1_subset_1 @ X1 @ 
% 3.71/3.90             (k1_zfmisc_1 @ 
% 3.71/3.90              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (k1_relat_1 @ sk_C))))
% 3.71/3.90          | ~ (l1_pre_topc @ X0)
% 3.71/3.90          | ~ (v1_funct_1 @ X1)
% 3.71/3.90          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (k1_relat_1 @ sk_C))
% 3.71/3.90          | (v3_tops_2 @ X1 @ X0 @ sk_A)
% 3.71/3.90          | ~ (v5_pre_topc @ 
% 3.71/3.90               (k2_tops_2 @ (u1_struct_0 @ X0) @ (k1_relat_1 @ sk_C) @ X1) @ 
% 3.71/3.90               sk_A @ X0)
% 3.71/3.90          | ~ (v5_pre_topc @ X1 @ X0 @ sk_A)
% 3.71/3.90          | ~ (v2_funct_1 @ X1)
% 3.71/3.90          | ((k2_relset_1 @ (u1_struct_0 @ X0) @ (k1_relat_1 @ sk_C) @ X1)
% 3.71/3.90              != (k1_relat_1 @ sk_C))
% 3.71/3.90          | ((k1_relset_1 @ (u1_struct_0 @ X0) @ (k1_relat_1 @ sk_C) @ X1)
% 3.71/3.90              != (k2_struct_0 @ X0)))),
% 3.71/3.90      inference('demod', [status(thm)],
% 3.71/3.90                ['298', '299', '300', '301', '302', '303', '304'])).
% 3.71/3.90  thf('306', plain,
% 3.71/3.90      (![X0 : $i]:
% 3.71/3.90         (~ (m1_subset_1 @ X0 @ 
% 3.71/3.90             (k1_zfmisc_1 @ 
% 3.71/3.90              (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 3.71/3.90          | ((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ X0)
% 3.71/3.90              != (k2_struct_0 @ sk_B))
% 3.71/3.90          | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ X0)
% 3.71/3.90              != (k1_relat_1 @ sk_C))
% 3.71/3.90          | ~ (v2_funct_1 @ X0)
% 3.71/3.90          | ~ (v5_pre_topc @ X0 @ sk_B @ sk_A)
% 3.71/3.90          | ~ (v5_pre_topc @ 
% 3.71/3.90               (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ X0) @ 
% 3.71/3.90               sk_A @ sk_B)
% 3.71/3.90          | (v3_tops_2 @ X0 @ sk_B @ sk_A)
% 3.71/3.90          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))
% 3.71/3.90          | ~ (v1_funct_1 @ X0)
% 3.71/3.90          | ~ (l1_pre_topc @ sk_B))),
% 3.71/3.90      inference('sup-', [status(thm)], ['295', '305'])).
% 3.71/3.90  thf('307', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['209', '255', '256', '257'])).
% 3.71/3.90  thf('308', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['209', '255', '256', '257'])).
% 3.71/3.90  thf('309', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['209', '255', '256', '257'])).
% 3.71/3.90  thf('310', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['209', '255', '256', '257'])).
% 3.71/3.90  thf('311', plain, ((l1_pre_topc @ sk_B)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('312', plain,
% 3.71/3.90      (![X0 : $i]:
% 3.71/3.90         (~ (m1_subset_1 @ X0 @ 
% 3.71/3.90             (k1_zfmisc_1 @ 
% 3.71/3.90              (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 3.71/3.90          | ((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ X0)
% 3.71/3.90              != (k2_struct_0 @ sk_B))
% 3.71/3.90          | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ X0)
% 3.71/3.90              != (k1_relat_1 @ sk_C))
% 3.71/3.90          | ~ (v2_funct_1 @ X0)
% 3.71/3.90          | ~ (v5_pre_topc @ X0 @ sk_B @ sk_A)
% 3.71/3.90          | ~ (v5_pre_topc @ 
% 3.71/3.90               (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ X0) @ 
% 3.71/3.90               sk_A @ sk_B)
% 3.71/3.90          | (v3_tops_2 @ X0 @ sk_B @ sk_A)
% 3.71/3.90          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))
% 3.71/3.90          | ~ (v1_funct_1 @ X0))),
% 3.71/3.90      inference('demod', [status(thm)],
% 3.71/3.90                ['306', '307', '308', '309', '310', '311'])).
% 3.71/3.90  thf('313', plain,
% 3.71/3.90      ((~ (v5_pre_topc @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_A @ sk_B)
% 3.71/3.90        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.71/3.90        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.71/3.90             (k1_relat_1 @ sk_C))
% 3.71/3.90        | (v3_tops_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 3.71/3.90        | ~ (v5_pre_topc @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 3.71/3.90        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 3.71/3.90        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 3.71/3.90            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 3.71/3.90        | ((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 3.71/3.90            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_B))
% 3.71/3.90        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.71/3.90             (k1_zfmisc_1 @ 
% 3.71/3.90              (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 3.71/3.90      inference('sup-', [status(thm)], ['294', '312'])).
% 3.71/3.90  thf(t65_funct_1, axiom,
% 3.71/3.90    (![A:$i]:
% 3.71/3.90     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.71/3.90       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 3.71/3.90  thf('314', plain,
% 3.71/3.90      (![X9 : $i]:
% 3.71/3.90         (~ (v2_funct_1 @ X9)
% 3.71/3.90          | ((k2_funct_1 @ (k2_funct_1 @ X9)) = (X9))
% 3.71/3.90          | ~ (v1_funct_1 @ X9)
% 3.71/3.90          | ~ (v1_relat_1 @ X9))),
% 3.71/3.90      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.71/3.90  thf('315', plain,
% 3.71/3.90      (![X8 : $i]:
% 3.71/3.90         ((v2_funct_1 @ (k2_funct_1 @ X8))
% 3.71/3.90          | ~ (v2_funct_1 @ X8)
% 3.71/3.90          | ~ (v1_funct_1 @ X8)
% 3.71/3.90          | ~ (v1_relat_1 @ X8))),
% 3.71/3.90      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.71/3.90  thf('316', plain,
% 3.71/3.90      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.71/3.90        (k1_zfmisc_1 @ 
% 3.71/3.90         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 3.71/3.90      inference('simplify', [status(thm)], ['134'])).
% 3.71/3.90  thf('317', plain,
% 3.71/3.90      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.71/3.90         (~ (v2_funct_1 @ X19)
% 3.71/3.90          | ((k2_relset_1 @ X21 @ X20 @ X19) != (X20))
% 3.71/3.90          | (m1_subset_1 @ (k2_funct_1 @ X19) @ 
% 3.71/3.90             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 3.71/3.90          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20)))
% 3.71/3.90          | ~ (v1_funct_2 @ X19 @ X21 @ X20)
% 3.71/3.90          | ~ (v1_funct_1 @ X19))),
% 3.71/3.90      inference('cnf', [status(esa)], [t31_funct_2])).
% 3.71/3.90  thf('318', plain,
% 3.71/3.90      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.71/3.90        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.71/3.90             (k1_relat_1 @ sk_C))
% 3.71/3.90        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.71/3.90           (k1_zfmisc_1 @ 
% 3.71/3.90            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))))
% 3.71/3.90        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 3.71/3.90            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 3.71/3.90        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.71/3.90      inference('sup-', [status(thm)], ['316', '317'])).
% 3.71/3.90  thf('319', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 3.71/3.90      inference('simplify', [status(thm)], ['153'])).
% 3.71/3.90  thf('320', plain,
% 3.71/3.90      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.71/3.90        (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('simplify', [status(thm)], ['167'])).
% 3.71/3.90  thf('321', plain,
% 3.71/3.90      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.71/3.90         (k1_zfmisc_1 @ 
% 3.71/3.90          (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))))
% 3.71/3.90        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 3.71/3.90            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 3.71/3.90        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.71/3.90      inference('demod', [status(thm)], ['318', '319', '320'])).
% 3.71/3.90  thf('322', plain,
% 3.71/3.90      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 3.71/3.90         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('clc', [status(thm)], ['285', '286'])).
% 3.71/3.90  thf('323', plain,
% 3.71/3.90      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.71/3.90         (k1_zfmisc_1 @ 
% 3.71/3.90          (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))))
% 3.71/3.90        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 3.71/3.90        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.71/3.90      inference('demod', [status(thm)], ['321', '322'])).
% 3.71/3.90  thf('324', plain,
% 3.71/3.90      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 3.71/3.90        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.71/3.90           (k1_zfmisc_1 @ 
% 3.71/3.90            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B)))))),
% 3.71/3.90      inference('simplify', [status(thm)], ['323'])).
% 3.71/3.90  thf('325', plain,
% 3.71/3.90      ((~ (v1_relat_1 @ sk_C)
% 3.71/3.90        | ~ (v1_funct_1 @ sk_C)
% 3.71/3.90        | ~ (v2_funct_1 @ sk_C)
% 3.71/3.90        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.71/3.90           (k1_zfmisc_1 @ 
% 3.71/3.90            (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B)))))),
% 3.71/3.90      inference('sup-', [status(thm)], ['315', '324'])).
% 3.71/3.90  thf('326', plain, ((v1_relat_1 @ sk_C)),
% 3.71/3.90      inference('sup-', [status(thm)], ['52', '53'])).
% 3.71/3.90  thf('327', plain, ((v1_funct_1 @ sk_C)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('328', plain, ((v2_funct_1 @ sk_C)),
% 3.71/3.90      inference('demod', [status(thm)], ['79', '80', '81', '88', '89'])).
% 3.71/3.90  thf('329', plain,
% 3.71/3.90      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.71/3.90        (k1_zfmisc_1 @ 
% 3.71/3.90         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))))),
% 3.71/3.90      inference('demod', [status(thm)], ['325', '326', '327', '328'])).
% 3.71/3.90  thf('330', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('demod', [status(thm)], ['60', '61', '63'])).
% 3.71/3.90  thf('331', plain,
% 3.71/3.90      (![X22 : $i]:
% 3.71/3.90         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 3.71/3.90      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.71/3.90  thf('332', plain,
% 3.71/3.90      (![X27 : $i, X28 : $i, X29 : $i]:
% 3.71/3.90         (~ (l1_pre_topc @ X27)
% 3.71/3.90          | ~ (v3_tops_2 @ X28 @ X29 @ X27)
% 3.71/3.90          | (v5_pre_topc @ X28 @ X29 @ X27)
% 3.71/3.90          | ~ (m1_subset_1 @ X28 @ 
% 3.71/3.90               (k1_zfmisc_1 @ 
% 3.71/3.90                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27))))
% 3.71/3.90          | ~ (v1_funct_2 @ X28 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27))
% 3.71/3.90          | ~ (v1_funct_1 @ X28)
% 3.71/3.90          | ~ (l1_pre_topc @ X29))),
% 3.71/3.90      inference('cnf', [status(esa)], [d5_tops_2])).
% 3.71/3.90  thf('333', plain,
% 3.71/3.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.71/3.90         (~ (m1_subset_1 @ X2 @ 
% 3.71/3.90             (k1_zfmisc_1 @ 
% 3.71/3.90              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (k2_struct_0 @ X0))))
% 3.71/3.90          | ~ (l1_struct_0 @ X0)
% 3.71/3.90          | ~ (l1_pre_topc @ X1)
% 3.71/3.90          | ~ (v1_funct_1 @ X2)
% 3.71/3.90          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 3.71/3.90          | (v5_pre_topc @ X2 @ X1 @ X0)
% 3.71/3.90          | ~ (v3_tops_2 @ X2 @ X1 @ X0)
% 3.71/3.90          | ~ (l1_pre_topc @ X0))),
% 3.71/3.90      inference('sup-', [status(thm)], ['331', '332'])).
% 3.71/3.90  thf('334', plain,
% 3.71/3.90      (![X0 : $i, X1 : $i]:
% 3.71/3.90         (~ (m1_subset_1 @ X1 @ 
% 3.71/3.90             (k1_zfmisc_1 @ 
% 3.71/3.90              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ X0))))
% 3.71/3.90          | ~ (l1_pre_topc @ X0)
% 3.71/3.90          | ~ (v3_tops_2 @ X1 @ sk_A @ X0)
% 3.71/3.90          | (v5_pre_topc @ X1 @ sk_A @ X0)
% 3.71/3.90          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 3.71/3.90          | ~ (v1_funct_1 @ X1)
% 3.71/3.90          | ~ (l1_pre_topc @ sk_A)
% 3.71/3.90          | ~ (l1_struct_0 @ X0))),
% 3.71/3.90      inference('sup-', [status(thm)], ['330', '333'])).
% 3.71/3.90  thf('335', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('demod', [status(thm)], ['60', '61', '63'])).
% 3.71/3.90  thf('336', plain, ((l1_pre_topc @ sk_A)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('337', plain,
% 3.71/3.90      (![X0 : $i, X1 : $i]:
% 3.71/3.90         (~ (m1_subset_1 @ X1 @ 
% 3.71/3.90             (k1_zfmisc_1 @ 
% 3.71/3.90              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ X0))))
% 3.71/3.90          | ~ (l1_pre_topc @ X0)
% 3.71/3.90          | ~ (v3_tops_2 @ X1 @ sk_A @ X0)
% 3.71/3.90          | (v5_pre_topc @ X1 @ sk_A @ X0)
% 3.71/3.90          | ~ (v1_funct_2 @ X1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ X0))
% 3.71/3.90          | ~ (v1_funct_1 @ X1)
% 3.71/3.90          | ~ (l1_struct_0 @ X0))),
% 3.71/3.90      inference('demod', [status(thm)], ['334', '335', '336'])).
% 3.71/3.90  thf('338', plain,
% 3.71/3.90      ((~ (l1_struct_0 @ sk_B)
% 3.71/3.90        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.71/3.90        | ~ (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.71/3.90             (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 3.71/3.90        | (v5_pre_topc @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_A @ sk_B)
% 3.71/3.90        | ~ (v3_tops_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_A @ sk_B)
% 3.71/3.90        | ~ (l1_pre_topc @ sk_B))),
% 3.71/3.90      inference('sup-', [status(thm)], ['329', '337'])).
% 3.71/3.90  thf('339', plain, ((l1_struct_0 @ sk_B)),
% 3.71/3.90      inference('sup-', [status(thm)], ['9', '10'])).
% 3.71/3.90  thf('340', plain,
% 3.71/3.90      (![X8 : $i]:
% 3.71/3.90         ((v2_funct_1 @ (k2_funct_1 @ X8))
% 3.71/3.90          | ~ (v2_funct_1 @ X8)
% 3.71/3.90          | ~ (v1_funct_1 @ X8)
% 3.71/3.90          | ~ (v1_relat_1 @ X8))),
% 3.71/3.90      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.71/3.90  thf('341', plain,
% 3.71/3.90      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.71/3.90        (k1_zfmisc_1 @ 
% 3.71/3.90         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 3.71/3.90      inference('simplify', [status(thm)], ['134'])).
% 3.71/3.90  thf('342', plain,
% 3.71/3.90      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.71/3.90         (~ (v2_funct_1 @ X19)
% 3.71/3.90          | ((k2_relset_1 @ X21 @ X20 @ X19) != (X20))
% 3.71/3.90          | (v1_funct_1 @ (k2_funct_1 @ X19))
% 3.71/3.90          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20)))
% 3.71/3.90          | ~ (v1_funct_2 @ X19 @ X21 @ X20)
% 3.71/3.90          | ~ (v1_funct_1 @ X19))),
% 3.71/3.90      inference('cnf', [status(esa)], [t31_funct_2])).
% 3.71/3.90  thf('343', plain,
% 3.71/3.90      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.71/3.90        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.71/3.90             (k1_relat_1 @ sk_C))
% 3.71/3.90        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.71/3.90        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 3.71/3.90            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 3.71/3.90        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.71/3.90      inference('sup-', [status(thm)], ['341', '342'])).
% 3.71/3.90  thf('344', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 3.71/3.90      inference('simplify', [status(thm)], ['153'])).
% 3.71/3.90  thf('345', plain,
% 3.71/3.90      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.71/3.90        (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('simplify', [status(thm)], ['167'])).
% 3.71/3.90  thf('346', plain,
% 3.71/3.90      (((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.71/3.90        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 3.71/3.90            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 3.71/3.90        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.71/3.90      inference('demod', [status(thm)], ['343', '344', '345'])).
% 3.71/3.90  thf('347', plain,
% 3.71/3.90      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 3.71/3.90         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('clc', [status(thm)], ['285', '286'])).
% 3.71/3.90  thf('348', plain,
% 3.71/3.90      (((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.71/3.90        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 3.71/3.90        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.71/3.90      inference('demod', [status(thm)], ['346', '347'])).
% 3.71/3.90  thf('349', plain,
% 3.71/3.90      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 3.71/3.90        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.71/3.90      inference('simplify', [status(thm)], ['348'])).
% 3.71/3.90  thf('350', plain,
% 3.71/3.90      ((~ (v1_relat_1 @ sk_C)
% 3.71/3.90        | ~ (v1_funct_1 @ sk_C)
% 3.71/3.90        | ~ (v2_funct_1 @ sk_C)
% 3.71/3.90        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.71/3.90      inference('sup-', [status(thm)], ['340', '349'])).
% 3.71/3.90  thf('351', plain, ((v1_relat_1 @ sk_C)),
% 3.71/3.90      inference('sup-', [status(thm)], ['52', '53'])).
% 3.71/3.90  thf('352', plain, ((v1_funct_1 @ sk_C)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('353', plain, ((v2_funct_1 @ sk_C)),
% 3.71/3.90      inference('demod', [status(thm)], ['79', '80', '81', '88', '89'])).
% 3.71/3.90  thf('354', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.71/3.90      inference('demod', [status(thm)], ['350', '351', '352', '353'])).
% 3.71/3.90  thf('355', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['209', '255', '256', '257'])).
% 3.71/3.90  thf('356', plain,
% 3.71/3.90      (![X8 : $i]:
% 3.71/3.90         ((v2_funct_1 @ (k2_funct_1 @ X8))
% 3.71/3.90          | ~ (v2_funct_1 @ X8)
% 3.71/3.90          | ~ (v1_funct_1 @ X8)
% 3.71/3.90          | ~ (v1_relat_1 @ X8))),
% 3.71/3.90      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.71/3.90  thf('357', plain,
% 3.71/3.90      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.71/3.90        (k1_zfmisc_1 @ 
% 3.71/3.90         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 3.71/3.90      inference('simplify', [status(thm)], ['134'])).
% 3.71/3.90  thf('358', plain,
% 3.71/3.90      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.71/3.90         (~ (v2_funct_1 @ X19)
% 3.71/3.90          | ((k2_relset_1 @ X21 @ X20 @ X19) != (X20))
% 3.71/3.90          | (v1_funct_2 @ (k2_funct_1 @ X19) @ X20 @ X21)
% 3.71/3.90          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20)))
% 3.71/3.90          | ~ (v1_funct_2 @ X19 @ X21 @ X20)
% 3.71/3.90          | ~ (v1_funct_1 @ X19))),
% 3.71/3.90      inference('cnf', [status(esa)], [t31_funct_2])).
% 3.71/3.90  thf('359', plain,
% 3.71/3.90      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.71/3.90        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.71/3.90             (k1_relat_1 @ sk_C))
% 3.71/3.90        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.71/3.90           (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 3.71/3.90        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 3.71/3.90            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 3.71/3.90        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.71/3.90      inference('sup-', [status(thm)], ['357', '358'])).
% 3.71/3.90  thf('360', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 3.71/3.90      inference('simplify', [status(thm)], ['153'])).
% 3.71/3.90  thf('361', plain,
% 3.71/3.90      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.71/3.90        (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('simplify', [status(thm)], ['167'])).
% 3.71/3.90  thf('362', plain,
% 3.71/3.90      (((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.71/3.90         (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 3.71/3.90        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 3.71/3.90            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 3.71/3.90        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.71/3.90      inference('demod', [status(thm)], ['359', '360', '361'])).
% 3.71/3.90  thf('363', plain,
% 3.71/3.90      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 3.71/3.90         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('clc', [status(thm)], ['285', '286'])).
% 3.71/3.90  thf('364', plain,
% 3.71/3.90      (((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.71/3.90         (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 3.71/3.90        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 3.71/3.90        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.71/3.90      inference('demod', [status(thm)], ['362', '363'])).
% 3.71/3.90  thf('365', plain,
% 3.71/3.90      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 3.71/3.90        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.71/3.90           (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B)))),
% 3.71/3.90      inference('simplify', [status(thm)], ['364'])).
% 3.71/3.90  thf('366', plain,
% 3.71/3.90      ((~ (v1_relat_1 @ sk_C)
% 3.71/3.90        | ~ (v1_funct_1 @ sk_C)
% 3.71/3.90        | ~ (v2_funct_1 @ sk_C)
% 3.71/3.90        | (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.71/3.90           (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B)))),
% 3.71/3.90      inference('sup-', [status(thm)], ['356', '365'])).
% 3.71/3.90  thf('367', plain, ((v1_relat_1 @ sk_C)),
% 3.71/3.90      inference('sup-', [status(thm)], ['52', '53'])).
% 3.71/3.90  thf('368', plain, ((v1_funct_1 @ sk_C)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('369', plain, ((v2_funct_1 @ sk_C)),
% 3.71/3.90      inference('demod', [status(thm)], ['79', '80', '81', '88', '89'])).
% 3.71/3.90  thf('370', plain,
% 3.71/3.90      ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.71/3.90        (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['366', '367', '368', '369'])).
% 3.71/3.90  thf('371', plain, ((l1_pre_topc @ sk_B)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('372', plain,
% 3.71/3.90      (((v5_pre_topc @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_A @ sk_B)
% 3.71/3.90        | ~ (v3_tops_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_A @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)],
% 3.71/3.90                ['338', '339', '354', '355', '370', '371'])).
% 3.71/3.90  thf('373', plain,
% 3.71/3.90      ((~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 3.71/3.90        | ~ (v1_relat_1 @ sk_C)
% 3.71/3.90        | ~ (v1_funct_1 @ sk_C)
% 3.71/3.90        | ~ (v2_funct_1 @ sk_C)
% 3.71/3.90        | (v5_pre_topc @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_A @ sk_B))),
% 3.71/3.90      inference('sup-', [status(thm)], ['314', '372'])).
% 3.71/3.90  thf('374', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('375', plain, ((v1_relat_1 @ sk_C)),
% 3.71/3.90      inference('sup-', [status(thm)], ['52', '53'])).
% 3.71/3.90  thf('376', plain, ((v1_funct_1 @ sk_C)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('377', plain, ((v2_funct_1 @ sk_C)),
% 3.71/3.90      inference('demod', [status(thm)], ['79', '80', '81', '88', '89'])).
% 3.71/3.90  thf('378', plain,
% 3.71/3.90      ((v5_pre_topc @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_A @ sk_B)),
% 3.71/3.90      inference('demod', [status(thm)], ['373', '374', '375', '376', '377'])).
% 3.71/3.90  thf('379', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 3.71/3.90      inference('simplify', [status(thm)], ['153'])).
% 3.71/3.90  thf('380', plain,
% 3.71/3.90      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.71/3.90        (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('simplify', [status(thm)], ['167'])).
% 3.71/3.90  thf('381', plain,
% 3.71/3.90      ((m1_subset_1 @ sk_C @ 
% 3.71/3.90        (k1_zfmisc_1 @ 
% 3.71/3.90         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 3.71/3.90      inference('demod', [status(thm)], ['70', '71'])).
% 3.71/3.90  thf('382', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('demod', [status(thm)], ['60', '61', '63'])).
% 3.71/3.90  thf('383', plain,
% 3.71/3.90      (![X27 : $i, X28 : $i, X29 : $i]:
% 3.71/3.90         (~ (l1_pre_topc @ X27)
% 3.71/3.90          | ~ (v3_tops_2 @ X28 @ X29 @ X27)
% 3.71/3.90          | (v5_pre_topc @ 
% 3.71/3.90             (k2_tops_2 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27) @ X28) @ 
% 3.71/3.90             X27 @ X29)
% 3.71/3.90          | ~ (m1_subset_1 @ X28 @ 
% 3.71/3.90               (k1_zfmisc_1 @ 
% 3.71/3.90                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27))))
% 3.71/3.90          | ~ (v1_funct_2 @ X28 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27))
% 3.71/3.90          | ~ (v1_funct_1 @ X28)
% 3.71/3.90          | ~ (l1_pre_topc @ X29))),
% 3.71/3.90      inference('cnf', [status(esa)], [d5_tops_2])).
% 3.71/3.90  thf('384', plain,
% 3.71/3.90      (![X0 : $i, X1 : $i]:
% 3.71/3.90         (~ (m1_subset_1 @ X1 @ 
% 3.71/3.90             (k1_zfmisc_1 @ 
% 3.71/3.90              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ X0))))
% 3.71/3.90          | ~ (l1_pre_topc @ sk_A)
% 3.71/3.90          | ~ (v1_funct_1 @ X1)
% 3.71/3.90          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 3.71/3.90          | (v5_pre_topc @ 
% 3.71/3.90             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0) @ X1) @ 
% 3.71/3.90             X0 @ sk_A)
% 3.71/3.90          | ~ (v3_tops_2 @ X1 @ sk_A @ X0)
% 3.71/3.90          | ~ (l1_pre_topc @ X0))),
% 3.71/3.90      inference('sup-', [status(thm)], ['382', '383'])).
% 3.71/3.90  thf('385', plain, ((l1_pre_topc @ sk_A)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('386', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('demod', [status(thm)], ['60', '61', '63'])).
% 3.71/3.90  thf('387', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('demod', [status(thm)], ['60', '61', '63'])).
% 3.71/3.90  thf('388', plain,
% 3.71/3.90      (![X0 : $i, X1 : $i]:
% 3.71/3.90         (~ (m1_subset_1 @ X1 @ 
% 3.71/3.90             (k1_zfmisc_1 @ 
% 3.71/3.90              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ X0))))
% 3.71/3.90          | ~ (v1_funct_1 @ X1)
% 3.71/3.90          | ~ (v1_funct_2 @ X1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ X0))
% 3.71/3.90          | (v5_pre_topc @ 
% 3.71/3.90             (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ X0) @ X1) @ 
% 3.71/3.90             X0 @ sk_A)
% 3.71/3.90          | ~ (v3_tops_2 @ X1 @ sk_A @ X0)
% 3.71/3.90          | ~ (l1_pre_topc @ X0))),
% 3.71/3.90      inference('demod', [status(thm)], ['384', '385', '386', '387'])).
% 3.71/3.90  thf('389', plain,
% 3.71/3.90      ((~ (l1_pre_topc @ sk_B)
% 3.71/3.90        | ~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 3.71/3.90        | (v5_pre_topc @ 
% 3.71/3.90           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 3.71/3.90           sk_B @ sk_A)
% 3.71/3.90        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 3.71/3.90        | ~ (v1_funct_1 @ sk_C))),
% 3.71/3.90      inference('sup-', [status(thm)], ['381', '388'])).
% 3.71/3.90  thf('390', plain, ((l1_pre_topc @ sk_B)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('391', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('392', plain,
% 3.71/3.90      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90         = (k2_funct_1 @ sk_C))),
% 3.71/3.90      inference('simplify', [status(thm)], ['245'])).
% 3.71/3.90  thf('393', plain,
% 3.71/3.90      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['86', '87'])).
% 3.71/3.90  thf('394', plain, ((v1_funct_1 @ sk_C)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('395', plain, ((v5_pre_topc @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 3.71/3.90      inference('demod', [status(thm)],
% 3.71/3.90                ['389', '390', '391', '392', '393', '394'])).
% 3.71/3.90  thf('396', plain,
% 3.71/3.90      (![X9 : $i]:
% 3.71/3.90         (~ (v2_funct_1 @ X9)
% 3.71/3.90          | ((k2_funct_1 @ (k2_funct_1 @ X9)) = (X9))
% 3.71/3.90          | ~ (v1_funct_1 @ X9)
% 3.71/3.90          | ~ (v1_relat_1 @ X9))),
% 3.71/3.90      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.71/3.90  thf('397', plain,
% 3.71/3.90      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.71/3.90        (k1_zfmisc_1 @ 
% 3.71/3.90         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))))),
% 3.71/3.90      inference('demod', [status(thm)], ['325', '326', '327', '328'])).
% 3.71/3.90  thf('398', plain,
% 3.71/3.90      (![X24 : $i, X25 : $i, X26 : $i]:
% 3.71/3.90         (((k2_relset_1 @ X25 @ X24 @ X26) != (X24))
% 3.71/3.90          | ~ (v2_funct_1 @ X26)
% 3.71/3.90          | ((k2_tops_2 @ X25 @ X24 @ X26) = (k2_funct_1 @ X26))
% 3.71/3.90          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24)))
% 3.71/3.90          | ~ (v1_funct_2 @ X26 @ X25 @ X24)
% 3.71/3.90          | ~ (v1_funct_1 @ X26))),
% 3.71/3.90      inference('cnf', [status(esa)], [d4_tops_2])).
% 3.71/3.90  thf('399', plain,
% 3.71/3.90      ((~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.71/3.90        | ~ (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.71/3.90             (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 3.71/3.90        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.71/3.90            (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.71/3.90            = (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 3.71/3.90        | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.71/3.90        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.71/3.90            (k2_funct_1 @ (k2_funct_1 @ sk_C))) != (k2_struct_0 @ sk_B)))),
% 3.71/3.90      inference('sup-', [status(thm)], ['397', '398'])).
% 3.71/3.90  thf('400', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.71/3.90      inference('demod', [status(thm)], ['350', '351', '352', '353'])).
% 3.71/3.90  thf('401', plain,
% 3.71/3.90      ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.71/3.90        (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['366', '367', '368', '369'])).
% 3.71/3.90  thf('402', plain,
% 3.71/3.90      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.71/3.90          (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.71/3.90          = (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 3.71/3.90        | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.71/3.90        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.71/3.90            (k2_funct_1 @ (k2_funct_1 @ sk_C))) != (k2_struct_0 @ sk_B)))),
% 3.71/3.90      inference('demod', [status(thm)], ['399', '400', '401'])).
% 3.71/3.90  thf('403', plain,
% 3.71/3.90      (![X9 : $i]:
% 3.71/3.90         (~ (v2_funct_1 @ X9)
% 3.71/3.90          | ((k2_funct_1 @ (k2_funct_1 @ X9)) = (X9))
% 3.71/3.90          | ~ (v1_funct_1 @ X9)
% 3.71/3.90          | ~ (v1_relat_1 @ X9))),
% 3.71/3.90      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.71/3.90  thf('404', plain,
% 3.71/3.90      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.71/3.90        (k1_zfmisc_1 @ 
% 3.71/3.90         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))))),
% 3.71/3.90      inference('demod', [status(thm)], ['325', '326', '327', '328'])).
% 3.71/3.90  thf('405', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('demod', [status(thm)], ['60', '61', '63'])).
% 3.71/3.90  thf('406', plain,
% 3.71/3.90      (![X22 : $i]:
% 3.71/3.90         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 3.71/3.90      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.71/3.90  thf('407', plain,
% 3.71/3.90      (![X27 : $i, X28 : $i, X29 : $i]:
% 3.71/3.90         (~ (l1_pre_topc @ X27)
% 3.71/3.90          | ~ (v3_tops_2 @ X28 @ X29 @ X27)
% 3.71/3.90          | (v2_funct_1 @ X28)
% 3.71/3.90          | ~ (m1_subset_1 @ X28 @ 
% 3.71/3.90               (k1_zfmisc_1 @ 
% 3.71/3.90                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27))))
% 3.71/3.90          | ~ (v1_funct_2 @ X28 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27))
% 3.71/3.90          | ~ (v1_funct_1 @ X28)
% 3.71/3.90          | ~ (l1_pre_topc @ X29))),
% 3.71/3.90      inference('cnf', [status(esa)], [d5_tops_2])).
% 3.71/3.90  thf('408', plain,
% 3.71/3.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.71/3.90         (~ (m1_subset_1 @ X2 @ 
% 3.71/3.90             (k1_zfmisc_1 @ 
% 3.71/3.90              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (k2_struct_0 @ X0))))
% 3.71/3.90          | ~ (l1_struct_0 @ X0)
% 3.71/3.90          | ~ (l1_pre_topc @ X1)
% 3.71/3.90          | ~ (v1_funct_1 @ X2)
% 3.71/3.90          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 3.71/3.90          | (v2_funct_1 @ X2)
% 3.71/3.90          | ~ (v3_tops_2 @ X2 @ X1 @ X0)
% 3.71/3.90          | ~ (l1_pre_topc @ X0))),
% 3.71/3.90      inference('sup-', [status(thm)], ['406', '407'])).
% 3.71/3.90  thf('409', plain,
% 3.71/3.90      (![X0 : $i, X1 : $i]:
% 3.71/3.90         (~ (m1_subset_1 @ X1 @ 
% 3.71/3.90             (k1_zfmisc_1 @ 
% 3.71/3.90              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ X0))))
% 3.71/3.90          | ~ (l1_pre_topc @ X0)
% 3.71/3.90          | ~ (v3_tops_2 @ X1 @ sk_A @ X0)
% 3.71/3.90          | (v2_funct_1 @ X1)
% 3.71/3.90          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 3.71/3.90          | ~ (v1_funct_1 @ X1)
% 3.71/3.90          | ~ (l1_pre_topc @ sk_A)
% 3.71/3.90          | ~ (l1_struct_0 @ X0))),
% 3.71/3.90      inference('sup-', [status(thm)], ['405', '408'])).
% 3.71/3.90  thf('410', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('demod', [status(thm)], ['60', '61', '63'])).
% 3.71/3.90  thf('411', plain, ((l1_pre_topc @ sk_A)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('412', plain,
% 3.71/3.90      (![X0 : $i, X1 : $i]:
% 3.71/3.90         (~ (m1_subset_1 @ X1 @ 
% 3.71/3.90             (k1_zfmisc_1 @ 
% 3.71/3.90              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ X0))))
% 3.71/3.90          | ~ (l1_pre_topc @ X0)
% 3.71/3.90          | ~ (v3_tops_2 @ X1 @ sk_A @ X0)
% 3.71/3.90          | (v2_funct_1 @ X1)
% 3.71/3.90          | ~ (v1_funct_2 @ X1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ X0))
% 3.71/3.90          | ~ (v1_funct_1 @ X1)
% 3.71/3.90          | ~ (l1_struct_0 @ X0))),
% 3.71/3.90      inference('demod', [status(thm)], ['409', '410', '411'])).
% 3.71/3.90  thf('413', plain,
% 3.71/3.90      ((~ (l1_struct_0 @ sk_B)
% 3.71/3.90        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.71/3.90        | ~ (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.71/3.90             (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 3.71/3.90        | (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.71/3.90        | ~ (v3_tops_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_A @ sk_B)
% 3.71/3.90        | ~ (l1_pre_topc @ sk_B))),
% 3.71/3.90      inference('sup-', [status(thm)], ['404', '412'])).
% 3.71/3.90  thf('414', plain, ((l1_struct_0 @ sk_B)),
% 3.71/3.90      inference('sup-', [status(thm)], ['9', '10'])).
% 3.71/3.90  thf('415', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.71/3.90      inference('demod', [status(thm)], ['350', '351', '352', '353'])).
% 3.71/3.90  thf('416', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['209', '255', '256', '257'])).
% 3.71/3.90  thf('417', plain,
% 3.71/3.90      ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.71/3.90        (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['366', '367', '368', '369'])).
% 3.71/3.90  thf('418', plain, ((l1_pre_topc @ sk_B)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('419', plain,
% 3.71/3.90      (((v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.71/3.90        | ~ (v3_tops_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_A @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)],
% 3.71/3.90                ['413', '414', '415', '416', '417', '418'])).
% 3.71/3.90  thf('420', plain,
% 3.71/3.90      ((~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 3.71/3.90        | ~ (v1_relat_1 @ sk_C)
% 3.71/3.90        | ~ (v1_funct_1 @ sk_C)
% 3.71/3.90        | ~ (v2_funct_1 @ sk_C)
% 3.71/3.90        | (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.71/3.90      inference('sup-', [status(thm)], ['403', '419'])).
% 3.71/3.90  thf('421', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('422', plain, ((v1_relat_1 @ sk_C)),
% 3.71/3.90      inference('sup-', [status(thm)], ['52', '53'])).
% 3.71/3.90  thf('423', plain, ((v1_funct_1 @ sk_C)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('424', plain, ((v2_funct_1 @ sk_C)),
% 3.71/3.90      inference('demod', [status(thm)], ['79', '80', '81', '88', '89'])).
% 3.71/3.90  thf('425', plain, ((v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.71/3.90      inference('demod', [status(thm)], ['420', '421', '422', '423', '424'])).
% 3.71/3.90  thf('426', plain,
% 3.71/3.90      (![X9 : $i]:
% 3.71/3.90         (~ (v2_funct_1 @ X9)
% 3.71/3.90          | ((k2_funct_1 @ (k2_funct_1 @ X9)) = (X9))
% 3.71/3.90          | ~ (v1_funct_1 @ X9)
% 3.71/3.90          | ~ (v1_relat_1 @ X9))),
% 3.71/3.90      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.71/3.90  thf('427', plain,
% 3.71/3.90      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.71/3.90        (k1_zfmisc_1 @ 
% 3.71/3.90         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))))),
% 3.71/3.90      inference('demod', [status(thm)], ['325', '326', '327', '328'])).
% 3.71/3.90  thf('428', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('demod', [status(thm)], ['60', '61', '63'])).
% 3.71/3.90  thf('429', plain,
% 3.71/3.90      (![X22 : $i]:
% 3.71/3.90         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 3.71/3.90      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.71/3.90  thf('430', plain,
% 3.71/3.90      (![X27 : $i, X28 : $i, X29 : $i]:
% 3.71/3.90         (~ (l1_pre_topc @ X27)
% 3.71/3.90          | ~ (v3_tops_2 @ X28 @ X29 @ X27)
% 3.71/3.90          | ((k2_relset_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27) @ X28)
% 3.71/3.90              = (k2_struct_0 @ X27))
% 3.71/3.90          | ~ (m1_subset_1 @ X28 @ 
% 3.71/3.90               (k1_zfmisc_1 @ 
% 3.71/3.90                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27))))
% 3.71/3.90          | ~ (v1_funct_2 @ X28 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27))
% 3.71/3.90          | ~ (v1_funct_1 @ X28)
% 3.71/3.90          | ~ (l1_pre_topc @ X29))),
% 3.71/3.90      inference('cnf', [status(esa)], [d5_tops_2])).
% 3.71/3.90  thf('431', plain,
% 3.71/3.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.71/3.90         (~ (m1_subset_1 @ X2 @ 
% 3.71/3.90             (k1_zfmisc_1 @ 
% 3.71/3.90              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (k2_struct_0 @ X0))))
% 3.71/3.90          | ~ (l1_struct_0 @ X0)
% 3.71/3.90          | ~ (l1_pre_topc @ X1)
% 3.71/3.90          | ~ (v1_funct_1 @ X2)
% 3.71/3.90          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 3.71/3.90          | ((k2_relset_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ X2)
% 3.71/3.90              = (k2_struct_0 @ X0))
% 3.71/3.90          | ~ (v3_tops_2 @ X2 @ X1 @ X0)
% 3.71/3.90          | ~ (l1_pre_topc @ X0))),
% 3.71/3.90      inference('sup-', [status(thm)], ['429', '430'])).
% 3.71/3.90  thf('432', plain,
% 3.71/3.90      (![X0 : $i, X1 : $i]:
% 3.71/3.90         (~ (m1_subset_1 @ X1 @ 
% 3.71/3.90             (k1_zfmisc_1 @ 
% 3.71/3.90              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ X0))))
% 3.71/3.90          | ~ (l1_pre_topc @ X0)
% 3.71/3.90          | ~ (v3_tops_2 @ X1 @ sk_A @ X0)
% 3.71/3.90          | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0) @ X1)
% 3.71/3.90              = (k2_struct_0 @ X0))
% 3.71/3.90          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 3.71/3.90          | ~ (v1_funct_1 @ X1)
% 3.71/3.90          | ~ (l1_pre_topc @ sk_A)
% 3.71/3.90          | ~ (l1_struct_0 @ X0))),
% 3.71/3.90      inference('sup-', [status(thm)], ['428', '431'])).
% 3.71/3.90  thf('433', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('demod', [status(thm)], ['60', '61', '63'])).
% 3.71/3.90  thf('434', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('demod', [status(thm)], ['60', '61', '63'])).
% 3.71/3.90  thf('435', plain, ((l1_pre_topc @ sk_A)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('436', plain,
% 3.71/3.90      (![X0 : $i, X1 : $i]:
% 3.71/3.90         (~ (m1_subset_1 @ X1 @ 
% 3.71/3.90             (k1_zfmisc_1 @ 
% 3.71/3.90              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ X0))))
% 3.71/3.90          | ~ (l1_pre_topc @ X0)
% 3.71/3.90          | ~ (v3_tops_2 @ X1 @ sk_A @ X0)
% 3.71/3.90          | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ X0) @ X1)
% 3.71/3.90              = (k2_struct_0 @ X0))
% 3.71/3.90          | ~ (v1_funct_2 @ X1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ X0))
% 3.71/3.90          | ~ (v1_funct_1 @ X1)
% 3.71/3.90          | ~ (l1_struct_0 @ X0))),
% 3.71/3.90      inference('demod', [status(thm)], ['432', '433', '434', '435'])).
% 3.71/3.90  thf('437', plain,
% 3.71/3.90      ((~ (l1_struct_0 @ sk_B)
% 3.71/3.90        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.71/3.90        | ~ (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.71/3.90             (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 3.71/3.90        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 3.71/3.90            (k2_funct_1 @ (k2_funct_1 @ sk_C))) = (k2_struct_0 @ sk_B))
% 3.71/3.90        | ~ (v3_tops_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_A @ sk_B)
% 3.71/3.90        | ~ (l1_pre_topc @ sk_B))),
% 3.71/3.90      inference('sup-', [status(thm)], ['427', '436'])).
% 3.71/3.90  thf('438', plain, ((l1_struct_0 @ sk_B)),
% 3.71/3.90      inference('sup-', [status(thm)], ['9', '10'])).
% 3.71/3.90  thf('439', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.71/3.90      inference('demod', [status(thm)], ['350', '351', '352', '353'])).
% 3.71/3.90  thf('440', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['209', '255', '256', '257'])).
% 3.71/3.90  thf('441', plain,
% 3.71/3.90      ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.71/3.90        (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['366', '367', '368', '369'])).
% 3.71/3.90  thf('442', plain, (((u1_struct_0 @ sk_B) = (k2_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['209', '255', '256', '257'])).
% 3.71/3.90  thf('443', plain, ((l1_pre_topc @ sk_B)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('444', plain,
% 3.71/3.90      ((((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.71/3.90          (k2_funct_1 @ (k2_funct_1 @ sk_C))) = (k2_struct_0 @ sk_B))
% 3.71/3.90        | ~ (v3_tops_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_A @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)],
% 3.71/3.90                ['437', '438', '439', '440', '441', '442', '443'])).
% 3.71/3.90  thf('445', plain,
% 3.71/3.90      ((~ (v3_tops_2 @ sk_C @ sk_A @ sk_B)
% 3.71/3.90        | ~ (v1_relat_1 @ sk_C)
% 3.71/3.90        | ~ (v1_funct_1 @ sk_C)
% 3.71/3.90        | ~ (v2_funct_1 @ sk_C)
% 3.71/3.90        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.71/3.90            (k2_funct_1 @ (k2_funct_1 @ sk_C))) = (k2_struct_0 @ sk_B)))),
% 3.71/3.90      inference('sup-', [status(thm)], ['426', '444'])).
% 3.71/3.90  thf('446', plain, ((v3_tops_2 @ sk_C @ sk_A @ sk_B)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('447', plain, ((v1_relat_1 @ sk_C)),
% 3.71/3.90      inference('sup-', [status(thm)], ['52', '53'])).
% 3.71/3.90  thf('448', plain, ((v1_funct_1 @ sk_C)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('449', plain, ((v2_funct_1 @ sk_C)),
% 3.71/3.90      inference('demod', [status(thm)], ['79', '80', '81', '88', '89'])).
% 3.71/3.90  thf('450', plain,
% 3.71/3.90      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.71/3.90         (k2_funct_1 @ (k2_funct_1 @ sk_C))) = (k2_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['445', '446', '447', '448', '449'])).
% 3.71/3.90  thf('451', plain,
% 3.71/3.90      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.71/3.90          (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.71/3.90          = (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 3.71/3.90        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 3.71/3.90      inference('demod', [status(thm)], ['402', '425', '450'])).
% 3.71/3.90  thf('452', plain,
% 3.71/3.90      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 3.71/3.90         (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.71/3.90         = (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.71/3.90      inference('simplify', [status(thm)], ['451'])).
% 3.71/3.90  thf('453', plain,
% 3.71/3.90      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90          = (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 3.71/3.90        | ~ (v1_relat_1 @ sk_C)
% 3.71/3.90        | ~ (v1_funct_1 @ sk_C)
% 3.71/3.90        | ~ (v2_funct_1 @ sk_C))),
% 3.71/3.90      inference('sup+', [status(thm)], ['396', '452'])).
% 3.71/3.90  thf('454', plain,
% 3.71/3.90      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.71/3.90         = (k2_funct_1 @ sk_C))),
% 3.71/3.90      inference('simplify', [status(thm)], ['110'])).
% 3.71/3.90  thf('455', plain, ((v1_relat_1 @ sk_C)),
% 3.71/3.90      inference('sup-', [status(thm)], ['52', '53'])).
% 3.71/3.90  thf('456', plain, ((v1_funct_1 @ sk_C)),
% 3.71/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.90  thf('457', plain, ((v2_funct_1 @ sk_C)),
% 3.71/3.90      inference('demod', [status(thm)], ['79', '80', '81', '88', '89'])).
% 3.71/3.90  thf('458', plain,
% 3.71/3.90      (((k2_funct_1 @ sk_C) = (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.71/3.90      inference('demod', [status(thm)], ['453', '454', '455', '456', '457'])).
% 3.71/3.90  thf('459', plain,
% 3.71/3.90      (![X8 : $i]:
% 3.71/3.90         ((v2_funct_1 @ (k2_funct_1 @ X8))
% 3.71/3.90          | ~ (v2_funct_1 @ X8)
% 3.71/3.90          | ~ (v1_funct_1 @ X8)
% 3.71/3.90          | ~ (v1_relat_1 @ X8))),
% 3.71/3.90      inference('cnf', [status(esa)], [fc6_funct_1])).
% 3.71/3.90  thf('460', plain,
% 3.71/3.90      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 3.71/3.90        | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.71/3.90        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.71/3.90        | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.71/3.90      inference('sup+', [status(thm)], ['458', '459'])).
% 3.71/3.90  thf('461', plain,
% 3.71/3.90      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.71/3.90        (k1_zfmisc_1 @ 
% 3.71/3.90         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))))),
% 3.71/3.90      inference('demod', [status(thm)], ['325', '326', '327', '328'])).
% 3.71/3.90  thf('462', plain,
% 3.71/3.90      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.71/3.90         ((v1_relat_1 @ X10)
% 3.71/3.90          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 3.71/3.90      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.71/3.90  thf('463', plain, ((v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.71/3.90      inference('sup-', [status(thm)], ['461', '462'])).
% 3.71/3.90  thf('464', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.71/3.90      inference('demod', [status(thm)], ['350', '351', '352', '353'])).
% 3.71/3.90  thf('465', plain, ((v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.71/3.90      inference('demod', [status(thm)], ['420', '421', '422', '423', '424'])).
% 3.71/3.90  thf('466', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 3.71/3.90      inference('demod', [status(thm)], ['460', '463', '464', '465'])).
% 3.71/3.90  thf('467', plain,
% 3.71/3.90      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 3.71/3.90         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 3.71/3.90      inference('clc', [status(thm)], ['285', '286'])).
% 3.71/3.90  thf('468', plain,
% 3.71/3.90      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.71/3.90        (k1_zfmisc_1 @ 
% 3.71/3.90         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 3.71/3.90      inference('simplify', [status(thm)], ['134'])).
% 3.71/3.90  thf('469', plain,
% 3.71/3.90      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.71/3.90         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 3.71/3.90          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 3.71/3.90      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.71/3.90  thf('470', plain,
% 3.71/3.90      (((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 3.71/3.90         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 3.71/3.90      inference('sup-', [status(thm)], ['468', '469'])).
% 3.71/3.90  thf('471', plain,
% 3.71/3.90      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B))),
% 3.71/3.90      inference('clc', [status(thm)], ['253', '254'])).
% 3.71/3.90  thf('472', plain,
% 3.71/3.90      (((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 3.71/3.90         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B))),
% 3.71/3.90      inference('demod', [status(thm)], ['470', '471'])).
% 3.71/3.90  thf('473', plain,
% 3.71/3.90      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.71/3.90        (k1_zfmisc_1 @ 
% 3.71/3.90         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 3.71/3.90      inference('simplify', [status(thm)], ['134'])).
% 3.71/3.90  thf('474', plain,
% 3.71/3.90      (((v3_tops_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 3.71/3.90        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 3.71/3.90        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 3.71/3.90      inference('demod', [status(thm)],
% 3.71/3.90                ['313', '378', '379', '380', '395', '466', '467', '472', '473'])).
% 3.71/3.90  thf('475', plain, ((v3_tops_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 3.71/3.90      inference('simplify', [status(thm)], ['474'])).
% 3.71/3.90  thf('476', plain, ($false), inference('demod', [status(thm)], ['112', '475'])).
% 3.71/3.90  
% 3.71/3.90  % SZS output end Refutation
% 3.71/3.90  
% 3.71/3.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
