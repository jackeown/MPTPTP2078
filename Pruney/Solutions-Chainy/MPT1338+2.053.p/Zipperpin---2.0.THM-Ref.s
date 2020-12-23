%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vuY0yHZFY7

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 380 expanded)
%              Number of leaves         :   47 ( 135 expanded)
%              Depth                    :   20
%              Number of atoms          : 1671 (8385 expanded)
%              Number of equality atoms :  138 ( 505 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_funct_1 @ X2 )
        = ( k4_relat_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t62_tops_2,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
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
                      = ( k2_struct_0 @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_tops_2])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X17: $i] :
      ( ( k9_setfam_1 @ X17 )
      = ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( m1_subset_1 @ sk_C @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('6',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

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

thf('8',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X25 @ X27 )
       != X25 )
      | ~ ( v2_funct_1 @ X27 )
      | ( ( k2_tops_2 @ X26 @ X25 @ X27 )
        = ( k2_funct_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('9',plain,(
    ! [X17: $i] :
      ( ( k9_setfam_1 @ X17 )
      = ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('10',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X25 @ X27 )
       != X25 )
      | ~ ( v2_funct_1 @ X27 )
      | ( ( k2_tops_2 @ X26 @ X25 @ X27 )
        = ( k2_funct_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('14',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('20',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12','17','18','23'])).

thf('25',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('27',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['27'])).

thf('29',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t35_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( B = k1_xboole_0 )
          | ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) )
              = ( k6_partfun1 @ A ) )
            & ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C )
              = ( k6_partfun1 @ B ) ) ) ) ) ) )).

thf('35',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X18 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_2 @ X19 @ X20 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X18 ) ) )
      | ( ( k5_relat_1 @ X19 @ ( k2_funct_1 @ X19 ) )
        = ( k6_partfun1 @ X20 ) )
      | ~ ( v2_funct_1 @ X19 )
      | ( ( k2_relset_1 @ X20 @ X18 @ X19 )
       != X18 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('36',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('37',plain,(
    ! [X17: $i] :
      ( ( k9_setfam_1 @ X17 )
      = ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('38',plain,(
    ! [X16: $i] :
      ( ( k6_partfun1 @ X16 )
      = ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('39',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X18 = o_0_0_xboole_0 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_2 @ X19 @ X20 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ X20 @ X18 ) ) )
      | ( ( k5_relat_1 @ X19 @ ( k2_funct_1 @ X19 ) )
        = ( k6_relat_1 @ X20 ) )
      | ~ ( v2_funct_1 @ X19 )
      | ( ( k2_relset_1 @ X20 @ X18 @ X19 )
       != X18 ) ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('40',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_struct_0 @ sk_B )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('42',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('44',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k2_struct_0 @ sk_B )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41','42','43','44'])).

thf('46',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = o_0_0_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf(t58_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('47',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X3 @ ( k2_funct_1 @ X3 ) ) )
        = ( k1_relat_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('48',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) )
      = ( k1_relat_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
      = o_0_0_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('49',plain,(
    ! [X1: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X1 ) )
      = X1 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('51',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('52',plain,(
    ! [X17: $i] :
      ( ( k9_setfam_1 @ X17 )
      = ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('53',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['48','49','54','55','56'])).

thf('58',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k2_struct_0 @ sk_B )
      = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','57'])).

thf('59',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('62',plain,(
    ! [X23: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['60','64'])).

thf('66',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ) )).

thf('67',plain,(
    ! [X24: $i] :
      ( ( v1_xboole_0 @ ( k1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc3_struct_0])).

thf('68',plain,(
    v1_xboole_0 @ ( k1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k1_struct_0 @ A )
        = k1_xboole_0 ) ) )).

thf('70',plain,(
    ! [X21: $i] :
      ( ( ( k1_struct_0 @ X21 )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d2_struct_0])).

thf('71',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('72',plain,(
    ! [X21: $i] :
      ( ( ( k1_struct_0 @ X21 )
        = o_0_0_xboole_0 )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k1_struct_0 @ sk_A )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['68','73'])).

thf('75',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['65','74','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','78'])).

thf('80',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_funct_1 @ X2 )
        = ( k4_relat_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('81',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['24'])).

thf('82',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('83',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['27'])).

thf('84',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['81','86'])).

thf('88',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['80','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_C @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t24_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k1_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k2_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('90',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X13 @ ( k3_relset_1 @ X13 @ X14 @ X15 ) )
        = ( k2_relset_1 @ X13 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[t24_relset_1])).

thf('91',plain,(
    ! [X17: $i] :
      ( ( k9_setfam_1 @ X17 )
      = ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('92',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X13 @ ( k3_relset_1 @ X13 @ X14 @ X15 ) )
        = ( k2_relset_1 @ X13 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf('94',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_C @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(redefinition_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k3_relset_1 @ A @ B @ C )
        = ( k4_relat_1 @ C ) ) ) )).

thf('97',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k3_relset_1 @ X11 @ X12 @ X10 )
        = ( k4_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('98',plain,(
    ! [X17: $i] :
      ( ( k9_setfam_1 @ X17 )
      = ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('99',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k3_relset_1 @ X11 @ X12 @ X10 )
        = ( k4_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['96','99'])).

thf('101',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['95','100'])).

thf('102',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['50','53'])).

thf('103',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['88','101','102','103','104'])).

thf('106',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['27'])).

thf('108',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['106','107'])).

thf('109',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['79','108'])).

thf('110',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_C @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('112',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X13 @ ( k3_relset_1 @ X13 @ X14 @ X15 ) )
        = ( k1_relset_1 @ X13 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[t24_relset_1])).

thf('113',plain,(
    ! [X17: $i] :
      ( ( k9_setfam_1 @ X17 )
      = ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('114',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X13 @ ( k3_relset_1 @ X13 @ X14 @ X15 ) )
        = ( k1_relset_1 @ X13 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['111','114'])).

thf('116',plain,
    ( ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['96','99'])).

thf('117',plain,(
    m1_subset_1 @ sk_C @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('118',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('119',plain,(
    ! [X17: $i] :
      ( ( k9_setfam_1 @ X17 )
      = ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('120',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['117','120'])).

thf('122',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['115','116','121'])).

thf('123',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['50','53'])).

thf('124',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['110','122','123','124','125'])).

thf('127',plain,(
    $false ),
    inference(simplify,[status(thm)],['126'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vuY0yHZFY7
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:58:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 194 iterations in 0.089s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.55  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.20/0.55  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.20/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.55  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.55  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 0.20/0.55  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.20/0.55  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.55  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.20/0.55  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.20/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.55  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.20/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.55  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.20/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.55  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 0.20/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.55  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.55  thf(d9_funct_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.55       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.20/0.55  thf('0', plain,
% 0.20/0.55      (![X2 : $i]:
% 0.20/0.55         (~ (v2_funct_1 @ X2)
% 0.20/0.55          | ((k2_funct_1 @ X2) = (k4_relat_1 @ X2))
% 0.20/0.55          | ~ (v1_funct_1 @ X2)
% 0.20/0.55          | ~ (v1_relat_1 @ X2))),
% 0.20/0.55      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.20/0.55  thf(d3_struct_0, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.20/0.55  thf('1', plain,
% 0.20/0.55      (![X22 : $i]:
% 0.20/0.55         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.55  thf(t62_tops_2, conjecture,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( l1_struct_0 @ A ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.20/0.55           ( ![C:$i]:
% 0.20/0.55             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.55                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.55                 ( m1_subset_1 @
% 0.20/0.55                   C @ 
% 0.20/0.55                   ( k1_zfmisc_1 @
% 0.20/0.55                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.55               ( ( ( ( k2_relset_1 @
% 0.20/0.55                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.20/0.55                     ( k2_struct_0 @ B ) ) & 
% 0.20/0.55                   ( v2_funct_1 @ C ) ) =>
% 0.20/0.55                 ( ( ( k1_relset_1 @
% 0.20/0.55                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.20/0.55                       ( k2_tops_2 @
% 0.20/0.55                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.20/0.55                     ( k2_struct_0 @ B ) ) & 
% 0.20/0.55                   ( ( k2_relset_1 @
% 0.20/0.55                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.20/0.55                       ( k2_tops_2 @
% 0.20/0.55                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.20/0.55                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i]:
% 0.20/0.55        ( ( l1_struct_0 @ A ) =>
% 0.20/0.55          ( ![B:$i]:
% 0.20/0.55            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.20/0.55              ( ![C:$i]:
% 0.20/0.55                ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.55                    ( v1_funct_2 @
% 0.20/0.55                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.55                    ( m1_subset_1 @
% 0.20/0.55                      C @ 
% 0.20/0.55                      ( k1_zfmisc_1 @
% 0.20/0.55                        ( k2_zfmisc_1 @
% 0.20/0.55                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.55                  ( ( ( ( k2_relset_1 @
% 0.20/0.55                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.20/0.55                        ( k2_struct_0 @ B ) ) & 
% 0.20/0.55                      ( v2_funct_1 @ C ) ) =>
% 0.20/0.55                    ( ( ( k1_relset_1 @
% 0.20/0.55                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.20/0.55                          ( k2_tops_2 @
% 0.20/0.55                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.20/0.55                        ( k2_struct_0 @ B ) ) & 
% 0.20/0.55                      ( ( k2_relset_1 @
% 0.20/0.55                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.20/0.55                          ( k2_tops_2 @
% 0.20/0.55                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.20/0.55                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ 
% 0.20/0.55        (k1_zfmisc_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(redefinition_k9_setfam_1, axiom,
% 0.20/0.55    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.55  thf('3', plain, (![X17 : $i]: ((k9_setfam_1 @ X17) = (k1_zfmisc_1 @ X17))),
% 0.20/0.55      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.20/0.55  thf('4', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ 
% 0.20/0.55        (k9_setfam_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.55      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.55  thf('5', plain,
% 0.20/0.55      (((m1_subset_1 @ sk_C @ 
% 0.20/0.55         (k9_setfam_1 @ 
% 0.20/0.55          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.20/0.55        | ~ (l1_struct_0 @ sk_B))),
% 0.20/0.55      inference('sup+', [status(thm)], ['1', '4'])).
% 0.20/0.55  thf('6', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('7', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ 
% 0.20/0.55        (k9_setfam_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.20/0.55      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.55  thf(d4_tops_2, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.55       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.20/0.55         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.20/0.55  thf('8', plain,
% 0.20/0.55      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.55         (((k2_relset_1 @ X26 @ X25 @ X27) != (X25))
% 0.20/0.55          | ~ (v2_funct_1 @ X27)
% 0.20/0.55          | ((k2_tops_2 @ X26 @ X25 @ X27) = (k2_funct_1 @ X27))
% 0.20/0.55          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 0.20/0.55          | ~ (v1_funct_2 @ X27 @ X26 @ X25)
% 0.20/0.55          | ~ (v1_funct_1 @ X27))),
% 0.20/0.55      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.20/0.55  thf('9', plain, (![X17 : $i]: ((k9_setfam_1 @ X17) = (k1_zfmisc_1 @ X17))),
% 0.20/0.55      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.20/0.55  thf('10', plain,
% 0.20/0.55      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.55         (((k2_relset_1 @ X26 @ X25 @ X27) != (X25))
% 0.20/0.55          | ~ (v2_funct_1 @ X27)
% 0.20/0.55          | ((k2_tops_2 @ X26 @ X25 @ X27) = (k2_funct_1 @ X27))
% 0.20/0.55          | ~ (m1_subset_1 @ X27 @ (k9_setfam_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 0.20/0.55          | ~ (v1_funct_2 @ X27 @ X26 @ X25)
% 0.20/0.55          | ~ (v1_funct_1 @ X27))),
% 0.20/0.55      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.55  thf('11', plain,
% 0.20/0.55      ((~ (v1_funct_1 @ sk_C)
% 0.20/0.55        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.20/0.55        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.20/0.55            = (k2_funct_1 @ sk_C))
% 0.20/0.55        | ~ (v2_funct_1 @ sk_C)
% 0.20/0.55        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.20/0.55            != (k2_struct_0 @ sk_B)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['7', '10'])).
% 0.20/0.55  thf('12', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('13', plain,
% 0.20/0.55      (![X22 : $i]:
% 0.20/0.55         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.55  thf('14', plain,
% 0.20/0.55      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('15', plain,
% 0.20/0.55      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.20/0.55        | ~ (l1_struct_0 @ sk_B))),
% 0.20/0.55      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.55  thf('16', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('17', plain,
% 0.20/0.55      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.20/0.55      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.55  thf('18', plain, ((v2_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('19', plain,
% 0.20/0.55      (![X22 : $i]:
% 0.20/0.55         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.55  thf('20', plain,
% 0.20/0.55      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.20/0.55         = (k2_struct_0 @ sk_B))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('21', plain,
% 0.20/0.55      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.20/0.55          = (k2_struct_0 @ sk_B))
% 0.20/0.55        | ~ (l1_struct_0 @ sk_B))),
% 0.20/0.55      inference('sup+', [status(thm)], ['19', '20'])).
% 0.20/0.55  thf('22', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('23', plain,
% 0.20/0.55      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.20/0.55         = (k2_struct_0 @ sk_B))),
% 0.20/0.55      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.55  thf('24', plain,
% 0.20/0.55      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.20/0.55          = (k2_funct_1 @ sk_C))
% 0.20/0.55        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.20/0.55      inference('demod', [status(thm)], ['11', '12', '17', '18', '23'])).
% 0.20/0.55  thf('25', plain,
% 0.20/0.55      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.20/0.55         = (k2_funct_1 @ sk_C))),
% 0.20/0.55      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.55  thf('26', plain,
% 0.20/0.55      (![X22 : $i]:
% 0.20/0.55         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.55  thf('27', plain,
% 0.20/0.55      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.20/0.55          != (k2_struct_0 @ sk_B))
% 0.20/0.55        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.20/0.55            != (k2_struct_0 @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('28', plain,
% 0.20/0.55      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.20/0.55          != (k2_struct_0 @ sk_A)))
% 0.20/0.55         <= (~
% 0.20/0.55             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.20/0.55                = (k2_struct_0 @ sk_A))))),
% 0.20/0.55      inference('split', [status(esa)], ['27'])).
% 0.20/0.55  thf('29', plain,
% 0.20/0.55      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.20/0.55           != (k2_struct_0 @ sk_A))
% 0.20/0.55         | ~ (l1_struct_0 @ sk_B)))
% 0.20/0.55         <= (~
% 0.20/0.55             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.20/0.55                = (k2_struct_0 @ sk_A))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['26', '28'])).
% 0.20/0.55  thf('30', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('31', plain,
% 0.20/0.55      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.20/0.55          != (k2_struct_0 @ sk_A)))
% 0.20/0.55         <= (~
% 0.20/0.55             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.20/0.55                = (k2_struct_0 @ sk_A))))),
% 0.20/0.55      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.55  thf('32', plain,
% 0.20/0.55      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55          (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))
% 0.20/0.55         <= (~
% 0.20/0.55             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.20/0.55                = (k2_struct_0 @ sk_A))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['25', '31'])).
% 0.20/0.55  thf('33', plain,
% 0.20/0.55      (![X22 : $i]:
% 0.20/0.55         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.55  thf('34', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ 
% 0.20/0.55        (k9_setfam_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.20/0.55      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.55  thf(t35_funct_2, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.55       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.20/0.55         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.55           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.20/0.55             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.20/0.55  thf('35', plain,
% 0.20/0.55      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.55         (((X18) = (k1_xboole_0))
% 0.20/0.55          | ~ (v1_funct_1 @ X19)
% 0.20/0.55          | ~ (v1_funct_2 @ X19 @ X20 @ X18)
% 0.20/0.55          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X18)))
% 0.20/0.55          | ((k5_relat_1 @ X19 @ (k2_funct_1 @ X19)) = (k6_partfun1 @ X20))
% 0.20/0.55          | ~ (v2_funct_1 @ X19)
% 0.20/0.55          | ((k2_relset_1 @ X20 @ X18 @ X19) != (X18)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.20/0.55  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.20/0.55  thf('36', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.55  thf('37', plain, (![X17 : $i]: ((k9_setfam_1 @ X17) = (k1_zfmisc_1 @ X17))),
% 0.20/0.55      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.20/0.55  thf(redefinition_k6_partfun1, axiom,
% 0.20/0.55    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.20/0.55  thf('38', plain, (![X16 : $i]: ((k6_partfun1 @ X16) = (k6_relat_1 @ X16))),
% 0.20/0.55      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.55  thf('39', plain,
% 0.20/0.55      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.55         (((X18) = (o_0_0_xboole_0))
% 0.20/0.55          | ~ (v1_funct_1 @ X19)
% 0.20/0.55          | ~ (v1_funct_2 @ X19 @ X20 @ X18)
% 0.20/0.55          | ~ (m1_subset_1 @ X19 @ (k9_setfam_1 @ (k2_zfmisc_1 @ X20 @ X18)))
% 0.20/0.55          | ((k5_relat_1 @ X19 @ (k2_funct_1 @ X19)) = (k6_relat_1 @ X20))
% 0.20/0.55          | ~ (v2_funct_1 @ X19)
% 0.20/0.55          | ((k2_relset_1 @ X20 @ X18 @ X19) != (X18)))),
% 0.20/0.55      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 0.20/0.55  thf('40', plain,
% 0.20/0.55      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.20/0.55          != (k2_struct_0 @ sk_B))
% 0.20/0.55        | ~ (v2_funct_1 @ sk_C)
% 0.20/0.55        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.20/0.55            = (k6_relat_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.55        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.20/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.55        | ((k2_struct_0 @ sk_B) = (o_0_0_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['34', '39'])).
% 0.20/0.55  thf('41', plain,
% 0.20/0.55      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.20/0.55         = (k2_struct_0 @ sk_B))),
% 0.20/0.55      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.55  thf('42', plain, ((v2_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('43', plain,
% 0.20/0.55      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.20/0.55      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.55  thf('44', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('45', plain,
% 0.20/0.55      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.20/0.55        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.20/0.55            = (k6_relat_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.55        | ((k2_struct_0 @ sk_B) = (o_0_0_xboole_0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['40', '41', '42', '43', '44'])).
% 0.20/0.55  thf('46', plain,
% 0.20/0.55      ((((k2_struct_0 @ sk_B) = (o_0_0_xboole_0))
% 0.20/0.55        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.20/0.55            = (k6_relat_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.55      inference('simplify', [status(thm)], ['45'])).
% 0.20/0.55  thf(t58_funct_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.55       ( ( v2_funct_1 @ A ) =>
% 0.20/0.55         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.20/0.55             ( k1_relat_1 @ A ) ) & 
% 0.20/0.55           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.20/0.55             ( k1_relat_1 @ A ) ) ) ) ))).
% 0.20/0.55  thf('47', plain,
% 0.20/0.55      (![X3 : $i]:
% 0.20/0.55         (~ (v2_funct_1 @ X3)
% 0.20/0.55          | ((k2_relat_1 @ (k5_relat_1 @ X3 @ (k2_funct_1 @ X3)))
% 0.20/0.55              = (k1_relat_1 @ X3))
% 0.20/0.55          | ~ (v1_funct_1 @ X3)
% 0.20/0.55          | ~ (v1_relat_1 @ X3))),
% 0.20/0.55      inference('cnf', [status(esa)], [t58_funct_1])).
% 0.20/0.55  thf('48', plain,
% 0.20/0.55      ((((k2_relat_1 @ (k6_relat_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.55          = (k1_relat_1 @ sk_C))
% 0.20/0.55        | ((k2_struct_0 @ sk_B) = (o_0_0_xboole_0))
% 0.20/0.55        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.55        | ~ (v2_funct_1 @ sk_C))),
% 0.20/0.55      inference('sup+', [status(thm)], ['46', '47'])).
% 0.20/0.55  thf(t71_relat_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.20/0.55       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.55  thf('49', plain, (![X1 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X1)) = (X1))),
% 0.20/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.55  thf('50', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ 
% 0.20/0.55        (k9_setfam_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.55      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.55  thf(cc1_relset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.55       ( v1_relat_1 @ C ) ))).
% 0.20/0.55  thf('51', plain,
% 0.20/0.55      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.55         ((v1_relat_1 @ X4)
% 0.20/0.55          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.20/0.55      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.55  thf('52', plain, (![X17 : $i]: ((k9_setfam_1 @ X17) = (k1_zfmisc_1 @ X17))),
% 0.20/0.55      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.20/0.55  thf('53', plain,
% 0.20/0.55      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.55         ((v1_relat_1 @ X4)
% 0.20/0.55          | ~ (m1_subset_1 @ X4 @ (k9_setfam_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.20/0.55      inference('demod', [status(thm)], ['51', '52'])).
% 0.20/0.55  thf('54', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.55      inference('sup-', [status(thm)], ['50', '53'])).
% 0.20/0.55  thf('55', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('56', plain, ((v2_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('57', plain,
% 0.20/0.55      ((((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 0.20/0.55        | ((k2_struct_0 @ sk_B) = (o_0_0_xboole_0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['48', '49', '54', '55', '56'])).
% 0.20/0.55  thf('58', plain,
% 0.20/0.55      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 0.20/0.55        | ~ (l1_struct_0 @ sk_A)
% 0.20/0.55        | ((k2_struct_0 @ sk_B) = (o_0_0_xboole_0)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['33', '57'])).
% 0.20/0.55  thf('59', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('60', plain,
% 0.20/0.55      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 0.20/0.55        | ((k2_struct_0 @ sk_B) = (o_0_0_xboole_0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['58', '59'])).
% 0.20/0.55  thf('61', plain,
% 0.20/0.55      (![X22 : $i]:
% 0.20/0.55         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.55  thf(fc2_struct_0, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.55       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.55  thf('62', plain,
% 0.20/0.55      (![X23 : $i]:
% 0.20/0.55         (~ (v1_xboole_0 @ (u1_struct_0 @ X23))
% 0.20/0.55          | ~ (l1_struct_0 @ X23)
% 0.20/0.55          | (v2_struct_0 @ X23))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.55  thf('63', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.20/0.55          | ~ (l1_struct_0 @ X0)
% 0.20/0.55          | (v2_struct_0 @ X0)
% 0.20/0.55          | ~ (l1_struct_0 @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['61', '62'])).
% 0.20/0.55  thf('64', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((v2_struct_0 @ X0)
% 0.20/0.55          | ~ (l1_struct_0 @ X0)
% 0.20/0.55          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['63'])).
% 0.20/0.55  thf('65', plain,
% 0.20/0.55      ((~ (v1_xboole_0 @ o_0_0_xboole_0)
% 0.20/0.55        | ((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 0.20/0.55        | ~ (l1_struct_0 @ sk_B)
% 0.20/0.55        | (v2_struct_0 @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['60', '64'])).
% 0.20/0.55  thf('66', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(fc3_struct_0, axiom,
% 0.20/0.55    (![A:$i]: ( ( l1_struct_0 @ A ) => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ))).
% 0.20/0.55  thf('67', plain,
% 0.20/0.55      (![X24 : $i]:
% 0.20/0.55         ((v1_xboole_0 @ (k1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc3_struct_0])).
% 0.20/0.55  thf('68', plain, ((v1_xboole_0 @ (k1_struct_0 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['66', '67'])).
% 0.20/0.55  thf('69', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(d2_struct_0, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( l1_struct_0 @ A ) => ( ( k1_struct_0 @ A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.55  thf('70', plain,
% 0.20/0.55      (![X21 : $i]:
% 0.20/0.55         (((k1_struct_0 @ X21) = (k1_xboole_0)) | ~ (l1_struct_0 @ X21))),
% 0.20/0.55      inference('cnf', [status(esa)], [d2_struct_0])).
% 0.20/0.55  thf('71', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.55  thf('72', plain,
% 0.20/0.55      (![X21 : $i]:
% 0.20/0.55         (((k1_struct_0 @ X21) = (o_0_0_xboole_0)) | ~ (l1_struct_0 @ X21))),
% 0.20/0.55      inference('demod', [status(thm)], ['70', '71'])).
% 0.20/0.55  thf('73', plain, (((k1_struct_0 @ sk_A) = (o_0_0_xboole_0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['69', '72'])).
% 0.20/0.55  thf('74', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.20/0.55      inference('demod', [status(thm)], ['68', '73'])).
% 0.20/0.55  thf('75', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('76', plain,
% 0.20/0.55      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.20/0.55      inference('demod', [status(thm)], ['65', '74', '75'])).
% 0.20/0.55  thf('77', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('78', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.20/0.55      inference('clc', [status(thm)], ['76', '77'])).
% 0.20/0.55  thf('79', plain,
% 0.20/0.55      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55          (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 0.20/0.55         <= (~
% 0.20/0.55             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.20/0.55                = (k2_struct_0 @ sk_A))))),
% 0.20/0.55      inference('demod', [status(thm)], ['32', '78'])).
% 0.20/0.55  thf('80', plain,
% 0.20/0.55      (![X2 : $i]:
% 0.20/0.55         (~ (v2_funct_1 @ X2)
% 0.20/0.55          | ((k2_funct_1 @ X2) = (k4_relat_1 @ X2))
% 0.20/0.55          | ~ (v1_funct_1 @ X2)
% 0.20/0.55          | ~ (v1_relat_1 @ X2))),
% 0.20/0.55      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.20/0.55  thf('81', plain,
% 0.20/0.55      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.20/0.55         = (k2_funct_1 @ sk_C))),
% 0.20/0.55      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.55  thf('82', plain,
% 0.20/0.55      (![X22 : $i]:
% 0.20/0.55         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.55  thf('83', plain,
% 0.20/0.55      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.20/0.55          != (k2_struct_0 @ sk_B)))
% 0.20/0.55         <= (~
% 0.20/0.55             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.20/0.55                = (k2_struct_0 @ sk_B))))),
% 0.20/0.55      inference('split', [status(esa)], ['27'])).
% 0.20/0.55  thf('84', plain,
% 0.20/0.55      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.20/0.55           != (k2_struct_0 @ sk_B))
% 0.20/0.55         | ~ (l1_struct_0 @ sk_B)))
% 0.20/0.55         <= (~
% 0.20/0.55             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.20/0.55                = (k2_struct_0 @ sk_B))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['82', '83'])).
% 0.20/0.55  thf('85', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('86', plain,
% 0.20/0.55      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.20/0.55          != (k2_struct_0 @ sk_B)))
% 0.20/0.55         <= (~
% 0.20/0.55             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.20/0.55                = (k2_struct_0 @ sk_B))))),
% 0.20/0.55      inference('demod', [status(thm)], ['84', '85'])).
% 0.20/0.55  thf('87', plain,
% 0.20/0.55      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55          (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_B)))
% 0.20/0.55         <= (~
% 0.20/0.55             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.20/0.55                = (k2_struct_0 @ sk_B))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['81', '86'])).
% 0.20/0.55  thf('88', plain,
% 0.20/0.55      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55           (k4_relat_1 @ sk_C)) != (k2_struct_0 @ sk_B))
% 0.20/0.55         | ~ (v1_relat_1 @ sk_C)
% 0.20/0.55         | ~ (v1_funct_1 @ sk_C)
% 0.20/0.55         | ~ (v2_funct_1 @ sk_C)))
% 0.20/0.55         <= (~
% 0.20/0.55             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.20/0.55                = (k2_struct_0 @ sk_B))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['80', '87'])).
% 0.20/0.55  thf('89', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ 
% 0.20/0.55        (k9_setfam_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.55      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.55  thf(t24_relset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.55       ( ( ( k1_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) ) =
% 0.20/0.55           ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.20/0.55         ( ( k2_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) ) =
% 0.20/0.55           ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.55  thf('90', plain,
% 0.20/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.55         (((k1_relset_1 @ X14 @ X13 @ (k3_relset_1 @ X13 @ X14 @ X15))
% 0.20/0.55            = (k2_relset_1 @ X13 @ X14 @ X15))
% 0.20/0.55          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.20/0.55      inference('cnf', [status(esa)], [t24_relset_1])).
% 0.20/0.55  thf('91', plain, (![X17 : $i]: ((k9_setfam_1 @ X17) = (k1_zfmisc_1 @ X17))),
% 0.20/0.55      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.20/0.55  thf('92', plain,
% 0.20/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.55         (((k1_relset_1 @ X14 @ X13 @ (k3_relset_1 @ X13 @ X14 @ X15))
% 0.20/0.55            = (k2_relset_1 @ X13 @ X14 @ X15))
% 0.20/0.55          | ~ (m1_subset_1 @ X15 @ (k9_setfam_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.20/0.55      inference('demod', [status(thm)], ['90', '91'])).
% 0.20/0.55  thf('93', plain,
% 0.20/0.55      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55         (k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.20/0.55         = (k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.20/0.55      inference('sup-', [status(thm)], ['89', '92'])).
% 0.20/0.55  thf('94', plain,
% 0.20/0.55      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.20/0.55         = (k2_struct_0 @ sk_B))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('95', plain,
% 0.20/0.55      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55         (k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.20/0.55         = (k2_struct_0 @ sk_B))),
% 0.20/0.55      inference('demod', [status(thm)], ['93', '94'])).
% 0.20/0.55  thf('96', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ 
% 0.20/0.55        (k9_setfam_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.55      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.55  thf(redefinition_k3_relset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.55       ( ( k3_relset_1 @ A @ B @ C ) = ( k4_relat_1 @ C ) ) ))).
% 0.20/0.55  thf('97', plain,
% 0.20/0.55      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.55         (((k3_relset_1 @ X11 @ X12 @ X10) = (k4_relat_1 @ X10))
% 0.20/0.55          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.20/0.55      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 0.20/0.55  thf('98', plain, (![X17 : $i]: ((k9_setfam_1 @ X17) = (k1_zfmisc_1 @ X17))),
% 0.20/0.55      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.20/0.55  thf('99', plain,
% 0.20/0.55      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.55         (((k3_relset_1 @ X11 @ X12 @ X10) = (k4_relat_1 @ X10))
% 0.20/0.55          | ~ (m1_subset_1 @ X10 @ (k9_setfam_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.20/0.55      inference('demod', [status(thm)], ['97', '98'])).
% 0.20/0.55  thf('100', plain,
% 0.20/0.55      (((k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.20/0.55         = (k4_relat_1 @ sk_C))),
% 0.20/0.55      inference('sup-', [status(thm)], ['96', '99'])).
% 0.20/0.55  thf('101', plain,
% 0.20/0.55      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55         (k4_relat_1 @ sk_C)) = (k2_struct_0 @ sk_B))),
% 0.20/0.55      inference('demod', [status(thm)], ['95', '100'])).
% 0.20/0.55  thf('102', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.55      inference('sup-', [status(thm)], ['50', '53'])).
% 0.20/0.55  thf('103', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('104', plain, ((v2_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('105', plain,
% 0.20/0.55      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))
% 0.20/0.55         <= (~
% 0.20/0.55             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.20/0.55                = (k2_struct_0 @ sk_B))))),
% 0.20/0.55      inference('demod', [status(thm)], ['88', '101', '102', '103', '104'])).
% 0.20/0.55  thf('106', plain,
% 0.20/0.55      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.20/0.55          = (k2_struct_0 @ sk_B)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['105'])).
% 0.20/0.55  thf('107', plain,
% 0.20/0.55      (~
% 0.20/0.55       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.20/0.55          = (k2_struct_0 @ sk_A))) | 
% 0.20/0.55       ~
% 0.20/0.55       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.20/0.55          = (k2_struct_0 @ sk_B)))),
% 0.20/0.55      inference('split', [status(esa)], ['27'])).
% 0.20/0.55  thf('108', plain,
% 0.20/0.55      (~
% 0.20/0.55       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.20/0.55          = (k2_struct_0 @ sk_A)))),
% 0.20/0.55      inference('sat_resolution*', [status(thm)], ['106', '107'])).
% 0.20/0.55  thf('109', plain,
% 0.20/0.55      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55         (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))),
% 0.20/0.55      inference('simpl_trail', [status(thm)], ['79', '108'])).
% 0.20/0.55  thf('110', plain,
% 0.20/0.55      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55          (k4_relat_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.20/0.55        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.55        | ~ (v2_funct_1 @ sk_C))),
% 0.20/0.55      inference('sup-', [status(thm)], ['0', '109'])).
% 0.20/0.55  thf('111', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ 
% 0.20/0.55        (k9_setfam_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.55      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.55  thf('112', plain,
% 0.20/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.55         (((k2_relset_1 @ X14 @ X13 @ (k3_relset_1 @ X13 @ X14 @ X15))
% 0.20/0.55            = (k1_relset_1 @ X13 @ X14 @ X15))
% 0.20/0.55          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.20/0.55      inference('cnf', [status(esa)], [t24_relset_1])).
% 0.20/0.55  thf('113', plain, (![X17 : $i]: ((k9_setfam_1 @ X17) = (k1_zfmisc_1 @ X17))),
% 0.20/0.55      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.20/0.55  thf('114', plain,
% 0.20/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.55         (((k2_relset_1 @ X14 @ X13 @ (k3_relset_1 @ X13 @ X14 @ X15))
% 0.20/0.55            = (k1_relset_1 @ X13 @ X14 @ X15))
% 0.20/0.55          | ~ (m1_subset_1 @ X15 @ (k9_setfam_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.20/0.55      inference('demod', [status(thm)], ['112', '113'])).
% 0.20/0.55  thf('115', plain,
% 0.20/0.55      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55         (k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.20/0.55         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.20/0.55      inference('sup-', [status(thm)], ['111', '114'])).
% 0.20/0.55  thf('116', plain,
% 0.20/0.55      (((k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.20/0.55         = (k4_relat_1 @ sk_C))),
% 0.20/0.55      inference('sup-', [status(thm)], ['96', '99'])).
% 0.20/0.55  thf('117', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ 
% 0.20/0.55        (k9_setfam_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.55      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.55  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.55       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.55  thf('118', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.55         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 0.20/0.55          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.20/0.55      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.55  thf('119', plain, (![X17 : $i]: ((k9_setfam_1 @ X17) = (k1_zfmisc_1 @ X17))),
% 0.20/0.55      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.20/0.55  thf('120', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.55         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 0.20/0.55          | ~ (m1_subset_1 @ X7 @ (k9_setfam_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.20/0.55      inference('demod', [status(thm)], ['118', '119'])).
% 0.20/0.55  thf('121', plain,
% 0.20/0.55      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.20/0.55         = (k1_relat_1 @ sk_C))),
% 0.20/0.55      inference('sup-', [status(thm)], ['117', '120'])).
% 0.20/0.55  thf('122', plain,
% 0.20/0.55      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55         (k4_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.20/0.55      inference('demod', [status(thm)], ['115', '116', '121'])).
% 0.20/0.55  thf('123', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.55      inference('sup-', [status(thm)], ['50', '53'])).
% 0.20/0.55  thf('124', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('125', plain, ((v2_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('126', plain, (((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))),
% 0.20/0.55      inference('demod', [status(thm)], ['110', '122', '123', '124', '125'])).
% 0.20/0.55  thf('127', plain, ($false), inference('simplify', [status(thm)], ['126'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
