%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.v8OhNCrTlR

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:49 EST 2020

% Result     : Theorem 3.55s
% Output     : Refutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :  208 (2089 expanded)
%              Number of leaves         :   40 ( 621 expanded)
%              Depth                    :   22
%              Number of atoms          : 1839 (54329 expanded)
%              Number of equality atoms :  124 (2780 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k3_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k3_relset_1 @ X8 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_relset_1])).

thf('2',plain,(
    m1_subset_1 @ ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k3_relset_1 @ A @ B @ C )
        = ( k4_relat_1 @ C ) ) ) )).

thf('4',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k3_relset_1 @ X18 @ X19 @ X17 )
        = ( k4_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('5',plain,
    ( ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('7',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('14',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( v1_partfun1 @ X20 @ X21 )
      | ~ ( v1_funct_2 @ X20 @ X21 @ X22 )
      | ~ ( v1_funct_1 @ X20 )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('22',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('27',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20','27'])).

thf('29',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('30',plain,(
    ! [X26: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('31',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['28','35'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('37',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_partfun1 @ X24 @ X23 )
      | ( ( k1_relat_1 @ X24 )
        = X23 )
      | ~ ( v4_relat_1 @ X24 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('40',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('41',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('43',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('44',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = ( k4_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['39','40'])).

thf('51',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('52',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('53',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['39','40'])).

thf('55',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf('58',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','41','44','57'])).

thf('59',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['6','58'])).

thf('60',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('61',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('63',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['63'])).

thf('65',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','64'])).

thf('66',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','41','44','57'])).

thf('69',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','41','44','57'])).

thf('70',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('71',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('72',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['71','76'])).

thf('78',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('81',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('83',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['28','35'])).

thf('84',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_partfun1 @ X24 @ X23 )
      | ( ( k1_relat_1 @ X24 )
        = X23 )
      | ~ ( v4_relat_1 @ X24 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('88',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['39','40'])).

thf('90',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('91',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('92',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf('94',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['88','89','92','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['81','94'])).

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

thf('96',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X27 @ X29 )
       != X27 )
      | ~ ( v2_funct_1 @ X29 )
      | ( ( k2_tops_2 @ X28 @ X27 @ X29 )
        = ( k2_funct_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('97',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('100',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('101',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['99','104'])).

thf('106',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('109',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['88','89','92','93'])).

thf('111',plain,(
    v1_funct_2 @ sk_C @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('113',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('115',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('116',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('121',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('122',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('123',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['114','122'])).

thf('124',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['88','89','92','93'])).

thf('127',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['97','98','111','112','113','127'])).

thf('129',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['88','89','92','93'])).

thf('131',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k4_relat_1 @ sk_C ) )
     != ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68','69','70','129','130'])).

thf('132',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['128'])).

thf('133',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('134',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('135',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('136',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['63'])).

thf('137',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['134','139'])).

thf('141',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('142',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['133','142'])).

thf('144',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['88','89','92','93'])).

thf('147',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','41','44','57'])).

thf('148',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_tops_2 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['145','146','147'])).

thf('149',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k4_relat_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['132','148'])).

thf('150',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['6','58'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('151',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('152',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('154',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relat_1 @ X1 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('155',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['153','154'])).

thf('156',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['39','40'])).

thf('157',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['155','156','157','158'])).

thf('160',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['152','159'])).

thf('161',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['149','160'])).

thf('162',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['63'])).

thf('164',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['162','163'])).

thf('165',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k4_relat_1 @ sk_C ) )
 != ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['131','164'])).

thf('166',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['61','165'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.v8OhNCrTlR
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:51:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.55/3.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.55/3.72  % Solved by: fo/fo7.sh
% 3.55/3.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.55/3.72  % done 427 iterations in 3.261s
% 3.55/3.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.55/3.72  % SZS output start Refutation
% 3.55/3.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.55/3.72  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 3.55/3.72  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.55/3.72  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.55/3.72  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.55/3.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.55/3.72  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.55/3.72  thf(sk_B_type, type, sk_B: $i).
% 3.55/3.72  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 3.55/3.72  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.55/3.72  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 3.55/3.72  thf(sk_C_type, type, sk_C: $i).
% 3.55/3.72  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 3.55/3.72  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 3.55/3.72  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.55/3.72  thf(sk_A_type, type, sk_A: $i).
% 3.55/3.72  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.55/3.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.55/3.72  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.55/3.72  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 3.55/3.72  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 3.55/3.72  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.55/3.72  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.55/3.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.55/3.72  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 3.55/3.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.55/3.72  thf(t62_tops_2, conjecture,
% 3.55/3.72    (![A:$i]:
% 3.55/3.72     ( ( l1_struct_0 @ A ) =>
% 3.55/3.72       ( ![B:$i]:
% 3.55/3.72         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 3.55/3.72           ( ![C:$i]:
% 3.55/3.72             ( ( ( v1_funct_1 @ C ) & 
% 3.55/3.72                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 3.55/3.72                 ( m1_subset_1 @
% 3.55/3.72                   C @ 
% 3.55/3.72                   ( k1_zfmisc_1 @
% 3.55/3.72                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.55/3.72               ( ( ( ( k2_relset_1 @
% 3.55/3.72                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 3.55/3.72                     ( k2_struct_0 @ B ) ) & 
% 3.55/3.72                   ( v2_funct_1 @ C ) ) =>
% 3.55/3.72                 ( ( ( k1_relset_1 @
% 3.55/3.72                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 3.55/3.72                       ( k2_tops_2 @
% 3.55/3.72                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 3.55/3.72                     ( k2_struct_0 @ B ) ) & 
% 3.55/3.72                   ( ( k2_relset_1 @
% 3.55/3.72                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 3.55/3.72                       ( k2_tops_2 @
% 3.55/3.72                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 3.55/3.72                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 3.55/3.72  thf(zf_stmt_0, negated_conjecture,
% 3.55/3.72    (~( ![A:$i]:
% 3.55/3.72        ( ( l1_struct_0 @ A ) =>
% 3.55/3.72          ( ![B:$i]:
% 3.55/3.72            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 3.55/3.72              ( ![C:$i]:
% 3.55/3.72                ( ( ( v1_funct_1 @ C ) & 
% 3.55/3.72                    ( v1_funct_2 @
% 3.55/3.72                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 3.55/3.72                    ( m1_subset_1 @
% 3.55/3.72                      C @ 
% 3.55/3.72                      ( k1_zfmisc_1 @
% 3.55/3.72                        ( k2_zfmisc_1 @
% 3.55/3.72                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.55/3.72                  ( ( ( ( k2_relset_1 @
% 3.55/3.72                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 3.55/3.72                        ( k2_struct_0 @ B ) ) & 
% 3.55/3.72                      ( v2_funct_1 @ C ) ) =>
% 3.55/3.72                    ( ( ( k1_relset_1 @
% 3.55/3.72                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 3.55/3.72                          ( k2_tops_2 @
% 3.55/3.72                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 3.55/3.72                        ( k2_struct_0 @ B ) ) & 
% 3.55/3.72                      ( ( k2_relset_1 @
% 3.55/3.72                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 3.55/3.72                          ( k2_tops_2 @
% 3.55/3.72                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 3.55/3.72                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 3.55/3.72    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 3.55/3.72  thf('0', plain,
% 3.55/3.72      ((m1_subset_1 @ sk_C @ 
% 3.55/3.72        (k1_zfmisc_1 @ 
% 3.55/3.72         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.55/3.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.72  thf(dt_k3_relset_1, axiom,
% 3.55/3.72    (![A:$i,B:$i,C:$i]:
% 3.55/3.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.55/3.72       ( m1_subset_1 @
% 3.55/3.72         ( k3_relset_1 @ A @ B @ C ) @ 
% 3.55/3.72         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ))).
% 3.55/3.72  thf('1', plain,
% 3.55/3.72      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.55/3.72         ((m1_subset_1 @ (k3_relset_1 @ X8 @ X9 @ X10) @ 
% 3.55/3.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X8)))
% 3.55/3.72          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 3.55/3.72      inference('cnf', [status(esa)], [dt_k3_relset_1])).
% 3.55/3.72  thf('2', plain,
% 3.55/3.72      ((m1_subset_1 @ 
% 3.55/3.72        (k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 3.55/3.72        (k1_zfmisc_1 @ 
% 3.55/3.72         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 3.55/3.72      inference('sup-', [status(thm)], ['0', '1'])).
% 3.55/3.72  thf('3', plain,
% 3.55/3.72      ((m1_subset_1 @ sk_C @ 
% 3.55/3.72        (k1_zfmisc_1 @ 
% 3.55/3.72         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.55/3.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.72  thf(redefinition_k3_relset_1, axiom,
% 3.55/3.72    (![A:$i,B:$i,C:$i]:
% 3.55/3.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.55/3.72       ( ( k3_relset_1 @ A @ B @ C ) = ( k4_relat_1 @ C ) ) ))).
% 3.55/3.72  thf('4', plain,
% 3.55/3.72      (![X17 : $i, X18 : $i, X19 : $i]:
% 3.55/3.72         (((k3_relset_1 @ X18 @ X19 @ X17) = (k4_relat_1 @ X17))
% 3.55/3.72          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 3.55/3.72      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 3.55/3.72  thf('5', plain,
% 3.55/3.72      (((k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.55/3.72         = (k4_relat_1 @ sk_C))),
% 3.55/3.72      inference('sup-', [status(thm)], ['3', '4'])).
% 3.55/3.72  thf('6', plain,
% 3.55/3.72      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 3.55/3.72        (k1_zfmisc_1 @ 
% 3.55/3.72         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 3.55/3.72      inference('demod', [status(thm)], ['2', '5'])).
% 3.55/3.72  thf(d3_struct_0, axiom,
% 3.55/3.72    (![A:$i]:
% 3.55/3.72     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 3.55/3.72  thf('7', plain,
% 3.55/3.72      (![X25 : $i]:
% 3.55/3.72         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 3.55/3.72      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.55/3.72  thf('8', plain,
% 3.55/3.72      ((m1_subset_1 @ sk_C @ 
% 3.55/3.72        (k1_zfmisc_1 @ 
% 3.55/3.72         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.55/3.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.72  thf('9', plain,
% 3.55/3.72      (((m1_subset_1 @ sk_C @ 
% 3.55/3.72         (k1_zfmisc_1 @ 
% 3.55/3.72          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 3.55/3.72        | ~ (l1_struct_0 @ sk_B))),
% 3.55/3.72      inference('sup+', [status(thm)], ['7', '8'])).
% 3.55/3.72  thf('10', plain, ((l1_struct_0 @ sk_B)),
% 3.55/3.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.72  thf('11', plain,
% 3.55/3.72      ((m1_subset_1 @ sk_C @ 
% 3.55/3.72        (k1_zfmisc_1 @ 
% 3.55/3.72         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 3.55/3.72      inference('demod', [status(thm)], ['9', '10'])).
% 3.55/3.72  thf('12', plain,
% 3.55/3.72      ((m1_subset_1 @ sk_C @ 
% 3.55/3.72        (k1_zfmisc_1 @ 
% 3.55/3.72         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.55/3.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.72  thf(redefinition_k2_relset_1, axiom,
% 3.55/3.72    (![A:$i,B:$i,C:$i]:
% 3.55/3.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.55/3.72       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.55/3.72  thf('13', plain,
% 3.55/3.72      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.55/3.72         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 3.55/3.72          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 3.55/3.72      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.55/3.72  thf('14', plain,
% 3.55/3.72      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.55/3.72         = (k2_relat_1 @ sk_C))),
% 3.55/3.72      inference('sup-', [status(thm)], ['12', '13'])).
% 3.55/3.72  thf('15', plain,
% 3.55/3.72      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.55/3.72         = (k2_struct_0 @ sk_B))),
% 3.55/3.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.72  thf('16', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 3.55/3.72      inference('sup+', [status(thm)], ['14', '15'])).
% 3.55/3.72  thf('17', plain,
% 3.55/3.72      ((m1_subset_1 @ sk_C @ 
% 3.55/3.72        (k1_zfmisc_1 @ 
% 3.55/3.72         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 3.55/3.72      inference('demod', [status(thm)], ['11', '16'])).
% 3.55/3.72  thf(cc5_funct_2, axiom,
% 3.55/3.72    (![A:$i,B:$i]:
% 3.55/3.72     ( ( ~( v1_xboole_0 @ B ) ) =>
% 3.55/3.72       ( ![C:$i]:
% 3.55/3.72         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.55/3.72           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 3.55/3.72             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 3.55/3.72  thf('18', plain,
% 3.55/3.72      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.55/3.72         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 3.55/3.72          | (v1_partfun1 @ X20 @ X21)
% 3.55/3.72          | ~ (v1_funct_2 @ X20 @ X21 @ X22)
% 3.55/3.72          | ~ (v1_funct_1 @ X20)
% 3.55/3.72          | (v1_xboole_0 @ X22))),
% 3.55/3.72      inference('cnf', [status(esa)], [cc5_funct_2])).
% 3.55/3.72  thf('19', plain,
% 3.55/3.72      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 3.55/3.72        | ~ (v1_funct_1 @ sk_C)
% 3.55/3.72        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 3.55/3.72        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 3.55/3.72      inference('sup-', [status(thm)], ['17', '18'])).
% 3.55/3.72  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 3.55/3.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.72  thf('21', plain,
% 3.55/3.72      (![X25 : $i]:
% 3.55/3.72         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 3.55/3.72      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.55/3.72  thf('22', plain,
% 3.55/3.72      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.55/3.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.72  thf('23', plain,
% 3.55/3.72      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 3.55/3.72        | ~ (l1_struct_0 @ sk_B))),
% 3.55/3.72      inference('sup+', [status(thm)], ['21', '22'])).
% 3.55/3.72  thf('24', plain, ((l1_struct_0 @ sk_B)),
% 3.55/3.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.72  thf('25', plain,
% 3.55/3.72      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 3.55/3.72      inference('demod', [status(thm)], ['23', '24'])).
% 3.55/3.72  thf('26', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 3.55/3.72      inference('sup+', [status(thm)], ['14', '15'])).
% 3.55/3.72  thf('27', plain,
% 3.55/3.72      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 3.55/3.72      inference('demod', [status(thm)], ['25', '26'])).
% 3.55/3.72  thf('28', plain,
% 3.55/3.72      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 3.55/3.72        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 3.55/3.72      inference('demod', [status(thm)], ['19', '20', '27'])).
% 3.55/3.72  thf('29', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 3.55/3.72      inference('sup+', [status(thm)], ['14', '15'])).
% 3.55/3.72  thf(fc5_struct_0, axiom,
% 3.55/3.72    (![A:$i]:
% 3.55/3.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 3.55/3.72       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 3.55/3.72  thf('30', plain,
% 3.55/3.72      (![X26 : $i]:
% 3.55/3.72         (~ (v1_xboole_0 @ (k2_struct_0 @ X26))
% 3.55/3.72          | ~ (l1_struct_0 @ X26)
% 3.55/3.72          | (v2_struct_0 @ X26))),
% 3.55/3.72      inference('cnf', [status(esa)], [fc5_struct_0])).
% 3.55/3.72  thf('31', plain,
% 3.55/3.72      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 3.55/3.72        | (v2_struct_0 @ sk_B)
% 3.55/3.72        | ~ (l1_struct_0 @ sk_B))),
% 3.55/3.72      inference('sup-', [status(thm)], ['29', '30'])).
% 3.55/3.72  thf('32', plain, ((l1_struct_0 @ sk_B)),
% 3.55/3.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.72  thf('33', plain,
% 3.55/3.72      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 3.55/3.72      inference('demod', [status(thm)], ['31', '32'])).
% 3.55/3.72  thf('34', plain, (~ (v2_struct_0 @ sk_B)),
% 3.55/3.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.72  thf('35', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 3.55/3.72      inference('clc', [status(thm)], ['33', '34'])).
% 3.55/3.72  thf('36', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 3.55/3.72      inference('clc', [status(thm)], ['28', '35'])).
% 3.55/3.72  thf(d4_partfun1, axiom,
% 3.55/3.72    (![A:$i,B:$i]:
% 3.55/3.72     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 3.55/3.72       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 3.55/3.72  thf('37', plain,
% 3.55/3.72      (![X23 : $i, X24 : $i]:
% 3.55/3.72         (~ (v1_partfun1 @ X24 @ X23)
% 3.55/3.72          | ((k1_relat_1 @ X24) = (X23))
% 3.55/3.72          | ~ (v4_relat_1 @ X24 @ X23)
% 3.55/3.72          | ~ (v1_relat_1 @ X24))),
% 3.55/3.72      inference('cnf', [status(esa)], [d4_partfun1])).
% 3.55/3.72  thf('38', plain,
% 3.55/3.72      ((~ (v1_relat_1 @ sk_C)
% 3.55/3.72        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 3.55/3.72        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 3.55/3.72      inference('sup-', [status(thm)], ['36', '37'])).
% 3.55/3.72  thf('39', plain,
% 3.55/3.72      ((m1_subset_1 @ sk_C @ 
% 3.55/3.72        (k1_zfmisc_1 @ 
% 3.55/3.72         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.55/3.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.72  thf(cc1_relset_1, axiom,
% 3.55/3.72    (![A:$i,B:$i,C:$i]:
% 3.55/3.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.55/3.72       ( v1_relat_1 @ C ) ))).
% 3.55/3.72  thf('40', plain,
% 3.55/3.72      (![X2 : $i, X3 : $i, X4 : $i]:
% 3.55/3.72         ((v1_relat_1 @ X2)
% 3.55/3.72          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 3.55/3.72      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.55/3.72  thf('41', plain, ((v1_relat_1 @ sk_C)),
% 3.55/3.72      inference('sup-', [status(thm)], ['39', '40'])).
% 3.55/3.72  thf('42', plain,
% 3.55/3.72      ((m1_subset_1 @ sk_C @ 
% 3.55/3.72        (k1_zfmisc_1 @ 
% 3.55/3.72         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.55/3.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.72  thf(cc2_relset_1, axiom,
% 3.55/3.72    (![A:$i,B:$i,C:$i]:
% 3.55/3.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.55/3.72       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.55/3.72  thf('43', plain,
% 3.55/3.72      (![X5 : $i, X6 : $i, X7 : $i]:
% 3.55/3.72         ((v4_relat_1 @ X5 @ X6)
% 3.55/3.72          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 3.55/3.72      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.55/3.72  thf('44', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 3.55/3.72      inference('sup-', [status(thm)], ['42', '43'])).
% 3.55/3.72  thf('45', plain, ((v1_funct_1 @ sk_C)),
% 3.55/3.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.72  thf(d9_funct_1, axiom,
% 3.55/3.72    (![A:$i]:
% 3.55/3.72     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.55/3.72       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 3.55/3.72  thf('46', plain,
% 3.55/3.72      (![X0 : $i]:
% 3.55/3.72         (~ (v2_funct_1 @ X0)
% 3.55/3.72          | ((k2_funct_1 @ X0) = (k4_relat_1 @ X0))
% 3.55/3.72          | ~ (v1_funct_1 @ X0)
% 3.55/3.72          | ~ (v1_relat_1 @ X0))),
% 3.55/3.72      inference('cnf', [status(esa)], [d9_funct_1])).
% 3.55/3.72  thf('47', plain,
% 3.55/3.72      ((~ (v1_relat_1 @ sk_C)
% 3.55/3.72        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 3.55/3.72        | ~ (v2_funct_1 @ sk_C))),
% 3.55/3.72      inference('sup-', [status(thm)], ['45', '46'])).
% 3.55/3.72  thf('48', plain, ((v2_funct_1 @ sk_C)),
% 3.55/3.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.72  thf('49', plain,
% 3.55/3.72      ((~ (v1_relat_1 @ sk_C) | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C)))),
% 3.55/3.72      inference('demod', [status(thm)], ['47', '48'])).
% 3.55/3.72  thf('50', plain, ((v1_relat_1 @ sk_C)),
% 3.55/3.72      inference('sup-', [status(thm)], ['39', '40'])).
% 3.55/3.72  thf('51', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 3.55/3.72      inference('demod', [status(thm)], ['49', '50'])).
% 3.55/3.72  thf(t55_funct_1, axiom,
% 3.55/3.72    (![A:$i]:
% 3.55/3.72     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.55/3.72       ( ( v2_funct_1 @ A ) =>
% 3.55/3.72         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 3.55/3.72           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 3.55/3.72  thf('52', plain,
% 3.55/3.72      (![X1 : $i]:
% 3.55/3.72         (~ (v2_funct_1 @ X1)
% 3.55/3.72          | ((k1_relat_1 @ X1) = (k2_relat_1 @ (k2_funct_1 @ X1)))
% 3.55/3.72          | ~ (v1_funct_1 @ X1)
% 3.55/3.72          | ~ (v1_relat_1 @ X1))),
% 3.55/3.72      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.55/3.72  thf('53', plain,
% 3.55/3.72      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 3.55/3.72        | ~ (v1_relat_1 @ sk_C)
% 3.55/3.72        | ~ (v1_funct_1 @ sk_C)
% 3.55/3.72        | ~ (v2_funct_1 @ sk_C))),
% 3.55/3.72      inference('sup+', [status(thm)], ['51', '52'])).
% 3.55/3.72  thf('54', plain, ((v1_relat_1 @ sk_C)),
% 3.55/3.72      inference('sup-', [status(thm)], ['39', '40'])).
% 3.55/3.72  thf('55', plain, ((v1_funct_1 @ sk_C)),
% 3.55/3.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.72  thf('56', plain, ((v2_funct_1 @ sk_C)),
% 3.55/3.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.72  thf('57', plain,
% 3.55/3.72      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 3.55/3.72      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 3.55/3.72  thf('58', plain,
% 3.55/3.72      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (u1_struct_0 @ sk_A))),
% 3.55/3.72      inference('demod', [status(thm)], ['38', '41', '44', '57'])).
% 3.55/3.72  thf('59', plain,
% 3.55/3.72      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 3.55/3.72        (k1_zfmisc_1 @ 
% 3.55/3.72         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 3.55/3.72          (k2_relat_1 @ (k4_relat_1 @ sk_C)))))),
% 3.55/3.72      inference('demod', [status(thm)], ['6', '58'])).
% 3.55/3.72  thf('60', plain,
% 3.55/3.72      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.55/3.72         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 3.55/3.72          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 3.55/3.72      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.55/3.72  thf('61', plain,
% 3.55/3.72      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 3.55/3.72         (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ (k4_relat_1 @ sk_C))
% 3.55/3.72         = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 3.55/3.72      inference('sup-', [status(thm)], ['59', '60'])).
% 3.55/3.72  thf('62', plain,
% 3.55/3.72      (![X25 : $i]:
% 3.55/3.72         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 3.55/3.72      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.55/3.72  thf('63', plain,
% 3.55/3.72      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.55/3.72          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.55/3.72          != (k2_struct_0 @ sk_B))
% 3.55/3.72        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.55/3.72            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.55/3.72            != (k2_struct_0 @ sk_A)))),
% 3.55/3.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.72  thf('64', plain,
% 3.55/3.72      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.55/3.72          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.55/3.72          != (k2_struct_0 @ sk_A)))
% 3.55/3.72         <= (~
% 3.55/3.72             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.55/3.72                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.55/3.72                = (k2_struct_0 @ sk_A))))),
% 3.55/3.72      inference('split', [status(esa)], ['63'])).
% 3.55/3.72  thf('65', plain,
% 3.55/3.72      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.55/3.72           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 3.55/3.72           != (k2_struct_0 @ sk_A))
% 3.55/3.72         | ~ (l1_struct_0 @ sk_B)))
% 3.55/3.72         <= (~
% 3.55/3.72             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.55/3.72                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.55/3.72                = (k2_struct_0 @ sk_A))))),
% 3.55/3.72      inference('sup-', [status(thm)], ['62', '64'])).
% 3.55/3.72  thf('66', plain, ((l1_struct_0 @ sk_B)),
% 3.55/3.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.72  thf('67', plain,
% 3.55/3.72      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.55/3.72          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 3.55/3.72          != (k2_struct_0 @ sk_A)))
% 3.55/3.72         <= (~
% 3.55/3.72             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.55/3.72                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.55/3.72                = (k2_struct_0 @ sk_A))))),
% 3.55/3.72      inference('demod', [status(thm)], ['65', '66'])).
% 3.55/3.72  thf('68', plain,
% 3.55/3.72      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (u1_struct_0 @ sk_A))),
% 3.55/3.72      inference('demod', [status(thm)], ['38', '41', '44', '57'])).
% 3.55/3.72  thf('69', plain,
% 3.55/3.72      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (u1_struct_0 @ sk_A))),
% 3.55/3.72      inference('demod', [status(thm)], ['38', '41', '44', '57'])).
% 3.55/3.72  thf('70', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 3.55/3.72      inference('sup+', [status(thm)], ['14', '15'])).
% 3.55/3.72  thf('71', plain,
% 3.55/3.72      (![X25 : $i]:
% 3.55/3.72         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 3.55/3.72      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.55/3.72  thf('72', plain,
% 3.55/3.72      (![X25 : $i]:
% 3.55/3.72         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 3.55/3.72      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.55/3.72  thf('73', plain,
% 3.55/3.72      ((m1_subset_1 @ sk_C @ 
% 3.55/3.72        (k1_zfmisc_1 @ 
% 3.55/3.72         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.55/3.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.72  thf('74', plain,
% 3.55/3.72      (((m1_subset_1 @ sk_C @ 
% 3.55/3.72         (k1_zfmisc_1 @ 
% 3.55/3.72          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 3.55/3.72        | ~ (l1_struct_0 @ sk_A))),
% 3.55/3.72      inference('sup+', [status(thm)], ['72', '73'])).
% 3.55/3.72  thf('75', plain, ((l1_struct_0 @ sk_A)),
% 3.55/3.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.72  thf('76', plain,
% 3.55/3.72      ((m1_subset_1 @ sk_C @ 
% 3.55/3.72        (k1_zfmisc_1 @ 
% 3.55/3.72         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.55/3.72      inference('demod', [status(thm)], ['74', '75'])).
% 3.55/3.72  thf('77', plain,
% 3.55/3.72      (((m1_subset_1 @ sk_C @ 
% 3.55/3.72         (k1_zfmisc_1 @ 
% 3.55/3.72          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 3.55/3.72        | ~ (l1_struct_0 @ sk_B))),
% 3.55/3.72      inference('sup+', [status(thm)], ['71', '76'])).
% 3.55/3.72  thf('78', plain, ((l1_struct_0 @ sk_B)),
% 3.55/3.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.72  thf('79', plain,
% 3.55/3.72      ((m1_subset_1 @ sk_C @ 
% 3.55/3.72        (k1_zfmisc_1 @ 
% 3.55/3.72         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 3.55/3.72      inference('demod', [status(thm)], ['77', '78'])).
% 3.55/3.72  thf('80', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 3.55/3.72      inference('sup+', [status(thm)], ['14', '15'])).
% 3.55/3.72  thf('81', plain,
% 3.55/3.72      ((m1_subset_1 @ sk_C @ 
% 3.55/3.72        (k1_zfmisc_1 @ 
% 3.55/3.72         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 3.55/3.72      inference('demod', [status(thm)], ['79', '80'])).
% 3.55/3.72  thf('82', plain,
% 3.55/3.72      (![X25 : $i]:
% 3.55/3.72         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 3.55/3.72      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.55/3.72  thf('83', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 3.55/3.72      inference('clc', [status(thm)], ['28', '35'])).
% 3.55/3.72  thf('84', plain,
% 3.55/3.72      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 3.55/3.72      inference('sup+', [status(thm)], ['82', '83'])).
% 3.55/3.72  thf('85', plain, ((l1_struct_0 @ sk_A)),
% 3.55/3.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.72  thf('86', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 3.55/3.72      inference('demod', [status(thm)], ['84', '85'])).
% 3.55/3.72  thf('87', plain,
% 3.55/3.72      (![X23 : $i, X24 : $i]:
% 3.55/3.72         (~ (v1_partfun1 @ X24 @ X23)
% 3.55/3.72          | ((k1_relat_1 @ X24) = (X23))
% 3.55/3.72          | ~ (v4_relat_1 @ X24 @ X23)
% 3.55/3.72          | ~ (v1_relat_1 @ X24))),
% 3.55/3.72      inference('cnf', [status(esa)], [d4_partfun1])).
% 3.55/3.72  thf('88', plain,
% 3.55/3.72      ((~ (v1_relat_1 @ sk_C)
% 3.55/3.72        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 3.55/3.72        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 3.55/3.72      inference('sup-', [status(thm)], ['86', '87'])).
% 3.55/3.72  thf('89', plain, ((v1_relat_1 @ sk_C)),
% 3.55/3.72      inference('sup-', [status(thm)], ['39', '40'])).
% 3.55/3.72  thf('90', plain,
% 3.55/3.72      ((m1_subset_1 @ sk_C @ 
% 3.55/3.72        (k1_zfmisc_1 @ 
% 3.55/3.72         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.55/3.72      inference('demod', [status(thm)], ['74', '75'])).
% 3.55/3.72  thf('91', plain,
% 3.55/3.72      (![X5 : $i, X6 : $i, X7 : $i]:
% 3.55/3.72         ((v4_relat_1 @ X5 @ X6)
% 3.55/3.72          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 3.55/3.72      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.55/3.72  thf('92', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 3.55/3.72      inference('sup-', [status(thm)], ['90', '91'])).
% 3.55/3.72  thf('93', plain,
% 3.55/3.72      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 3.55/3.72      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 3.55/3.72  thf('94', plain,
% 3.55/3.72      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 3.55/3.72      inference('demod', [status(thm)], ['88', '89', '92', '93'])).
% 3.55/3.72  thf('95', plain,
% 3.55/3.72      ((m1_subset_1 @ sk_C @ 
% 3.55/3.72        (k1_zfmisc_1 @ 
% 3.55/3.72         (k2_zfmisc_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 3.55/3.72          (k2_relat_1 @ sk_C))))),
% 3.55/3.72      inference('demod', [status(thm)], ['81', '94'])).
% 3.55/3.72  thf(d4_tops_2, axiom,
% 3.55/3.72    (![A:$i,B:$i,C:$i]:
% 3.55/3.72     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.55/3.72         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.55/3.72       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 3.55/3.72         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 3.55/3.72  thf('96', plain,
% 3.55/3.72      (![X27 : $i, X28 : $i, X29 : $i]:
% 3.55/3.72         (((k2_relset_1 @ X28 @ X27 @ X29) != (X27))
% 3.55/3.72          | ~ (v2_funct_1 @ X29)
% 3.55/3.72          | ((k2_tops_2 @ X28 @ X27 @ X29) = (k2_funct_1 @ X29))
% 3.55/3.72          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 3.55/3.72          | ~ (v1_funct_2 @ X29 @ X28 @ X27)
% 3.55/3.72          | ~ (v1_funct_1 @ X29))),
% 3.55/3.72      inference('cnf', [status(esa)], [d4_tops_2])).
% 3.55/3.72  thf('97', plain,
% 3.55/3.72      ((~ (v1_funct_1 @ sk_C)
% 3.55/3.72        | ~ (v1_funct_2 @ sk_C @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 3.55/3.72             (k2_relat_1 @ sk_C))
% 3.55/3.72        | ((k2_tops_2 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 3.55/3.72            (k2_relat_1 @ sk_C) @ sk_C) = (k2_funct_1 @ sk_C))
% 3.55/3.72        | ~ (v2_funct_1 @ sk_C)
% 3.55/3.72        | ((k2_relset_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 3.55/3.72            (k2_relat_1 @ sk_C) @ sk_C) != (k2_relat_1 @ sk_C)))),
% 3.55/3.72      inference('sup-', [status(thm)], ['95', '96'])).
% 3.55/3.72  thf('98', plain, ((v1_funct_1 @ sk_C)),
% 3.55/3.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.72  thf('99', plain,
% 3.55/3.72      (![X25 : $i]:
% 3.55/3.72         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 3.55/3.72      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.55/3.72  thf('100', plain,
% 3.55/3.72      (![X25 : $i]:
% 3.55/3.72         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 3.55/3.72      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.55/3.72  thf('101', plain,
% 3.55/3.72      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.55/3.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.72  thf('102', plain,
% 3.55/3.72      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.55/3.72        | ~ (l1_struct_0 @ sk_A))),
% 3.55/3.72      inference('sup+', [status(thm)], ['100', '101'])).
% 3.55/3.72  thf('103', plain, ((l1_struct_0 @ sk_A)),
% 3.55/3.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.72  thf('104', plain,
% 3.55/3.72      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.55/3.72      inference('demod', [status(thm)], ['102', '103'])).
% 3.55/3.72  thf('105', plain,
% 3.55/3.72      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 3.55/3.72        | ~ (l1_struct_0 @ sk_B))),
% 3.55/3.72      inference('sup+', [status(thm)], ['99', '104'])).
% 3.55/3.72  thf('106', plain, ((l1_struct_0 @ sk_B)),
% 3.55/3.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.72  thf('107', plain,
% 3.55/3.72      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 3.55/3.72      inference('demod', [status(thm)], ['105', '106'])).
% 3.55/3.72  thf('108', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 3.55/3.72      inference('sup+', [status(thm)], ['14', '15'])).
% 3.55/3.72  thf('109', plain,
% 3.55/3.72      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 3.55/3.72      inference('demod', [status(thm)], ['107', '108'])).
% 3.55/3.72  thf('110', plain,
% 3.55/3.72      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 3.55/3.72      inference('demod', [status(thm)], ['88', '89', '92', '93'])).
% 3.55/3.72  thf('111', plain,
% 3.55/3.72      ((v1_funct_2 @ sk_C @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 3.55/3.72        (k2_relat_1 @ sk_C))),
% 3.55/3.72      inference('demod', [status(thm)], ['109', '110'])).
% 3.55/3.72  thf('112', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 3.55/3.72      inference('demod', [status(thm)], ['49', '50'])).
% 3.55/3.72  thf('113', plain, ((v2_funct_1 @ sk_C)),
% 3.55/3.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.72  thf('114', plain,
% 3.55/3.72      (![X25 : $i]:
% 3.55/3.72         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 3.55/3.72      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.55/3.72  thf('115', plain,
% 3.55/3.72      (![X25 : $i]:
% 3.55/3.72         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 3.55/3.72      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.55/3.72  thf('116', plain,
% 3.55/3.72      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.55/3.72         = (k2_struct_0 @ sk_B))),
% 3.55/3.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.72  thf('117', plain,
% 3.55/3.72      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.55/3.72          = (k2_struct_0 @ sk_B))
% 3.55/3.72        | ~ (l1_struct_0 @ sk_B))),
% 3.55/3.72      inference('sup+', [status(thm)], ['115', '116'])).
% 3.55/3.72  thf('118', plain, ((l1_struct_0 @ sk_B)),
% 3.55/3.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.72  thf('119', plain,
% 3.55/3.72      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.55/3.72         = (k2_struct_0 @ sk_B))),
% 3.55/3.72      inference('demod', [status(thm)], ['117', '118'])).
% 3.55/3.72  thf('120', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 3.55/3.72      inference('sup+', [status(thm)], ['14', '15'])).
% 3.55/3.72  thf('121', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 3.55/3.72      inference('sup+', [status(thm)], ['14', '15'])).
% 3.55/3.72  thf('122', plain,
% 3.55/3.72      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 3.55/3.72         = (k2_relat_1 @ sk_C))),
% 3.55/3.72      inference('demod', [status(thm)], ['119', '120', '121'])).
% 3.55/3.72  thf('123', plain,
% 3.55/3.72      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 3.55/3.72          = (k2_relat_1 @ sk_C))
% 3.55/3.72        | ~ (l1_struct_0 @ sk_A))),
% 3.55/3.72      inference('sup+', [status(thm)], ['114', '122'])).
% 3.55/3.72  thf('124', plain, ((l1_struct_0 @ sk_A)),
% 3.55/3.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.72  thf('125', plain,
% 3.55/3.72      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 3.55/3.72         = (k2_relat_1 @ sk_C))),
% 3.55/3.72      inference('demod', [status(thm)], ['123', '124'])).
% 3.55/3.72  thf('126', plain,
% 3.55/3.72      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 3.55/3.72      inference('demod', [status(thm)], ['88', '89', '92', '93'])).
% 3.55/3.72  thf('127', plain,
% 3.55/3.72      (((k2_relset_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 3.55/3.72         (k2_relat_1 @ sk_C) @ sk_C) = (k2_relat_1 @ sk_C))),
% 3.55/3.72      inference('demod', [status(thm)], ['125', '126'])).
% 3.55/3.72  thf('128', plain,
% 3.55/3.72      ((((k2_tops_2 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 3.55/3.72          (k2_relat_1 @ sk_C) @ sk_C) = (k4_relat_1 @ sk_C))
% 3.55/3.72        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 3.55/3.72      inference('demod', [status(thm)],
% 3.55/3.72                ['97', '98', '111', '112', '113', '127'])).
% 3.55/3.72  thf('129', plain,
% 3.55/3.72      (((k2_tops_2 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 3.55/3.72         (k2_relat_1 @ sk_C) @ sk_C) = (k4_relat_1 @ sk_C))),
% 3.55/3.72      inference('simplify', [status(thm)], ['128'])).
% 3.55/3.72  thf('130', plain,
% 3.55/3.72      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 3.55/3.72      inference('demod', [status(thm)], ['88', '89', '92', '93'])).
% 3.55/3.72  thf('131', plain,
% 3.55/3.72      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 3.55/3.72          (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ (k4_relat_1 @ sk_C))
% 3.55/3.72          != (k2_relat_1 @ (k4_relat_1 @ sk_C))))
% 3.55/3.72         <= (~
% 3.55/3.72             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.55/3.72                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.55/3.72                = (k2_struct_0 @ sk_A))))),
% 3.55/3.72      inference('demod', [status(thm)], ['67', '68', '69', '70', '129', '130'])).
% 3.55/3.72  thf('132', plain,
% 3.55/3.72      (((k2_tops_2 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 3.55/3.72         (k2_relat_1 @ sk_C) @ sk_C) = (k4_relat_1 @ sk_C))),
% 3.55/3.72      inference('simplify', [status(thm)], ['128'])).
% 3.55/3.72  thf('133', plain,
% 3.55/3.72      (![X25 : $i]:
% 3.55/3.72         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 3.55/3.72      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.55/3.72  thf('134', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 3.55/3.72      inference('sup+', [status(thm)], ['14', '15'])).
% 3.55/3.72  thf('135', plain,
% 3.55/3.72      (![X25 : $i]:
% 3.55/3.72         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 3.55/3.72      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.55/3.72  thf('136', plain,
% 3.55/3.72      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.55/3.72          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.55/3.72          != (k2_struct_0 @ sk_B)))
% 3.55/3.72         <= (~
% 3.55/3.72             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.55/3.72                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.55/3.72                = (k2_struct_0 @ sk_B))))),
% 3.55/3.72      inference('split', [status(esa)], ['63'])).
% 3.55/3.72  thf('137', plain,
% 3.55/3.72      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.55/3.72           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 3.55/3.72           != (k2_struct_0 @ sk_B))
% 3.55/3.72         | ~ (l1_struct_0 @ sk_B)))
% 3.55/3.72         <= (~
% 3.55/3.72             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.55/3.72                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.55/3.72                = (k2_struct_0 @ sk_B))))),
% 3.55/3.72      inference('sup-', [status(thm)], ['135', '136'])).
% 3.55/3.72  thf('138', plain, ((l1_struct_0 @ sk_B)),
% 3.55/3.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.72  thf('139', plain,
% 3.55/3.72      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.55/3.72          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 3.55/3.72          != (k2_struct_0 @ sk_B)))
% 3.55/3.72         <= (~
% 3.55/3.72             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.55/3.72                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.55/3.72                = (k2_struct_0 @ sk_B))))),
% 3.55/3.72      inference('demod', [status(thm)], ['137', '138'])).
% 3.55/3.72  thf('140', plain,
% 3.55/3.72      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.55/3.72          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 3.55/3.72          != (k2_struct_0 @ sk_B)))
% 3.55/3.72         <= (~
% 3.55/3.72             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.55/3.72                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.55/3.72                = (k2_struct_0 @ sk_B))))),
% 3.55/3.72      inference('sup-', [status(thm)], ['134', '139'])).
% 3.55/3.72  thf('141', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 3.55/3.72      inference('sup+', [status(thm)], ['14', '15'])).
% 3.55/3.72  thf('142', plain,
% 3.55/3.72      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.55/3.72          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 3.55/3.72          != (k2_relat_1 @ sk_C)))
% 3.55/3.72         <= (~
% 3.55/3.72             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.55/3.72                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.55/3.72                = (k2_struct_0 @ sk_B))))),
% 3.55/3.72      inference('demod', [status(thm)], ['140', '141'])).
% 3.55/3.72  thf('143', plain,
% 3.55/3.72      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.55/3.72           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 3.55/3.72           != (k2_relat_1 @ sk_C))
% 3.55/3.72         | ~ (l1_struct_0 @ sk_A)))
% 3.55/3.72         <= (~
% 3.55/3.72             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.55/3.72                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.55/3.72                = (k2_struct_0 @ sk_B))))),
% 3.55/3.72      inference('sup-', [status(thm)], ['133', '142'])).
% 3.55/3.72  thf('144', plain, ((l1_struct_0 @ sk_A)),
% 3.55/3.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.72  thf('145', plain,
% 3.55/3.72      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.55/3.72          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 3.55/3.72          != (k2_relat_1 @ sk_C)))
% 3.55/3.72         <= (~
% 3.55/3.72             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.55/3.72                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.55/3.72                = (k2_struct_0 @ sk_B))))),
% 3.55/3.72      inference('demod', [status(thm)], ['143', '144'])).
% 3.55/3.72  thf('146', plain,
% 3.55/3.72      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 3.55/3.72      inference('demod', [status(thm)], ['88', '89', '92', '93'])).
% 3.55/3.72  thf('147', plain,
% 3.55/3.72      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (u1_struct_0 @ sk_A))),
% 3.55/3.72      inference('demod', [status(thm)], ['38', '41', '44', '57'])).
% 3.55/3.72  thf('148', plain,
% 3.55/3.72      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 3.55/3.72          (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 3.55/3.72          (k2_tops_2 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 3.55/3.72           (k2_relat_1 @ sk_C) @ sk_C))
% 3.55/3.72          != (k2_relat_1 @ sk_C)))
% 3.55/3.72         <= (~
% 3.55/3.72             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.55/3.72                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.55/3.72                = (k2_struct_0 @ sk_B))))),
% 3.55/3.72      inference('demod', [status(thm)], ['145', '146', '147'])).
% 3.55/3.72  thf('149', plain,
% 3.55/3.72      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 3.55/3.72          (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ (k4_relat_1 @ sk_C))
% 3.55/3.72          != (k2_relat_1 @ sk_C)))
% 3.55/3.72         <= (~
% 3.55/3.72             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.55/3.72                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.55/3.72                = (k2_struct_0 @ sk_B))))),
% 3.55/3.72      inference('sup-', [status(thm)], ['132', '148'])).
% 3.55/3.72  thf('150', plain,
% 3.55/3.72      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 3.55/3.72        (k1_zfmisc_1 @ 
% 3.55/3.72         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 3.55/3.72          (k2_relat_1 @ (k4_relat_1 @ sk_C)))))),
% 3.55/3.72      inference('demod', [status(thm)], ['6', '58'])).
% 3.55/3.72  thf(redefinition_k1_relset_1, axiom,
% 3.55/3.72    (![A:$i,B:$i,C:$i]:
% 3.55/3.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.55/3.72       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.55/3.72  thf('151', plain,
% 3.55/3.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 3.55/3.72         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 3.55/3.72          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 3.55/3.72      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.55/3.72  thf('152', plain,
% 3.55/3.72      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 3.55/3.72         (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ (k4_relat_1 @ sk_C))
% 3.55/3.72         = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 3.55/3.72      inference('sup-', [status(thm)], ['150', '151'])).
% 3.55/3.72  thf('153', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 3.55/3.72      inference('demod', [status(thm)], ['49', '50'])).
% 3.55/3.72  thf('154', plain,
% 3.55/3.72      (![X1 : $i]:
% 3.55/3.72         (~ (v2_funct_1 @ X1)
% 3.55/3.72          | ((k2_relat_1 @ X1) = (k1_relat_1 @ (k2_funct_1 @ X1)))
% 3.55/3.72          | ~ (v1_funct_1 @ X1)
% 3.55/3.72          | ~ (v1_relat_1 @ X1))),
% 3.55/3.72      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.55/3.72  thf('155', plain,
% 3.55/3.72      ((((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))
% 3.55/3.72        | ~ (v1_relat_1 @ sk_C)
% 3.55/3.72        | ~ (v1_funct_1 @ sk_C)
% 3.55/3.72        | ~ (v2_funct_1 @ sk_C))),
% 3.55/3.72      inference('sup+', [status(thm)], ['153', '154'])).
% 3.55/3.72  thf('156', plain, ((v1_relat_1 @ sk_C)),
% 3.55/3.72      inference('sup-', [status(thm)], ['39', '40'])).
% 3.55/3.72  thf('157', plain, ((v1_funct_1 @ sk_C)),
% 3.55/3.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.72  thf('158', plain, ((v2_funct_1 @ sk_C)),
% 3.55/3.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.55/3.72  thf('159', plain,
% 3.55/3.72      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 3.55/3.72      inference('demod', [status(thm)], ['155', '156', '157', '158'])).
% 3.55/3.72  thf('160', plain,
% 3.55/3.72      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 3.55/3.72         (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ (k4_relat_1 @ sk_C))
% 3.55/3.72         = (k2_relat_1 @ sk_C))),
% 3.55/3.72      inference('demod', [status(thm)], ['152', '159'])).
% 3.55/3.72  thf('161', plain,
% 3.55/3.72      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 3.55/3.72         <= (~
% 3.55/3.72             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.55/3.72                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.55/3.72                = (k2_struct_0 @ sk_B))))),
% 3.55/3.72      inference('demod', [status(thm)], ['149', '160'])).
% 3.55/3.72  thf('162', plain,
% 3.55/3.72      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.55/3.72          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.55/3.72          = (k2_struct_0 @ sk_B)))),
% 3.55/3.72      inference('simplify', [status(thm)], ['161'])).
% 3.55/3.72  thf('163', plain,
% 3.55/3.72      (~
% 3.55/3.72       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.55/3.72          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.55/3.72          = (k2_struct_0 @ sk_A))) | 
% 3.55/3.72       ~
% 3.55/3.72       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.55/3.72          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.55/3.72          = (k2_struct_0 @ sk_B)))),
% 3.55/3.72      inference('split', [status(esa)], ['63'])).
% 3.55/3.72  thf('164', plain,
% 3.55/3.72      (~
% 3.55/3.72       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.55/3.72          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.55/3.72          = (k2_struct_0 @ sk_A)))),
% 3.55/3.72      inference('sat_resolution*', [status(thm)], ['162', '163'])).
% 3.55/3.72  thf('165', plain,
% 3.55/3.72      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 3.55/3.72         (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ (k4_relat_1 @ sk_C))
% 3.55/3.72         != (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 3.55/3.72      inference('simpl_trail', [status(thm)], ['131', '164'])).
% 3.55/3.72  thf('166', plain, ($false),
% 3.55/3.72      inference('simplify_reflect-', [status(thm)], ['61', '165'])).
% 3.55/3.72  
% 3.55/3.72  % SZS output end Refutation
% 3.55/3.72  
% 3.55/3.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
