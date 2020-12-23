%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vTztS7hn0X

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:00 EST 2020

% Result     : Theorem 3.01s
% Output     : Refutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :  210 (2202 expanded)
%              Number of leaves         :   41 ( 664 expanded)
%              Depth                    :   22
%              Number of atoms          : 1848 (54905 expanded)
%              Number of equality atoms :  123 (2764 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( k3_relset_1 @ X9 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k3_relset_1 @ X19 @ X20 @ X18 )
        = ( k4_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
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
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( v1_partfun1 @ X21 @ X22 )
      | ~ ( v1_funct_2 @ X21 @ X22 @ X23 )
      | ~ ( v1_funct_1 @ X21 )
      | ( v1_xboole_0 @ X23 ) ) ),
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
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
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
    ! [X27: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_partfun1 @ X25 @ X24 )
      | ( ( k1_relat_1 @ X25 )
        = X24 )
      | ~ ( v4_relat_1 @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('42',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('43',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('45',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('46',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('48',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_funct_1 @ X4 )
        = ( k4_relat_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('51',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('53',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('54',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('56',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['54','55','56','57'])).

thf('59',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','43','46','58'])).

thf('60',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['6','59'])).

thf('61',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('62',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('64',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['64'])).

thf('66',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','65'])).

thf('67',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','43','46','58'])).

thf('70',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','43','46','58'])).

thf('71',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('72',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('73',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['72','77'])).

thf('79',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('84',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['28','35'])).

thf('85',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_partfun1 @ X25 @ X24 )
      | ( ( k1_relat_1 @ X25 )
        = X24 )
      | ~ ( v4_relat_1 @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('89',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('91',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('92',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('93',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['54','55','56','57'])).

thf('95',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['89','90','93','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['82','95'])).

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

thf('97',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X28 @ X30 )
       != X28 )
      | ~ ( v2_funct_1 @ X30 )
      | ( ( k2_tops_2 @ X29 @ X28 @ X30 )
        = ( k2_funct_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('98',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('101',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('102',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['100','105'])).

thf('107',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('110',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['89','90','93','94'])).

thf('112',plain,(
    v1_funct_2 @ sk_C @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('114',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('116',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('117',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['115','120'])).

thf('122',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('125',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('126',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['89','90','93','94'])).

thf('128',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['98','99','112','113','114','128'])).

thf('130',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['89','90','93','94'])).

thf('132',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k4_relat_1 @ sk_C ) )
     != ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69','70','71','130','131'])).

thf('133',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['129'])).

thf('134',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('135',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('136',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('137',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['64'])).

thf('138',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['135','140'])).

thf('142',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['134','143'])).

thf('145',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('146',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['89','90','93','94'])).

thf('148',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['38','43','46','58'])).

thf('149',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_tops_2 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['146','147','148'])).

thf('150',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k4_relat_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['133','149'])).

thf('151',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['6','59'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('152',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('153',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('155',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('156',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['154','155'])).

thf('157',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('158',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['156','157','158','159'])).

thf('161',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['153','160'])).

thf('162',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['150','161'])).

thf('163',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['64'])).

thf('165',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['163','164'])).

thf('166',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ ( k4_relat_1 @ sk_C ) )
 != ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['132','165'])).

thf('167',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['62','166'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vTztS7hn0X
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:53:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 3.01/3.24  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.01/3.24  % Solved by: fo/fo7.sh
% 3.01/3.24  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.01/3.24  % done 390 iterations in 2.786s
% 3.01/3.24  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.01/3.24  % SZS output start Refutation
% 3.01/3.24  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 3.01/3.24  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.01/3.24  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.01/3.24  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 3.01/3.24  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.01/3.24  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.01/3.24  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.01/3.24  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.01/3.24  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 3.01/3.24  thf(sk_A_type, type, sk_A: $i).
% 3.01/3.24  thf(sk_C_type, type, sk_C: $i).
% 3.01/3.24  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.01/3.24  thf(sk_B_type, type, sk_B: $i).
% 3.01/3.24  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.01/3.24  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.01/3.24  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.01/3.24  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 3.01/3.24  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 3.01/3.24  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 3.01/3.24  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.01/3.24  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 3.01/3.24  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.01/3.24  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 3.01/3.24  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.01/3.24  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.01/3.24  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.01/3.24  thf(t62_tops_2, conjecture,
% 3.01/3.24    (![A:$i]:
% 3.01/3.24     ( ( l1_struct_0 @ A ) =>
% 3.01/3.24       ( ![B:$i]:
% 3.01/3.24         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 3.01/3.24           ( ![C:$i]:
% 3.01/3.24             ( ( ( v1_funct_1 @ C ) & 
% 3.01/3.24                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 3.01/3.24                 ( m1_subset_1 @
% 3.01/3.24                   C @ 
% 3.01/3.24                   ( k1_zfmisc_1 @
% 3.01/3.24                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.01/3.24               ( ( ( ( k2_relset_1 @
% 3.01/3.24                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 3.01/3.24                     ( k2_struct_0 @ B ) ) & 
% 3.01/3.24                   ( v2_funct_1 @ C ) ) =>
% 3.01/3.24                 ( ( ( k1_relset_1 @
% 3.01/3.24                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 3.01/3.24                       ( k2_tops_2 @
% 3.01/3.24                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 3.01/3.24                     ( k2_struct_0 @ B ) ) & 
% 3.01/3.24                   ( ( k2_relset_1 @
% 3.01/3.24                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 3.01/3.24                       ( k2_tops_2 @
% 3.01/3.24                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 3.01/3.24                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 3.01/3.24  thf(zf_stmt_0, negated_conjecture,
% 3.01/3.24    (~( ![A:$i]:
% 3.01/3.24        ( ( l1_struct_0 @ A ) =>
% 3.01/3.24          ( ![B:$i]:
% 3.01/3.24            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 3.01/3.24              ( ![C:$i]:
% 3.01/3.24                ( ( ( v1_funct_1 @ C ) & 
% 3.01/3.24                    ( v1_funct_2 @
% 3.01/3.24                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 3.01/3.24                    ( m1_subset_1 @
% 3.01/3.24                      C @ 
% 3.01/3.24                      ( k1_zfmisc_1 @
% 3.01/3.24                        ( k2_zfmisc_1 @
% 3.01/3.24                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 3.01/3.24                  ( ( ( ( k2_relset_1 @
% 3.01/3.24                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 3.01/3.24                        ( k2_struct_0 @ B ) ) & 
% 3.01/3.24                      ( v2_funct_1 @ C ) ) =>
% 3.01/3.24                    ( ( ( k1_relset_1 @
% 3.01/3.24                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 3.01/3.24                          ( k2_tops_2 @
% 3.01/3.24                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 3.01/3.24                        ( k2_struct_0 @ B ) ) & 
% 3.01/3.24                      ( ( k2_relset_1 @
% 3.01/3.24                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 3.01/3.24                          ( k2_tops_2 @
% 3.01/3.24                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 3.01/3.24                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 3.01/3.24    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 3.01/3.24  thf('0', plain,
% 3.01/3.24      ((m1_subset_1 @ sk_C @ 
% 3.01/3.24        (k1_zfmisc_1 @ 
% 3.01/3.24         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf(dt_k3_relset_1, axiom,
% 3.01/3.24    (![A:$i,B:$i,C:$i]:
% 3.01/3.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.01/3.24       ( m1_subset_1 @
% 3.01/3.24         ( k3_relset_1 @ A @ B @ C ) @ 
% 3.01/3.24         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ))).
% 3.01/3.24  thf('1', plain,
% 3.01/3.24      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.01/3.24         ((m1_subset_1 @ (k3_relset_1 @ X9 @ X10 @ X11) @ 
% 3.01/3.24           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X9)))
% 3.01/3.24          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 3.01/3.24      inference('cnf', [status(esa)], [dt_k3_relset_1])).
% 3.01/3.24  thf('2', plain,
% 3.01/3.24      ((m1_subset_1 @ 
% 3.01/3.24        (k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 3.01/3.24        (k1_zfmisc_1 @ 
% 3.01/3.24         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 3.01/3.24      inference('sup-', [status(thm)], ['0', '1'])).
% 3.01/3.24  thf('3', plain,
% 3.01/3.24      ((m1_subset_1 @ sk_C @ 
% 3.01/3.24        (k1_zfmisc_1 @ 
% 3.01/3.24         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf(redefinition_k3_relset_1, axiom,
% 3.01/3.24    (![A:$i,B:$i,C:$i]:
% 3.01/3.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.01/3.24       ( ( k3_relset_1 @ A @ B @ C ) = ( k4_relat_1 @ C ) ) ))).
% 3.01/3.24  thf('4', plain,
% 3.01/3.24      (![X18 : $i, X19 : $i, X20 : $i]:
% 3.01/3.24         (((k3_relset_1 @ X19 @ X20 @ X18) = (k4_relat_1 @ X18))
% 3.01/3.24          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 3.01/3.24      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 3.01/3.24  thf('5', plain,
% 3.01/3.24      (((k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.01/3.24         = (k4_relat_1 @ sk_C))),
% 3.01/3.24      inference('sup-', [status(thm)], ['3', '4'])).
% 3.01/3.24  thf('6', plain,
% 3.01/3.24      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 3.01/3.24        (k1_zfmisc_1 @ 
% 3.01/3.24         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 3.01/3.24      inference('demod', [status(thm)], ['2', '5'])).
% 3.01/3.24  thf(d3_struct_0, axiom,
% 3.01/3.24    (![A:$i]:
% 3.01/3.24     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 3.01/3.24  thf('7', plain,
% 3.01/3.24      (![X26 : $i]:
% 3.01/3.24         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 3.01/3.24      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.01/3.24  thf('8', plain,
% 3.01/3.24      ((m1_subset_1 @ sk_C @ 
% 3.01/3.24        (k1_zfmisc_1 @ 
% 3.01/3.24         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf('9', plain,
% 3.01/3.24      (((m1_subset_1 @ sk_C @ 
% 3.01/3.24         (k1_zfmisc_1 @ 
% 3.01/3.24          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 3.01/3.24        | ~ (l1_struct_0 @ sk_B))),
% 3.01/3.24      inference('sup+', [status(thm)], ['7', '8'])).
% 3.01/3.24  thf('10', plain, ((l1_struct_0 @ sk_B)),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf('11', plain,
% 3.01/3.24      ((m1_subset_1 @ sk_C @ 
% 3.01/3.24        (k1_zfmisc_1 @ 
% 3.01/3.24         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 3.01/3.24      inference('demod', [status(thm)], ['9', '10'])).
% 3.01/3.24  thf('12', plain,
% 3.01/3.24      ((m1_subset_1 @ sk_C @ 
% 3.01/3.24        (k1_zfmisc_1 @ 
% 3.01/3.24         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf(redefinition_k2_relset_1, axiom,
% 3.01/3.24    (![A:$i,B:$i,C:$i]:
% 3.01/3.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.01/3.24       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.01/3.24  thf('13', plain,
% 3.01/3.24      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.01/3.24         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 3.01/3.24          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 3.01/3.24      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.01/3.24  thf('14', plain,
% 3.01/3.24      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.01/3.24         = (k2_relat_1 @ sk_C))),
% 3.01/3.24      inference('sup-', [status(thm)], ['12', '13'])).
% 3.01/3.24  thf('15', plain,
% 3.01/3.24      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.01/3.24         = (k2_struct_0 @ sk_B))),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf('16', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 3.01/3.24      inference('sup+', [status(thm)], ['14', '15'])).
% 3.01/3.24  thf('17', plain,
% 3.01/3.24      ((m1_subset_1 @ sk_C @ 
% 3.01/3.24        (k1_zfmisc_1 @ 
% 3.01/3.24         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 3.01/3.24      inference('demod', [status(thm)], ['11', '16'])).
% 3.01/3.24  thf(cc5_funct_2, axiom,
% 3.01/3.24    (![A:$i,B:$i]:
% 3.01/3.24     ( ( ~( v1_xboole_0 @ B ) ) =>
% 3.01/3.24       ( ![C:$i]:
% 3.01/3.24         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.01/3.24           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 3.01/3.24             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 3.01/3.24  thf('18', plain,
% 3.01/3.24      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.01/3.24         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 3.01/3.24          | (v1_partfun1 @ X21 @ X22)
% 3.01/3.24          | ~ (v1_funct_2 @ X21 @ X22 @ X23)
% 3.01/3.24          | ~ (v1_funct_1 @ X21)
% 3.01/3.24          | (v1_xboole_0 @ X23))),
% 3.01/3.24      inference('cnf', [status(esa)], [cc5_funct_2])).
% 3.01/3.24  thf('19', plain,
% 3.01/3.24      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 3.01/3.24        | ~ (v1_funct_1 @ sk_C)
% 3.01/3.24        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 3.01/3.24        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 3.01/3.24      inference('sup-', [status(thm)], ['17', '18'])).
% 3.01/3.24  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf('21', plain,
% 3.01/3.24      (![X26 : $i]:
% 3.01/3.24         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 3.01/3.24      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.01/3.24  thf('22', plain,
% 3.01/3.24      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf('23', plain,
% 3.01/3.24      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 3.01/3.24        | ~ (l1_struct_0 @ sk_B))),
% 3.01/3.24      inference('sup+', [status(thm)], ['21', '22'])).
% 3.01/3.24  thf('24', plain, ((l1_struct_0 @ sk_B)),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf('25', plain,
% 3.01/3.24      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 3.01/3.24      inference('demod', [status(thm)], ['23', '24'])).
% 3.01/3.24  thf('26', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 3.01/3.24      inference('sup+', [status(thm)], ['14', '15'])).
% 3.01/3.24  thf('27', plain,
% 3.01/3.24      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 3.01/3.24      inference('demod', [status(thm)], ['25', '26'])).
% 3.01/3.24  thf('28', plain,
% 3.01/3.24      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 3.01/3.24        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 3.01/3.24      inference('demod', [status(thm)], ['19', '20', '27'])).
% 3.01/3.24  thf('29', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 3.01/3.24      inference('sup+', [status(thm)], ['14', '15'])).
% 3.01/3.24  thf(fc5_struct_0, axiom,
% 3.01/3.24    (![A:$i]:
% 3.01/3.24     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 3.01/3.24       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 3.01/3.24  thf('30', plain,
% 3.01/3.24      (![X27 : $i]:
% 3.01/3.24         (~ (v1_xboole_0 @ (k2_struct_0 @ X27))
% 3.01/3.24          | ~ (l1_struct_0 @ X27)
% 3.01/3.24          | (v2_struct_0 @ X27))),
% 3.01/3.24      inference('cnf', [status(esa)], [fc5_struct_0])).
% 3.01/3.24  thf('31', plain,
% 3.01/3.24      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 3.01/3.24        | (v2_struct_0 @ sk_B)
% 3.01/3.24        | ~ (l1_struct_0 @ sk_B))),
% 3.01/3.24      inference('sup-', [status(thm)], ['29', '30'])).
% 3.01/3.24  thf('32', plain, ((l1_struct_0 @ sk_B)),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf('33', plain,
% 3.01/3.24      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 3.01/3.24      inference('demod', [status(thm)], ['31', '32'])).
% 3.01/3.24  thf('34', plain, (~ (v2_struct_0 @ sk_B)),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf('35', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 3.01/3.24      inference('clc', [status(thm)], ['33', '34'])).
% 3.01/3.24  thf('36', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 3.01/3.24      inference('clc', [status(thm)], ['28', '35'])).
% 3.01/3.24  thf(d4_partfun1, axiom,
% 3.01/3.24    (![A:$i,B:$i]:
% 3.01/3.24     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 3.01/3.24       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 3.01/3.24  thf('37', plain,
% 3.01/3.24      (![X24 : $i, X25 : $i]:
% 3.01/3.24         (~ (v1_partfun1 @ X25 @ X24)
% 3.01/3.24          | ((k1_relat_1 @ X25) = (X24))
% 3.01/3.24          | ~ (v4_relat_1 @ X25 @ X24)
% 3.01/3.24          | ~ (v1_relat_1 @ X25))),
% 3.01/3.24      inference('cnf', [status(esa)], [d4_partfun1])).
% 3.01/3.24  thf('38', plain,
% 3.01/3.24      ((~ (v1_relat_1 @ sk_C)
% 3.01/3.24        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 3.01/3.24        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 3.01/3.24      inference('sup-', [status(thm)], ['36', '37'])).
% 3.01/3.24  thf('39', plain,
% 3.01/3.24      ((m1_subset_1 @ sk_C @ 
% 3.01/3.24        (k1_zfmisc_1 @ 
% 3.01/3.24         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf(cc2_relat_1, axiom,
% 3.01/3.24    (![A:$i]:
% 3.01/3.24     ( ( v1_relat_1 @ A ) =>
% 3.01/3.24       ( ![B:$i]:
% 3.01/3.24         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 3.01/3.24  thf('40', plain,
% 3.01/3.24      (![X0 : $i, X1 : $i]:
% 3.01/3.24         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 3.01/3.24          | (v1_relat_1 @ X0)
% 3.01/3.24          | ~ (v1_relat_1 @ X1))),
% 3.01/3.24      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.01/3.24  thf('41', plain,
% 3.01/3.24      ((~ (v1_relat_1 @ 
% 3.01/3.24           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 3.01/3.24        | (v1_relat_1 @ sk_C))),
% 3.01/3.24      inference('sup-', [status(thm)], ['39', '40'])).
% 3.01/3.24  thf(fc6_relat_1, axiom,
% 3.01/3.24    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 3.01/3.24  thf('42', plain,
% 3.01/3.24      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 3.01/3.24      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.01/3.24  thf('43', plain, ((v1_relat_1 @ sk_C)),
% 3.01/3.24      inference('demod', [status(thm)], ['41', '42'])).
% 3.01/3.24  thf('44', plain,
% 3.01/3.24      ((m1_subset_1 @ sk_C @ 
% 3.01/3.24        (k1_zfmisc_1 @ 
% 3.01/3.24         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf(cc2_relset_1, axiom,
% 3.01/3.24    (![A:$i,B:$i,C:$i]:
% 3.01/3.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.01/3.24       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.01/3.24  thf('45', plain,
% 3.01/3.24      (![X6 : $i, X7 : $i, X8 : $i]:
% 3.01/3.24         ((v4_relat_1 @ X6 @ X7)
% 3.01/3.24          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 3.01/3.24      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.01/3.24  thf('46', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 3.01/3.24      inference('sup-', [status(thm)], ['44', '45'])).
% 3.01/3.24  thf('47', plain, ((v1_funct_1 @ sk_C)),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf(d9_funct_1, axiom,
% 3.01/3.24    (![A:$i]:
% 3.01/3.24     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.01/3.24       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 3.01/3.24  thf('48', plain,
% 3.01/3.24      (![X4 : $i]:
% 3.01/3.24         (~ (v2_funct_1 @ X4)
% 3.01/3.24          | ((k2_funct_1 @ X4) = (k4_relat_1 @ X4))
% 3.01/3.24          | ~ (v1_funct_1 @ X4)
% 3.01/3.24          | ~ (v1_relat_1 @ X4))),
% 3.01/3.24      inference('cnf', [status(esa)], [d9_funct_1])).
% 3.01/3.24  thf('49', plain,
% 3.01/3.24      ((~ (v1_relat_1 @ sk_C)
% 3.01/3.24        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 3.01/3.24        | ~ (v2_funct_1 @ sk_C))),
% 3.01/3.24      inference('sup-', [status(thm)], ['47', '48'])).
% 3.01/3.24  thf('50', plain, ((v1_relat_1 @ sk_C)),
% 3.01/3.24      inference('demod', [status(thm)], ['41', '42'])).
% 3.01/3.24  thf('51', plain, ((v2_funct_1 @ sk_C)),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf('52', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 3.01/3.24      inference('demod', [status(thm)], ['49', '50', '51'])).
% 3.01/3.24  thf(t55_funct_1, axiom,
% 3.01/3.24    (![A:$i]:
% 3.01/3.24     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.01/3.24       ( ( v2_funct_1 @ A ) =>
% 3.01/3.24         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 3.01/3.24           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 3.01/3.24  thf('53', plain,
% 3.01/3.24      (![X5 : $i]:
% 3.01/3.24         (~ (v2_funct_1 @ X5)
% 3.01/3.24          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 3.01/3.24          | ~ (v1_funct_1 @ X5)
% 3.01/3.24          | ~ (v1_relat_1 @ X5))),
% 3.01/3.24      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.01/3.24  thf('54', plain,
% 3.01/3.24      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 3.01/3.24        | ~ (v1_relat_1 @ sk_C)
% 3.01/3.24        | ~ (v1_funct_1 @ sk_C)
% 3.01/3.24        | ~ (v2_funct_1 @ sk_C))),
% 3.01/3.24      inference('sup+', [status(thm)], ['52', '53'])).
% 3.01/3.24  thf('55', plain, ((v1_relat_1 @ sk_C)),
% 3.01/3.24      inference('demod', [status(thm)], ['41', '42'])).
% 3.01/3.24  thf('56', plain, ((v1_funct_1 @ sk_C)),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf('57', plain, ((v2_funct_1 @ sk_C)),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf('58', plain,
% 3.01/3.24      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 3.01/3.24      inference('demod', [status(thm)], ['54', '55', '56', '57'])).
% 3.01/3.24  thf('59', plain,
% 3.01/3.24      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (u1_struct_0 @ sk_A))),
% 3.01/3.24      inference('demod', [status(thm)], ['38', '43', '46', '58'])).
% 3.01/3.24  thf('60', plain,
% 3.01/3.24      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 3.01/3.24        (k1_zfmisc_1 @ 
% 3.01/3.24         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 3.01/3.24          (k2_relat_1 @ (k4_relat_1 @ sk_C)))))),
% 3.01/3.24      inference('demod', [status(thm)], ['6', '59'])).
% 3.01/3.24  thf('61', plain,
% 3.01/3.24      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.01/3.24         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 3.01/3.24          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 3.01/3.24      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.01/3.24  thf('62', plain,
% 3.01/3.24      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 3.01/3.24         (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ (k4_relat_1 @ sk_C))
% 3.01/3.24         = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 3.01/3.24      inference('sup-', [status(thm)], ['60', '61'])).
% 3.01/3.24  thf('63', plain,
% 3.01/3.24      (![X26 : $i]:
% 3.01/3.24         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 3.01/3.24      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.01/3.24  thf('64', plain,
% 3.01/3.24      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.01/3.24          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.01/3.24          != (k2_struct_0 @ sk_B))
% 3.01/3.24        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.01/3.24            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.01/3.24            != (k2_struct_0 @ sk_A)))),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf('65', plain,
% 3.01/3.24      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.01/3.24          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.01/3.24          != (k2_struct_0 @ sk_A)))
% 3.01/3.24         <= (~
% 3.01/3.24             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.01/3.24                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.01/3.24                = (k2_struct_0 @ sk_A))))),
% 3.01/3.24      inference('split', [status(esa)], ['64'])).
% 3.01/3.24  thf('66', plain,
% 3.01/3.24      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.01/3.24           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 3.01/3.24           != (k2_struct_0 @ sk_A))
% 3.01/3.24         | ~ (l1_struct_0 @ sk_B)))
% 3.01/3.24         <= (~
% 3.01/3.24             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.01/3.24                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.01/3.24                = (k2_struct_0 @ sk_A))))),
% 3.01/3.24      inference('sup-', [status(thm)], ['63', '65'])).
% 3.01/3.24  thf('67', plain, ((l1_struct_0 @ sk_B)),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf('68', plain,
% 3.01/3.24      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.01/3.24          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 3.01/3.24          != (k2_struct_0 @ sk_A)))
% 3.01/3.24         <= (~
% 3.01/3.24             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.01/3.24                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.01/3.24                = (k2_struct_0 @ sk_A))))),
% 3.01/3.24      inference('demod', [status(thm)], ['66', '67'])).
% 3.01/3.24  thf('69', plain,
% 3.01/3.24      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (u1_struct_0 @ sk_A))),
% 3.01/3.24      inference('demod', [status(thm)], ['38', '43', '46', '58'])).
% 3.01/3.24  thf('70', plain,
% 3.01/3.24      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (u1_struct_0 @ sk_A))),
% 3.01/3.24      inference('demod', [status(thm)], ['38', '43', '46', '58'])).
% 3.01/3.24  thf('71', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 3.01/3.24      inference('sup+', [status(thm)], ['14', '15'])).
% 3.01/3.24  thf('72', plain,
% 3.01/3.24      (![X26 : $i]:
% 3.01/3.24         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 3.01/3.24      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.01/3.24  thf('73', plain,
% 3.01/3.24      (![X26 : $i]:
% 3.01/3.24         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 3.01/3.24      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.01/3.24  thf('74', plain,
% 3.01/3.24      ((m1_subset_1 @ sk_C @ 
% 3.01/3.24        (k1_zfmisc_1 @ 
% 3.01/3.24         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf('75', plain,
% 3.01/3.24      (((m1_subset_1 @ sk_C @ 
% 3.01/3.24         (k1_zfmisc_1 @ 
% 3.01/3.24          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 3.01/3.24        | ~ (l1_struct_0 @ sk_A))),
% 3.01/3.24      inference('sup+', [status(thm)], ['73', '74'])).
% 3.01/3.24  thf('76', plain, ((l1_struct_0 @ sk_A)),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf('77', plain,
% 3.01/3.24      ((m1_subset_1 @ sk_C @ 
% 3.01/3.24        (k1_zfmisc_1 @ 
% 3.01/3.24         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.01/3.24      inference('demod', [status(thm)], ['75', '76'])).
% 3.01/3.24  thf('78', plain,
% 3.01/3.24      (((m1_subset_1 @ sk_C @ 
% 3.01/3.24         (k1_zfmisc_1 @ 
% 3.01/3.24          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 3.01/3.24        | ~ (l1_struct_0 @ sk_B))),
% 3.01/3.24      inference('sup+', [status(thm)], ['72', '77'])).
% 3.01/3.24  thf('79', plain, ((l1_struct_0 @ sk_B)),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf('80', plain,
% 3.01/3.24      ((m1_subset_1 @ sk_C @ 
% 3.01/3.24        (k1_zfmisc_1 @ 
% 3.01/3.24         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 3.01/3.24      inference('demod', [status(thm)], ['78', '79'])).
% 3.01/3.24  thf('81', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 3.01/3.24      inference('sup+', [status(thm)], ['14', '15'])).
% 3.01/3.24  thf('82', plain,
% 3.01/3.24      ((m1_subset_1 @ sk_C @ 
% 3.01/3.24        (k1_zfmisc_1 @ 
% 3.01/3.24         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 3.01/3.24      inference('demod', [status(thm)], ['80', '81'])).
% 3.01/3.24  thf('83', plain,
% 3.01/3.24      (![X26 : $i]:
% 3.01/3.24         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 3.01/3.24      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.01/3.24  thf('84', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 3.01/3.24      inference('clc', [status(thm)], ['28', '35'])).
% 3.01/3.24  thf('85', plain,
% 3.01/3.24      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 3.01/3.24      inference('sup+', [status(thm)], ['83', '84'])).
% 3.01/3.24  thf('86', plain, ((l1_struct_0 @ sk_A)),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf('87', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 3.01/3.24      inference('demod', [status(thm)], ['85', '86'])).
% 3.01/3.24  thf('88', plain,
% 3.01/3.24      (![X24 : $i, X25 : $i]:
% 3.01/3.24         (~ (v1_partfun1 @ X25 @ X24)
% 3.01/3.24          | ((k1_relat_1 @ X25) = (X24))
% 3.01/3.24          | ~ (v4_relat_1 @ X25 @ X24)
% 3.01/3.24          | ~ (v1_relat_1 @ X25))),
% 3.01/3.24      inference('cnf', [status(esa)], [d4_partfun1])).
% 3.01/3.24  thf('89', plain,
% 3.01/3.24      ((~ (v1_relat_1 @ sk_C)
% 3.01/3.24        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 3.01/3.24        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 3.01/3.24      inference('sup-', [status(thm)], ['87', '88'])).
% 3.01/3.24  thf('90', plain, ((v1_relat_1 @ sk_C)),
% 3.01/3.24      inference('demod', [status(thm)], ['41', '42'])).
% 3.01/3.24  thf('91', plain,
% 3.01/3.24      ((m1_subset_1 @ sk_C @ 
% 3.01/3.24        (k1_zfmisc_1 @ 
% 3.01/3.24         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 3.01/3.24      inference('demod', [status(thm)], ['75', '76'])).
% 3.01/3.24  thf('92', plain,
% 3.01/3.24      (![X6 : $i, X7 : $i, X8 : $i]:
% 3.01/3.24         ((v4_relat_1 @ X6 @ X7)
% 3.01/3.24          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 3.01/3.24      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.01/3.24  thf('93', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 3.01/3.24      inference('sup-', [status(thm)], ['91', '92'])).
% 3.01/3.24  thf('94', plain,
% 3.01/3.24      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 3.01/3.24      inference('demod', [status(thm)], ['54', '55', '56', '57'])).
% 3.01/3.24  thf('95', plain,
% 3.01/3.24      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 3.01/3.24      inference('demod', [status(thm)], ['89', '90', '93', '94'])).
% 3.01/3.24  thf('96', plain,
% 3.01/3.24      ((m1_subset_1 @ sk_C @ 
% 3.01/3.24        (k1_zfmisc_1 @ 
% 3.01/3.24         (k2_zfmisc_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 3.01/3.24          (k2_relat_1 @ sk_C))))),
% 3.01/3.24      inference('demod', [status(thm)], ['82', '95'])).
% 3.01/3.24  thf(d4_tops_2, axiom,
% 3.01/3.24    (![A:$i,B:$i,C:$i]:
% 3.01/3.24     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.01/3.24         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.01/3.24       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 3.01/3.24         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 3.01/3.24  thf('97', plain,
% 3.01/3.24      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.01/3.24         (((k2_relset_1 @ X29 @ X28 @ X30) != (X28))
% 3.01/3.24          | ~ (v2_funct_1 @ X30)
% 3.01/3.24          | ((k2_tops_2 @ X29 @ X28 @ X30) = (k2_funct_1 @ X30))
% 3.01/3.24          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 3.01/3.24          | ~ (v1_funct_2 @ X30 @ X29 @ X28)
% 3.01/3.24          | ~ (v1_funct_1 @ X30))),
% 3.01/3.24      inference('cnf', [status(esa)], [d4_tops_2])).
% 3.01/3.24  thf('98', plain,
% 3.01/3.24      ((~ (v1_funct_1 @ sk_C)
% 3.01/3.24        | ~ (v1_funct_2 @ sk_C @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 3.01/3.24             (k2_relat_1 @ sk_C))
% 3.01/3.24        | ((k2_tops_2 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 3.01/3.24            (k2_relat_1 @ sk_C) @ sk_C) = (k2_funct_1 @ sk_C))
% 3.01/3.24        | ~ (v2_funct_1 @ sk_C)
% 3.01/3.24        | ((k2_relset_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 3.01/3.24            (k2_relat_1 @ sk_C) @ sk_C) != (k2_relat_1 @ sk_C)))),
% 3.01/3.24      inference('sup-', [status(thm)], ['96', '97'])).
% 3.01/3.24  thf('99', plain, ((v1_funct_1 @ sk_C)),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf('100', plain,
% 3.01/3.24      (![X26 : $i]:
% 3.01/3.24         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 3.01/3.24      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.01/3.24  thf('101', plain,
% 3.01/3.24      (![X26 : $i]:
% 3.01/3.24         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 3.01/3.24      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.01/3.24  thf('102', plain,
% 3.01/3.24      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf('103', plain,
% 3.01/3.24      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 3.01/3.24        | ~ (l1_struct_0 @ sk_A))),
% 3.01/3.24      inference('sup+', [status(thm)], ['101', '102'])).
% 3.01/3.24  thf('104', plain, ((l1_struct_0 @ sk_A)),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf('105', plain,
% 3.01/3.24      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 3.01/3.24      inference('demod', [status(thm)], ['103', '104'])).
% 3.01/3.24  thf('106', plain,
% 3.01/3.24      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 3.01/3.24        | ~ (l1_struct_0 @ sk_B))),
% 3.01/3.24      inference('sup+', [status(thm)], ['100', '105'])).
% 3.01/3.24  thf('107', plain, ((l1_struct_0 @ sk_B)),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf('108', plain,
% 3.01/3.24      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 3.01/3.24      inference('demod', [status(thm)], ['106', '107'])).
% 3.01/3.24  thf('109', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 3.01/3.24      inference('sup+', [status(thm)], ['14', '15'])).
% 3.01/3.24  thf('110', plain,
% 3.01/3.24      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 3.01/3.24      inference('demod', [status(thm)], ['108', '109'])).
% 3.01/3.24  thf('111', plain,
% 3.01/3.24      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 3.01/3.24      inference('demod', [status(thm)], ['89', '90', '93', '94'])).
% 3.01/3.24  thf('112', plain,
% 3.01/3.24      ((v1_funct_2 @ sk_C @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 3.01/3.24        (k2_relat_1 @ sk_C))),
% 3.01/3.24      inference('demod', [status(thm)], ['110', '111'])).
% 3.01/3.24  thf('113', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 3.01/3.24      inference('demod', [status(thm)], ['49', '50', '51'])).
% 3.01/3.24  thf('114', plain, ((v2_funct_1 @ sk_C)),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf('115', plain,
% 3.01/3.24      (![X26 : $i]:
% 3.01/3.24         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 3.01/3.24      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.01/3.24  thf('116', plain,
% 3.01/3.24      (![X26 : $i]:
% 3.01/3.24         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 3.01/3.24      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.01/3.24  thf('117', plain,
% 3.01/3.24      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.01/3.24         = (k2_struct_0 @ sk_B))),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf('118', plain,
% 3.01/3.24      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.01/3.24          = (k2_struct_0 @ sk_B))
% 3.01/3.24        | ~ (l1_struct_0 @ sk_A))),
% 3.01/3.24      inference('sup+', [status(thm)], ['116', '117'])).
% 3.01/3.24  thf('119', plain, ((l1_struct_0 @ sk_A)),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf('120', plain,
% 3.01/3.24      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 3.01/3.24         = (k2_struct_0 @ sk_B))),
% 3.01/3.24      inference('demod', [status(thm)], ['118', '119'])).
% 3.01/3.24  thf('121', plain,
% 3.01/3.24      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.01/3.24          = (k2_struct_0 @ sk_B))
% 3.01/3.24        | ~ (l1_struct_0 @ sk_B))),
% 3.01/3.24      inference('sup+', [status(thm)], ['115', '120'])).
% 3.01/3.24  thf('122', plain, ((l1_struct_0 @ sk_B)),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf('123', plain,
% 3.01/3.24      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 3.01/3.24         = (k2_struct_0 @ sk_B))),
% 3.01/3.24      inference('demod', [status(thm)], ['121', '122'])).
% 3.01/3.24  thf('124', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 3.01/3.24      inference('sup+', [status(thm)], ['14', '15'])).
% 3.01/3.24  thf('125', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 3.01/3.24      inference('sup+', [status(thm)], ['14', '15'])).
% 3.01/3.24  thf('126', plain,
% 3.01/3.24      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 3.01/3.24         = (k2_relat_1 @ sk_C))),
% 3.01/3.24      inference('demod', [status(thm)], ['123', '124', '125'])).
% 3.01/3.24  thf('127', plain,
% 3.01/3.24      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 3.01/3.24      inference('demod', [status(thm)], ['89', '90', '93', '94'])).
% 3.01/3.24  thf('128', plain,
% 3.01/3.24      (((k2_relset_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 3.01/3.24         (k2_relat_1 @ sk_C) @ sk_C) = (k2_relat_1 @ sk_C))),
% 3.01/3.24      inference('demod', [status(thm)], ['126', '127'])).
% 3.01/3.24  thf('129', plain,
% 3.01/3.24      ((((k2_tops_2 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 3.01/3.24          (k2_relat_1 @ sk_C) @ sk_C) = (k4_relat_1 @ sk_C))
% 3.01/3.24        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 3.01/3.24      inference('demod', [status(thm)],
% 3.01/3.24                ['98', '99', '112', '113', '114', '128'])).
% 3.01/3.24  thf('130', plain,
% 3.01/3.24      (((k2_tops_2 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 3.01/3.24         (k2_relat_1 @ sk_C) @ sk_C) = (k4_relat_1 @ sk_C))),
% 3.01/3.24      inference('simplify', [status(thm)], ['129'])).
% 3.01/3.24  thf('131', plain,
% 3.01/3.24      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 3.01/3.24      inference('demod', [status(thm)], ['89', '90', '93', '94'])).
% 3.01/3.24  thf('132', plain,
% 3.01/3.24      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 3.01/3.24          (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ (k4_relat_1 @ sk_C))
% 3.01/3.24          != (k2_relat_1 @ (k4_relat_1 @ sk_C))))
% 3.01/3.24         <= (~
% 3.01/3.24             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.01/3.24                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.01/3.24                = (k2_struct_0 @ sk_A))))),
% 3.01/3.24      inference('demod', [status(thm)], ['68', '69', '70', '71', '130', '131'])).
% 3.01/3.24  thf('133', plain,
% 3.01/3.24      (((k2_tops_2 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 3.01/3.24         (k2_relat_1 @ sk_C) @ sk_C) = (k4_relat_1 @ sk_C))),
% 3.01/3.24      inference('simplify', [status(thm)], ['129'])).
% 3.01/3.24  thf('134', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 3.01/3.24      inference('sup+', [status(thm)], ['14', '15'])).
% 3.01/3.24  thf('135', plain,
% 3.01/3.24      (![X26 : $i]:
% 3.01/3.24         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 3.01/3.24      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.01/3.24  thf('136', plain,
% 3.01/3.24      (![X26 : $i]:
% 3.01/3.24         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 3.01/3.24      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.01/3.24  thf('137', plain,
% 3.01/3.24      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.01/3.24          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.01/3.24          != (k2_struct_0 @ sk_B)))
% 3.01/3.24         <= (~
% 3.01/3.24             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.01/3.24                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.01/3.24                = (k2_struct_0 @ sk_B))))),
% 3.01/3.24      inference('split', [status(esa)], ['64'])).
% 3.01/3.24  thf('138', plain,
% 3.01/3.24      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.01/3.24           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.01/3.24           != (k2_struct_0 @ sk_B))
% 3.01/3.24         | ~ (l1_struct_0 @ sk_A)))
% 3.01/3.24         <= (~
% 3.01/3.24             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.01/3.24                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.01/3.24                = (k2_struct_0 @ sk_B))))),
% 3.01/3.24      inference('sup-', [status(thm)], ['136', '137'])).
% 3.01/3.24  thf('139', plain, ((l1_struct_0 @ sk_A)),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf('140', plain,
% 3.01/3.24      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.01/3.24          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.01/3.24          != (k2_struct_0 @ sk_B)))
% 3.01/3.24         <= (~
% 3.01/3.24             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.01/3.24                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.01/3.24                = (k2_struct_0 @ sk_B))))),
% 3.01/3.24      inference('demod', [status(thm)], ['138', '139'])).
% 3.01/3.24  thf('141', plain,
% 3.01/3.24      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.01/3.24           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 3.01/3.24           != (k2_struct_0 @ sk_B))
% 3.01/3.24         | ~ (l1_struct_0 @ sk_B)))
% 3.01/3.24         <= (~
% 3.01/3.24             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.01/3.24                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.01/3.24                = (k2_struct_0 @ sk_B))))),
% 3.01/3.24      inference('sup-', [status(thm)], ['135', '140'])).
% 3.01/3.24  thf('142', plain, ((l1_struct_0 @ sk_B)),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf('143', plain,
% 3.01/3.24      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.01/3.24          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 3.01/3.24          != (k2_struct_0 @ sk_B)))
% 3.01/3.24         <= (~
% 3.01/3.24             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.01/3.24                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.01/3.24                = (k2_struct_0 @ sk_B))))),
% 3.01/3.24      inference('demod', [status(thm)], ['141', '142'])).
% 3.01/3.24  thf('144', plain,
% 3.01/3.24      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.01/3.24          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 3.01/3.24          != (k2_struct_0 @ sk_B)))
% 3.01/3.24         <= (~
% 3.01/3.24             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.01/3.24                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.01/3.24                = (k2_struct_0 @ sk_B))))),
% 3.01/3.24      inference('sup-', [status(thm)], ['134', '143'])).
% 3.01/3.24  thf('145', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 3.01/3.24      inference('sup+', [status(thm)], ['14', '15'])).
% 3.01/3.24  thf('146', plain,
% 3.01/3.24      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 3.01/3.24          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 3.01/3.24          != (k2_relat_1 @ sk_C)))
% 3.01/3.24         <= (~
% 3.01/3.24             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.01/3.24                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.01/3.24                = (k2_struct_0 @ sk_B))))),
% 3.01/3.24      inference('demod', [status(thm)], ['144', '145'])).
% 3.01/3.24  thf('147', plain,
% 3.01/3.24      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 3.01/3.24      inference('demod', [status(thm)], ['89', '90', '93', '94'])).
% 3.01/3.24  thf('148', plain,
% 3.01/3.24      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (u1_struct_0 @ sk_A))),
% 3.01/3.24      inference('demod', [status(thm)], ['38', '43', '46', '58'])).
% 3.01/3.24  thf('149', plain,
% 3.01/3.24      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 3.01/3.24          (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 3.01/3.24          (k2_tops_2 @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ 
% 3.01/3.24           (k2_relat_1 @ sk_C) @ sk_C))
% 3.01/3.24          != (k2_relat_1 @ sk_C)))
% 3.01/3.24         <= (~
% 3.01/3.24             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.01/3.24                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.01/3.24                = (k2_struct_0 @ sk_B))))),
% 3.01/3.24      inference('demod', [status(thm)], ['146', '147', '148'])).
% 3.01/3.24  thf('150', plain,
% 3.01/3.24      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 3.01/3.24          (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ (k4_relat_1 @ sk_C))
% 3.01/3.24          != (k2_relat_1 @ sk_C)))
% 3.01/3.24         <= (~
% 3.01/3.24             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.01/3.24                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.01/3.24                = (k2_struct_0 @ sk_B))))),
% 3.01/3.24      inference('sup-', [status(thm)], ['133', '149'])).
% 3.01/3.24  thf('151', plain,
% 3.01/3.24      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 3.01/3.24        (k1_zfmisc_1 @ 
% 3.01/3.24         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 3.01/3.24          (k2_relat_1 @ (k4_relat_1 @ sk_C)))))),
% 3.01/3.24      inference('demod', [status(thm)], ['6', '59'])).
% 3.01/3.24  thf(redefinition_k1_relset_1, axiom,
% 3.01/3.24    (![A:$i,B:$i,C:$i]:
% 3.01/3.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.01/3.24       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.01/3.24  thf('152', plain,
% 3.01/3.24      (![X12 : $i, X13 : $i, X14 : $i]:
% 3.01/3.24         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 3.01/3.24          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 3.01/3.24      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.01/3.24  thf('153', plain,
% 3.01/3.24      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 3.01/3.24         (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ (k4_relat_1 @ sk_C))
% 3.01/3.24         = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 3.01/3.24      inference('sup-', [status(thm)], ['151', '152'])).
% 3.01/3.24  thf('154', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 3.01/3.24      inference('demod', [status(thm)], ['49', '50', '51'])).
% 3.01/3.24  thf('155', plain,
% 3.01/3.24      (![X5 : $i]:
% 3.01/3.24         (~ (v2_funct_1 @ X5)
% 3.01/3.24          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 3.01/3.24          | ~ (v1_funct_1 @ X5)
% 3.01/3.24          | ~ (v1_relat_1 @ X5))),
% 3.01/3.24      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.01/3.24  thf('156', plain,
% 3.01/3.24      ((((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))
% 3.01/3.24        | ~ (v1_relat_1 @ sk_C)
% 3.01/3.24        | ~ (v1_funct_1 @ sk_C)
% 3.01/3.24        | ~ (v2_funct_1 @ sk_C))),
% 3.01/3.24      inference('sup+', [status(thm)], ['154', '155'])).
% 3.01/3.24  thf('157', plain, ((v1_relat_1 @ sk_C)),
% 3.01/3.24      inference('demod', [status(thm)], ['41', '42'])).
% 3.01/3.24  thf('158', plain, ((v1_funct_1 @ sk_C)),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf('159', plain, ((v2_funct_1 @ sk_C)),
% 3.01/3.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.01/3.24  thf('160', plain,
% 3.01/3.24      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 3.01/3.24      inference('demod', [status(thm)], ['156', '157', '158', '159'])).
% 3.01/3.24  thf('161', plain,
% 3.01/3.24      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 3.01/3.24         (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ (k4_relat_1 @ sk_C))
% 3.01/3.24         = (k2_relat_1 @ sk_C))),
% 3.01/3.24      inference('demod', [status(thm)], ['153', '160'])).
% 3.01/3.24  thf('162', plain,
% 3.01/3.24      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 3.01/3.24         <= (~
% 3.01/3.24             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.01/3.24                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.01/3.24                = (k2_struct_0 @ sk_B))))),
% 3.01/3.24      inference('demod', [status(thm)], ['150', '161'])).
% 3.01/3.24  thf('163', plain,
% 3.01/3.24      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.01/3.24          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.01/3.24          = (k2_struct_0 @ sk_B)))),
% 3.01/3.24      inference('simplify', [status(thm)], ['162'])).
% 3.01/3.24  thf('164', plain,
% 3.01/3.24      (~
% 3.01/3.24       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.01/3.24          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.01/3.24          = (k2_struct_0 @ sk_A))) | 
% 3.01/3.24       ~
% 3.01/3.24       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.01/3.24          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.01/3.24          = (k2_struct_0 @ sk_B)))),
% 3.01/3.24      inference('split', [status(esa)], ['64'])).
% 3.01/3.24  thf('165', plain,
% 3.01/3.24      (~
% 3.01/3.24       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 3.01/3.24          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 3.01/3.24          = (k2_struct_0 @ sk_A)))),
% 3.01/3.24      inference('sat_resolution*', [status(thm)], ['163', '164'])).
% 3.01/3.24  thf('166', plain,
% 3.01/3.24      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ 
% 3.01/3.24         (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ (k4_relat_1 @ sk_C))
% 3.01/3.24         != (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 3.01/3.24      inference('simpl_trail', [status(thm)], ['132', '165'])).
% 3.01/3.24  thf('167', plain, ($false),
% 3.01/3.24      inference('simplify_reflect-', [status(thm)], ['62', '166'])).
% 3.01/3.24  
% 3.01/3.24  % SZS output end Refutation
% 3.01/3.24  
% 3.01/3.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
