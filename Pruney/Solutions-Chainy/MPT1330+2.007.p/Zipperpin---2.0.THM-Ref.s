%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZAauyzJU9f

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:42 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 254 expanded)
%              Number of leaves         :   38 (  88 expanded)
%              Depth                    :   16
%              Number of atoms          : 1025 (4013 expanded)
%              Number of equality atoms :   96 ( 334 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t52_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( ( k2_struct_0 @ B )
                    = k1_xboole_0 )
                 => ( ( k2_struct_0 @ A )
                    = k1_xboole_0 ) )
               => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k2_struct_0 @ B ) )
                  = ( k2_struct_0 @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( l1_struct_0 @ B )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( ( ( ( k2_struct_0 @ B )
                      = k1_xboole_0 )
                   => ( ( k2_struct_0 @ A )
                      = k1_xboole_0 ) )
                 => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k2_struct_0 @ B ) )
                    = ( k2_struct_0 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_tops_2])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( v1_partfun1 @ X21 @ X22 )
      | ~ ( v1_funct_2 @ X21 @ X22 @ X23 )
      | ~ ( v1_funct_1 @ X21 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('7',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_partfun1 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('10',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_partfun1 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8','13'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('15',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_partfun1 @ X25 @ X24 )
      | ( ( k1_relat_1 @ X25 )
        = X24 )
      | ~ ( v4_relat_1 @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v4_relat_1 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('18',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('19',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v4_relat_1 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('22',plain,(
    v4_relat_1 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','19','22'])).

thf('24',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('25',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 @ ( k2_struct_0 @ sk_B_1 ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C_1 @ ( k2_struct_0 @ sk_B_1 ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C_1 @ ( k2_struct_0 @ sk_B_1 ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('30',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('34',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k8_relset_1 @ X18 @ X19 @ X20 @ X19 )
        = ( k1_relset_1 @ X18 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('35',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C_1 @ ( k2_struct_0 @ sk_B_1 ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('37',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('38',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C_1 @ ( k2_struct_0 @ sk_B_1 ) )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('40',plain,(
    ( k1_relat_1 @ sk_C_1 )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','39'])).

thf('41',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['23','40'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('42',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('43',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k2_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['0','43'])).

thf('45',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k2_struct_0 @ sk_B_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ( k2_struct_0 @ sk_B_1 )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['47'])).

thf('49',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('50',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['47'])).

thf('51',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('52',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) ) ) )
      | ~ ( l1_struct_0 @ sk_B_1 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['49','52'])).

thf('54',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k8_relset_1 @ X18 @ X19 @ X20 @ X19 )
        = ( k1_relset_1 @ X18 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('57',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ sk_C_1 @ ( k2_struct_0 @ sk_B_1 ) )
      = ( k1_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('59',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('60',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ sk_C_1 )
      = ( k1_relat_1 @ sk_C_1 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('62',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v4_relat_1 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('63',plain,
    ( ( v4_relat_1 @ sk_C_1 @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('64',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v4_relat_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k1_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('65',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('67',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('68',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X1 @ X2 )
      | ( r2_hidden @ X1 @ X3 )
      | ( X3
       != ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('69',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( r2_hidden @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','69'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('71',plain,(
    ! [X6: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf(t91_orders_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( ( k3_tarski @ A )
           != k1_xboole_0 )
          & ! [B: $i] :
              ~ ( ( B != k1_xboole_0 )
                & ( r2_hidden @ B @ A ) ) )
      & ~ ( ? [B: $i] :
              ( ( r2_hidden @ B @ A )
              & ( B != k1_xboole_0 ) )
          & ( ( k3_tarski @ A )
            = k1_xboole_0 ) ) ) )).

thf('72',plain,(
    ! [X27: $i,X28: $i] :
      ( ( X27 = k1_xboole_0 )
      | ~ ( r2_hidden @ X27 @ X28 )
      | ( ( k3_tarski @ X28 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t91_orders_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','74'])).

thf('76',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ sk_C_1 )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','75'])).

thf('77',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ sk_C_1 @ ( k2_struct_0 @ sk_B_1 ) )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','76'])).

thf('78',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('79',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['47'])).

thf('80',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('81',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 @ ( k2_struct_0 @ sk_B_1 ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 @ ( k2_struct_0 @ sk_B_1 ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 @ ( k2_struct_0 @ sk_B_1 ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 @ ( k2_struct_0 @ sk_B_1 ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','84'])).

thf('86',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['47'])).

thf('87',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 @ ( k2_struct_0 @ sk_B_1 ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ sk_C_1 @ ( k2_struct_0 @ sk_B_1 ) )
       != k1_xboole_0 )
      | ~ ( l1_struct_0 @ sk_B_1 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','87'])).

thf('89',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ sk_C_1 @ ( k2_struct_0 @ sk_B_1 ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ( k2_struct_0 @ sk_A )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['77','90'])).

thf('92',plain,
    ( ( ( k2_struct_0 @ sk_B_1 )
     != k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['47'])).

thf('93',plain,(
    ( k2_struct_0 @ sk_B_1 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['91','92'])).

thf('94',plain,(
    ( k2_struct_0 @ sk_B_1 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['48','93'])).

thf('95',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['46','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZAauyzJU9f
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:22:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.52/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.52/0.71  % Solved by: fo/fo7.sh
% 0.52/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.71  % done 267 iterations in 0.243s
% 0.52/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.52/0.71  % SZS output start Refutation
% 0.52/0.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.52/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.52/0.71  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.52/0.71  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.52/0.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.52/0.71  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.52/0.71  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.52/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.71  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.52/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.71  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.52/0.71  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.52/0.71  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.52/0.71  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.52/0.71  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.52/0.71  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.52/0.71  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.52/0.71  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.52/0.71  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.52/0.71  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.52/0.71  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.52/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.71  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.52/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.71  thf(d3_struct_0, axiom,
% 0.52/0.71    (![A:$i]:
% 0.52/0.71     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.52/0.71  thf('0', plain,
% 0.52/0.71      (![X26 : $i]:
% 0.52/0.71         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.52/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.71  thf('1', plain,
% 0.52/0.71      (![X26 : $i]:
% 0.52/0.71         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.52/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.71  thf(t52_tops_2, conjecture,
% 0.52/0.71    (![A:$i]:
% 0.52/0.71     ( ( l1_struct_0 @ A ) =>
% 0.52/0.71       ( ![B:$i]:
% 0.52/0.71         ( ( l1_struct_0 @ B ) =>
% 0.52/0.71           ( ![C:$i]:
% 0.52/0.71             ( ( ( v1_funct_1 @ C ) & 
% 0.52/0.71                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.52/0.71                 ( m1_subset_1 @
% 0.52/0.71                   C @ 
% 0.52/0.71                   ( k1_zfmisc_1 @
% 0.52/0.71                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.52/0.71               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.52/0.71                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.52/0.71                 ( ( k8_relset_1 @
% 0.52/0.71                     ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.52/0.71                     ( k2_struct_0 @ B ) ) =
% 0.52/0.71                   ( k2_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.52/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.71    (~( ![A:$i]:
% 0.52/0.71        ( ( l1_struct_0 @ A ) =>
% 0.52/0.71          ( ![B:$i]:
% 0.52/0.71            ( ( l1_struct_0 @ B ) =>
% 0.52/0.71              ( ![C:$i]:
% 0.52/0.71                ( ( ( v1_funct_1 @ C ) & 
% 0.52/0.71                    ( v1_funct_2 @
% 0.52/0.71                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.52/0.71                    ( m1_subset_1 @
% 0.52/0.71                      C @ 
% 0.52/0.71                      ( k1_zfmisc_1 @
% 0.52/0.71                        ( k2_zfmisc_1 @
% 0.52/0.71                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.52/0.71                  ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.52/0.71                      ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.52/0.71                    ( ( k8_relset_1 @
% 0.52/0.71                        ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.52/0.71                        ( k2_struct_0 @ B ) ) =
% 0.52/0.71                      ( k2_struct_0 @ A ) ) ) ) ) ) ) ) )),
% 0.52/0.71    inference('cnf.neg', [status(esa)], [t52_tops_2])).
% 0.52/0.71  thf('2', plain,
% 0.52/0.71      ((m1_subset_1 @ sk_C_1 @ 
% 0.52/0.71        (k1_zfmisc_1 @ 
% 0.52/0.71         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('3', plain,
% 0.52/0.71      (((m1_subset_1 @ sk_C_1 @ 
% 0.52/0.71         (k1_zfmisc_1 @ 
% 0.52/0.71          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))
% 0.52/0.71        | ~ (l1_struct_0 @ sk_A))),
% 0.52/0.71      inference('sup+', [status(thm)], ['1', '2'])).
% 0.52/0.71  thf('4', plain, ((l1_struct_0 @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('5', plain,
% 0.52/0.71      ((m1_subset_1 @ sk_C_1 @ 
% 0.52/0.71        (k1_zfmisc_1 @ 
% 0.52/0.71         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.52/0.71      inference('demod', [status(thm)], ['3', '4'])).
% 0.52/0.71  thf(cc5_funct_2, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.52/0.71       ( ![C:$i]:
% 0.52/0.71         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.71           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.52/0.71             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.52/0.71  thf('6', plain,
% 0.52/0.71      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.52/0.71         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.52/0.71          | (v1_partfun1 @ X21 @ X22)
% 0.52/0.71          | ~ (v1_funct_2 @ X21 @ X22 @ X23)
% 0.52/0.71          | ~ (v1_funct_1 @ X21)
% 0.52/0.71          | (v1_xboole_0 @ X23))),
% 0.52/0.71      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.52/0.71  thf('7', plain,
% 0.52/0.71      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.52/0.71        | ~ (v1_funct_1 @ sk_C_1)
% 0.52/0.71        | ~ (v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ 
% 0.52/0.71             (u1_struct_0 @ sk_B_1))
% 0.52/0.71        | (v1_partfun1 @ sk_C_1 @ (k2_struct_0 @ sk_A)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['5', '6'])).
% 0.52/0.71  thf('8', plain, ((v1_funct_1 @ sk_C_1)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('9', plain,
% 0.52/0.71      (![X26 : $i]:
% 0.52/0.71         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.52/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.71  thf('10', plain,
% 0.52/0.71      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('11', plain,
% 0.52/0.71      (((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))
% 0.52/0.71        | ~ (l1_struct_0 @ sk_A))),
% 0.52/0.71      inference('sup+', [status(thm)], ['9', '10'])).
% 0.52/0.71  thf('12', plain, ((l1_struct_0 @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('13', plain,
% 0.52/0.71      ((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.52/0.71      inference('demod', [status(thm)], ['11', '12'])).
% 0.52/0.71  thf('14', plain,
% 0.52/0.71      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.52/0.71        | (v1_partfun1 @ sk_C_1 @ (k2_struct_0 @ sk_A)))),
% 0.52/0.71      inference('demod', [status(thm)], ['7', '8', '13'])).
% 0.52/0.71  thf(d4_partfun1, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.52/0.71       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.52/0.71  thf('15', plain,
% 0.52/0.71      (![X24 : $i, X25 : $i]:
% 0.52/0.71         (~ (v1_partfun1 @ X25 @ X24)
% 0.52/0.71          | ((k1_relat_1 @ X25) = (X24))
% 0.52/0.71          | ~ (v4_relat_1 @ X25 @ X24)
% 0.52/0.71          | ~ (v1_relat_1 @ X25))),
% 0.52/0.71      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.52/0.71  thf('16', plain,
% 0.52/0.71      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.52/0.71        | ~ (v1_relat_1 @ sk_C_1)
% 0.52/0.71        | ~ (v4_relat_1 @ sk_C_1 @ (k2_struct_0 @ sk_A))
% 0.52/0.71        | ((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['14', '15'])).
% 0.52/0.71  thf('17', plain,
% 0.52/0.71      ((m1_subset_1 @ sk_C_1 @ 
% 0.52/0.71        (k1_zfmisc_1 @ 
% 0.52/0.71         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf(cc1_relset_1, axiom,
% 0.52/0.71    (![A:$i,B:$i,C:$i]:
% 0.52/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.71       ( v1_relat_1 @ C ) ))).
% 0.52/0.71  thf('18', plain,
% 0.52/0.71      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.52/0.71         ((v1_relat_1 @ X9)
% 0.52/0.71          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.52/0.71      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.52/0.71  thf('19', plain, ((v1_relat_1 @ sk_C_1)),
% 0.52/0.71      inference('sup-', [status(thm)], ['17', '18'])).
% 0.52/0.71  thf('20', plain,
% 0.52/0.71      ((m1_subset_1 @ sk_C_1 @ 
% 0.52/0.71        (k1_zfmisc_1 @ 
% 0.52/0.71         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.52/0.71      inference('demod', [status(thm)], ['3', '4'])).
% 0.52/0.71  thf(cc2_relset_1, axiom,
% 0.52/0.71    (![A:$i,B:$i,C:$i]:
% 0.52/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.71       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.52/0.71  thf('21', plain,
% 0.52/0.71      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.52/0.71         ((v4_relat_1 @ X12 @ X13)
% 0.52/0.71          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.52/0.71      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.52/0.71  thf('22', plain, ((v4_relat_1 @ sk_C_1 @ (k2_struct_0 @ sk_A))),
% 0.52/0.71      inference('sup-', [status(thm)], ['20', '21'])).
% 0.52/0.71  thf('23', plain,
% 0.52/0.71      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.52/0.71        | ((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A)))),
% 0.52/0.71      inference('demod', [status(thm)], ['16', '19', '22'])).
% 0.52/0.71  thf('24', plain,
% 0.52/0.71      (![X26 : $i]:
% 0.52/0.71         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.52/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.71  thf('25', plain,
% 0.52/0.71      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.52/0.71         sk_C_1 @ (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('26', plain,
% 0.52/0.71      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1) @ 
% 0.52/0.71          sk_C_1 @ (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A))
% 0.52/0.71        | ~ (l1_struct_0 @ sk_B_1))),
% 0.52/0.71      inference('sup-', [status(thm)], ['24', '25'])).
% 0.52/0.71  thf('27', plain, ((l1_struct_0 @ sk_B_1)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('28', plain,
% 0.52/0.71      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1) @ 
% 0.52/0.71         sk_C_1 @ (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A))),
% 0.52/0.71      inference('demod', [status(thm)], ['26', '27'])).
% 0.52/0.71  thf('29', plain,
% 0.52/0.71      (![X26 : $i]:
% 0.52/0.71         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.52/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.71  thf('30', plain,
% 0.52/0.71      ((m1_subset_1 @ sk_C_1 @ 
% 0.52/0.71        (k1_zfmisc_1 @ 
% 0.52/0.71         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('31', plain,
% 0.52/0.71      (((m1_subset_1 @ sk_C_1 @ 
% 0.52/0.71         (k1_zfmisc_1 @ 
% 0.52/0.71          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))))
% 0.52/0.71        | ~ (l1_struct_0 @ sk_B_1))),
% 0.52/0.71      inference('sup+', [status(thm)], ['29', '30'])).
% 0.52/0.71  thf('32', plain, ((l1_struct_0 @ sk_B_1)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('33', plain,
% 0.52/0.71      ((m1_subset_1 @ sk_C_1 @ 
% 0.52/0.71        (k1_zfmisc_1 @ 
% 0.52/0.71         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))))),
% 0.52/0.71      inference('demod', [status(thm)], ['31', '32'])).
% 0.52/0.71  thf(t38_relset_1, axiom,
% 0.52/0.71    (![A:$i,B:$i,C:$i]:
% 0.52/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.71       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.52/0.71         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.52/0.71  thf('34', plain,
% 0.52/0.71      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.52/0.71         (((k8_relset_1 @ X18 @ X19 @ X20 @ X19)
% 0.52/0.71            = (k1_relset_1 @ X18 @ X19 @ X20))
% 0.52/0.71          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.52/0.71      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.52/0.71  thf('35', plain,
% 0.52/0.71      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1) @ 
% 0.52/0.71         sk_C_1 @ (k2_struct_0 @ sk_B_1))
% 0.52/0.71         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1) @ 
% 0.52/0.71            sk_C_1))),
% 0.52/0.71      inference('sup-', [status(thm)], ['33', '34'])).
% 0.52/0.71  thf('36', plain,
% 0.52/0.71      ((m1_subset_1 @ sk_C_1 @ 
% 0.52/0.71        (k1_zfmisc_1 @ 
% 0.52/0.71         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))))),
% 0.52/0.71      inference('demod', [status(thm)], ['31', '32'])).
% 0.52/0.71  thf(redefinition_k1_relset_1, axiom,
% 0.52/0.71    (![A:$i,B:$i,C:$i]:
% 0.52/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.71       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.52/0.71  thf('37', plain,
% 0.52/0.71      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.52/0.71         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 0.52/0.71          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.52/0.71      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.52/0.71  thf('38', plain,
% 0.52/0.71      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1) @ sk_C_1)
% 0.52/0.71         = (k1_relat_1 @ sk_C_1))),
% 0.52/0.71      inference('sup-', [status(thm)], ['36', '37'])).
% 0.52/0.71  thf('39', plain,
% 0.52/0.71      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1) @ 
% 0.52/0.71         sk_C_1 @ (k2_struct_0 @ sk_B_1)) = (k1_relat_1 @ sk_C_1))),
% 0.52/0.71      inference('demod', [status(thm)], ['35', '38'])).
% 0.52/0.71  thf('40', plain, (((k1_relat_1 @ sk_C_1) != (k2_struct_0 @ sk_A))),
% 0.52/0.71      inference('demod', [status(thm)], ['28', '39'])).
% 0.52/0.71  thf('41', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 0.52/0.71      inference('simplify_reflect-', [status(thm)], ['23', '40'])).
% 0.52/0.71  thf(l13_xboole_0, axiom,
% 0.52/0.71    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.52/0.71  thf('42', plain,
% 0.52/0.71      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.71      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.52/0.71  thf('43', plain, (((u1_struct_0 @ sk_B_1) = (k1_xboole_0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['41', '42'])).
% 0.52/0.71  thf('44', plain,
% 0.52/0.71      ((((k2_struct_0 @ sk_B_1) = (k1_xboole_0)) | ~ (l1_struct_0 @ sk_B_1))),
% 0.52/0.71      inference('sup+', [status(thm)], ['0', '43'])).
% 0.52/0.71  thf('45', plain, ((l1_struct_0 @ sk_B_1)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('46', plain, (((k2_struct_0 @ sk_B_1) = (k1_xboole_0))),
% 0.52/0.71      inference('demod', [status(thm)], ['44', '45'])).
% 0.52/0.71  thf('47', plain,
% 0.52/0.71      ((((k2_struct_0 @ sk_A) = (k1_xboole_0))
% 0.52/0.71        | ((k2_struct_0 @ sk_B_1) != (k1_xboole_0)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('48', plain,
% 0.52/0.71      ((((k2_struct_0 @ sk_B_1) != (k1_xboole_0)))
% 0.52/0.71         <= (~ (((k2_struct_0 @ sk_B_1) = (k1_xboole_0))))),
% 0.52/0.71      inference('split', [status(esa)], ['47'])).
% 0.52/0.71  thf('49', plain,
% 0.52/0.71      (![X26 : $i]:
% 0.52/0.71         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.52/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.71  thf('50', plain,
% 0.52/0.71      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.52/0.71         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.71      inference('split', [status(esa)], ['47'])).
% 0.52/0.71  thf('51', plain,
% 0.52/0.71      ((m1_subset_1 @ sk_C_1 @ 
% 0.52/0.71        (k1_zfmisc_1 @ 
% 0.52/0.71         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.52/0.71      inference('demod', [status(thm)], ['3', '4'])).
% 0.52/0.71  thf('52', plain,
% 0.52/0.71      (((m1_subset_1 @ sk_C_1 @ 
% 0.52/0.71         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B_1)))))
% 0.52/0.71         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.71      inference('sup+', [status(thm)], ['50', '51'])).
% 0.52/0.71  thf('53', plain,
% 0.52/0.71      ((((m1_subset_1 @ sk_C_1 @ 
% 0.52/0.71          (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B_1))))
% 0.52/0.71         | ~ (l1_struct_0 @ sk_B_1)))
% 0.52/0.71         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.71      inference('sup+', [status(thm)], ['49', '52'])).
% 0.52/0.71  thf('54', plain, ((l1_struct_0 @ sk_B_1)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('55', plain,
% 0.52/0.71      (((m1_subset_1 @ sk_C_1 @ 
% 0.52/0.71         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B_1)))))
% 0.52/0.71         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.71      inference('demod', [status(thm)], ['53', '54'])).
% 0.52/0.71  thf('56', plain,
% 0.52/0.71      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.52/0.71         (((k8_relset_1 @ X18 @ X19 @ X20 @ X19)
% 0.52/0.71            = (k1_relset_1 @ X18 @ X19 @ X20))
% 0.52/0.71          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.52/0.71      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.52/0.71  thf('57', plain,
% 0.52/0.71      ((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B_1) @ sk_C_1 @ 
% 0.52/0.71          (k2_struct_0 @ sk_B_1))
% 0.52/0.71          = (k1_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B_1) @ sk_C_1)))
% 0.52/0.71         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.71      inference('sup-', [status(thm)], ['55', '56'])).
% 0.52/0.71  thf('58', plain,
% 0.52/0.71      (((m1_subset_1 @ sk_C_1 @ 
% 0.52/0.71         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B_1)))))
% 0.52/0.71         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.71      inference('demod', [status(thm)], ['53', '54'])).
% 0.52/0.71  thf('59', plain,
% 0.52/0.71      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.52/0.71         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 0.52/0.71          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.52/0.71      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.52/0.71  thf('60', plain,
% 0.52/0.71      ((((k1_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B_1) @ sk_C_1)
% 0.52/0.71          = (k1_relat_1 @ sk_C_1)))
% 0.52/0.71         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.71      inference('sup-', [status(thm)], ['58', '59'])).
% 0.52/0.71  thf('61', plain,
% 0.52/0.71      (((m1_subset_1 @ sk_C_1 @ 
% 0.52/0.71         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B_1)))))
% 0.52/0.71         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.71      inference('sup+', [status(thm)], ['50', '51'])).
% 0.52/0.71  thf('62', plain,
% 0.52/0.71      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.52/0.71         ((v4_relat_1 @ X12 @ X13)
% 0.52/0.71          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.52/0.71      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.52/0.71  thf('63', plain,
% 0.52/0.71      (((v4_relat_1 @ sk_C_1 @ k1_xboole_0))
% 0.52/0.71         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.71      inference('sup-', [status(thm)], ['61', '62'])).
% 0.52/0.71  thf(d18_relat_1, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( v1_relat_1 @ B ) =>
% 0.52/0.71       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.52/0.71  thf('64', plain,
% 0.52/0.71      (![X7 : $i, X8 : $i]:
% 0.52/0.71         (~ (v4_relat_1 @ X7 @ X8)
% 0.52/0.71          | (r1_tarski @ (k1_relat_1 @ X7) @ X8)
% 0.52/0.71          | ~ (v1_relat_1 @ X7))),
% 0.52/0.71      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.52/0.71  thf('65', plain,
% 0.52/0.71      (((~ (v1_relat_1 @ sk_C_1)
% 0.52/0.71         | (r1_tarski @ (k1_relat_1 @ sk_C_1) @ k1_xboole_0)))
% 0.52/0.71         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.71      inference('sup-', [status(thm)], ['63', '64'])).
% 0.52/0.71  thf('66', plain, ((v1_relat_1 @ sk_C_1)),
% 0.52/0.71      inference('sup-', [status(thm)], ['17', '18'])).
% 0.52/0.71  thf('67', plain,
% 0.52/0.71      (((r1_tarski @ (k1_relat_1 @ sk_C_1) @ k1_xboole_0))
% 0.52/0.71         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.71      inference('demod', [status(thm)], ['65', '66'])).
% 0.52/0.71  thf(d1_zfmisc_1, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.52/0.71       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.52/0.71  thf('68', plain,
% 0.52/0.71      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.52/0.71         (~ (r1_tarski @ X1 @ X2)
% 0.52/0.71          | (r2_hidden @ X1 @ X3)
% 0.52/0.71          | ((X3) != (k1_zfmisc_1 @ X2)))),
% 0.52/0.71      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.52/0.71  thf('69', plain,
% 0.52/0.71      (![X1 : $i, X2 : $i]:
% 0.52/0.71         ((r2_hidden @ X1 @ (k1_zfmisc_1 @ X2)) | ~ (r1_tarski @ X1 @ X2))),
% 0.52/0.71      inference('simplify', [status(thm)], ['68'])).
% 0.52/0.71  thf('70', plain,
% 0.52/0.71      (((r2_hidden @ (k1_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.52/0.71         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.71      inference('sup-', [status(thm)], ['67', '69'])).
% 0.52/0.71  thf(t99_zfmisc_1, axiom,
% 0.52/0.71    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.52/0.71  thf('71', plain, (![X6 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X6)) = (X6))),
% 0.52/0.71      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.52/0.71  thf(t91_orders_1, axiom,
% 0.52/0.71    (![A:$i]:
% 0.52/0.71     ( ( ~( ( ( k3_tarski @ A ) != ( k1_xboole_0 ) ) & 
% 0.52/0.71            ( ![B:$i]:
% 0.52/0.71              ( ~( ( ( B ) != ( k1_xboole_0 ) ) & ( r2_hidden @ B @ A ) ) ) ) ) ) & 
% 0.52/0.71       ( ~( ( ?[B:$i]: ( ( r2_hidden @ B @ A ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.52/0.71            ( ( k3_tarski @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.52/0.71  thf('72', plain,
% 0.52/0.71      (![X27 : $i, X28 : $i]:
% 0.52/0.71         (((X27) = (k1_xboole_0))
% 0.52/0.71          | ~ (r2_hidden @ X27 @ X28)
% 0.52/0.71          | ((k3_tarski @ X28) != (k1_xboole_0)))),
% 0.52/0.71      inference('cnf', [status(esa)], [t91_orders_1])).
% 0.52/0.71  thf('73', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         (((X0) != (k1_xboole_0))
% 0.52/0.71          | ~ (r2_hidden @ X1 @ (k1_zfmisc_1 @ X0))
% 0.52/0.71          | ((X1) = (k1_xboole_0)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['71', '72'])).
% 0.52/0.71  thf('74', plain,
% 0.52/0.71      (![X1 : $i]:
% 0.52/0.71         (((X1) = (k1_xboole_0))
% 0.52/0.71          | ~ (r2_hidden @ X1 @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.52/0.71      inference('simplify', [status(thm)], ['73'])).
% 0.52/0.71  thf('75', plain,
% 0.52/0.71      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))
% 0.52/0.71         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.71      inference('sup-', [status(thm)], ['70', '74'])).
% 0.52/0.71  thf('76', plain,
% 0.52/0.71      ((((k1_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B_1) @ sk_C_1)
% 0.52/0.71          = (k1_xboole_0)))
% 0.52/0.71         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.71      inference('demod', [status(thm)], ['60', '75'])).
% 0.52/0.71  thf('77', plain,
% 0.52/0.71      ((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B_1) @ sk_C_1 @ 
% 0.52/0.71          (k2_struct_0 @ sk_B_1)) = (k1_xboole_0)))
% 0.52/0.71         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.71      inference('demod', [status(thm)], ['57', '76'])).
% 0.52/0.71  thf('78', plain,
% 0.52/0.71      (![X26 : $i]:
% 0.52/0.71         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.52/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.71  thf('79', plain,
% 0.52/0.71      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.52/0.71         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.71      inference('split', [status(esa)], ['47'])).
% 0.52/0.71  thf('80', plain,
% 0.52/0.71      (![X26 : $i]:
% 0.52/0.71         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.52/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.71  thf('81', plain,
% 0.52/0.71      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.52/0.71         sk_C_1 @ (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('82', plain,
% 0.52/0.71      ((((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.52/0.71          sk_C_1 @ (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A))
% 0.52/0.71        | ~ (l1_struct_0 @ sk_A))),
% 0.52/0.71      inference('sup-', [status(thm)], ['80', '81'])).
% 0.52/0.71  thf('83', plain, ((l1_struct_0 @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('84', plain,
% 0.52/0.71      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.52/0.71         sk_C_1 @ (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A))),
% 0.52/0.71      inference('demod', [status(thm)], ['82', '83'])).
% 0.52/0.71  thf('85', plain,
% 0.52/0.71      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ sk_C_1 @ 
% 0.52/0.71          (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A)))
% 0.52/0.71         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.71      inference('sup-', [status(thm)], ['79', '84'])).
% 0.52/0.71  thf('86', plain,
% 0.52/0.71      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.52/0.71         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.71      inference('split', [status(esa)], ['47'])).
% 0.52/0.71  thf('87', plain,
% 0.52/0.71      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ sk_C_1 @ 
% 0.52/0.71          (k2_struct_0 @ sk_B_1)) != (k1_xboole_0)))
% 0.52/0.71         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.71      inference('demod', [status(thm)], ['85', '86'])).
% 0.52/0.71  thf('88', plain,
% 0.52/0.71      (((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B_1) @ sk_C_1 @ 
% 0.52/0.71           (k2_struct_0 @ sk_B_1)) != (k1_xboole_0))
% 0.52/0.71         | ~ (l1_struct_0 @ sk_B_1)))
% 0.52/0.71         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.71      inference('sup-', [status(thm)], ['78', '87'])).
% 0.52/0.71  thf('89', plain, ((l1_struct_0 @ sk_B_1)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('90', plain,
% 0.52/0.71      ((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B_1) @ sk_C_1 @ 
% 0.52/0.71          (k2_struct_0 @ sk_B_1)) != (k1_xboole_0)))
% 0.52/0.71         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.71      inference('demod', [status(thm)], ['88', '89'])).
% 0.52/0.71  thf('91', plain, (~ (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.52/0.71      inference('simplify_reflect-', [status(thm)], ['77', '90'])).
% 0.52/0.71  thf('92', plain,
% 0.52/0.71      (~ (((k2_struct_0 @ sk_B_1) = (k1_xboole_0))) | 
% 0.52/0.71       (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.52/0.71      inference('split', [status(esa)], ['47'])).
% 0.52/0.71  thf('93', plain, (~ (((k2_struct_0 @ sk_B_1) = (k1_xboole_0)))),
% 0.52/0.71      inference('sat_resolution*', [status(thm)], ['91', '92'])).
% 0.52/0.71  thf('94', plain, (((k2_struct_0 @ sk_B_1) != (k1_xboole_0))),
% 0.52/0.71      inference('simpl_trail', [status(thm)], ['48', '93'])).
% 0.52/0.71  thf('95', plain, ($false),
% 0.52/0.71      inference('simplify_reflect-', [status(thm)], ['46', '94'])).
% 0.52/0.71  
% 0.52/0.71  % SZS output end Refutation
% 0.52/0.71  
% 0.52/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
