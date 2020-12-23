%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GScA8AsFYr

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 368 expanded)
%              Number of leaves         :   33 ( 120 expanded)
%              Depth                    :   17
%              Number of atoms          : 1327 (6102 expanded)
%              Number of equality atoms :  131 ( 532 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','5'])).

thf('7',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t51_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( k8_relset_1 @ A @ B @ C @ ( k7_relset_1 @ A @ B @ C @ A ) )
          = A ) ) ) )).

thf('9',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( X24 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_2 @ X23 @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X24 ) ) )
      | ( ( k8_relset_1 @ X22 @ X24 @ X23 @ ( k7_relset_1 @ X22 @ X24 @ X23 @ X22 ) )
        = X22 ) ) ),
    inference(cnf,[status(esa)],[t51_funct_2])).

thf('10',plain,
    ( ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k7_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_A ) ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('12',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( ( k7_relset_1 @ X13 @ X14 @ X12 @ X15 )
        = ( k9_relat_1 @ X12 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('16',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k7_relset_1 @ X16 @ X17 @ X18 @ X16 )
        = ( k2_relset_1 @ X16 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('17',plain,
    ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_A ) )
    = ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('19',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('20',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_A ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( ( k7_relset_1 @ X13 @ X14 @ X12 @ X15 )
        = ( k9_relat_1 @ X12 @ X15 ) ) ) ),
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
    inference('sup+',[status(thm)],['14','25'])).

thf('27',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k9_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('30',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t39_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) )
          = ( k2_relset_1 @ B @ A @ C ) )
        & ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) )
          = ( k1_relset_1 @ B @ A @ C ) ) ) ) )).

thf('32',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k8_relset_1 @ X19 @ X20 @ X21 @ ( k7_relset_1 @ X19 @ X20 @ X21 @ X19 ) )
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[t39_relset_1])).

thf('33',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('36',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k1_relset_1 @ X7 @ X8 @ X6 )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('37',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k9_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['33','34','37'])).

thf('39',plain,
    ( ( k9_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('40',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_relat_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['30','40'])).

thf('42',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_relat_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['29','43'])).

thf('45',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('48',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('49',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['47','52'])).

thf('54',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','13','28','46','55','56'])).

thf('58',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['58'])).

thf('60',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['58'])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('62',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('63',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('64',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','64'])).

thf(t162_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B )
        = B ) ) )).

thf('66',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X5 ) @ X4 )
        = X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t162_funct_1])).

thf('67',plain,
    ( ( ( k9_relat_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ sk_C )
      = sk_C )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('68',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(t150_relat_1,axiom,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('69',plain,(
    ! [X3: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t150_relat_1])).

thf('70',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('72',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['70','75'])).

thf('77',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k8_relset_1 @ X16 @ X17 @ X18 @ X17 )
        = ( k1_relset_1 @ X16 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('78',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('80',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('81',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('82',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ k1_xboole_0 )
      = ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('84',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('85',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['79','85'])).

thf('87',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['78','88'])).

thf('90',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('91',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('92',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['58'])).

thf('95',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
       != k1_xboole_0 )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['90','95'])).

thf('97',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ( k2_struct_0 @ sk_A )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['89','98'])).

thf('100',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['58'])).

thf('101',plain,(
    ( k2_struct_0 @ sk_B )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['99','100'])).

thf('102',plain,(
    ( k2_struct_0 @ sk_B )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['59','101'])).

thf('103',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('104',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('109',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k8_relset_1 @ X16 @ X17 @ X18 @ X17 )
        = ( k1_relset_1 @ X16 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('110',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('112',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k1_relset_1 @ X7 @ X8 @ X6 )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('113',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['110','113'])).

thf('115',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['107','114'])).

thf('116',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['57','102','115'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GScA8AsFYr
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:48:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.58  % Solved by: fo/fo7.sh
% 0.21/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.58  % done 181 iterations in 0.062s
% 0.21/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.58  % SZS output start Refutation
% 0.21/0.58  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.58  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.58  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.58  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.58  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.58  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.58  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.58  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.58  thf(d3_struct_0, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.58  thf('0', plain,
% 0.21/0.58      (![X25 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf('1', plain,
% 0.21/0.58      (![X25 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf(t52_tops_2, conjecture,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( l1_struct_0 @ A ) =>
% 0.21/0.58       ( ![B:$i]:
% 0.21/0.58         ( ( l1_struct_0 @ B ) =>
% 0.21/0.58           ( ![C:$i]:
% 0.21/0.58             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.58                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.58                 ( m1_subset_1 @
% 0.21/0.58                   C @ 
% 0.21/0.58                   ( k1_zfmisc_1 @
% 0.21/0.58                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.58               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.58                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.58                 ( ( k8_relset_1 @
% 0.21/0.58                     ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.21/0.58                     ( k2_struct_0 @ B ) ) =
% 0.21/0.58                   ( k2_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.21/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.58    (~( ![A:$i]:
% 0.21/0.58        ( ( l1_struct_0 @ A ) =>
% 0.21/0.58          ( ![B:$i]:
% 0.21/0.58            ( ( l1_struct_0 @ B ) =>
% 0.21/0.58              ( ![C:$i]:
% 0.21/0.58                ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.58                    ( v1_funct_2 @
% 0.21/0.58                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.58                    ( m1_subset_1 @
% 0.21/0.58                      C @ 
% 0.21/0.58                      ( k1_zfmisc_1 @
% 0.21/0.58                        ( k2_zfmisc_1 @
% 0.21/0.58                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.58                  ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.58                      ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.58                    ( ( k8_relset_1 @
% 0.21/0.58                        ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.21/0.58                        ( k2_struct_0 @ B ) ) =
% 0.21/0.58                      ( k2_struct_0 @ A ) ) ) ) ) ) ) ) )),
% 0.21/0.58    inference('cnf.neg', [status(esa)], [t52_tops_2])).
% 0.21/0.58  thf('2', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('3', plain,
% 0.21/0.58      (((m1_subset_1 @ sk_C @ 
% 0.21/0.58         (k1_zfmisc_1 @ 
% 0.21/0.58          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.21/0.58        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.58      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.58  thf('4', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('5', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.58      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.58  thf('6', plain,
% 0.21/0.58      (((m1_subset_1 @ sk_C @ 
% 0.21/0.58         (k1_zfmisc_1 @ 
% 0.21/0.58          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.21/0.58        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.58      inference('sup+', [status(thm)], ['0', '5'])).
% 0.21/0.58  thf('7', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('8', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.21/0.58      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.58  thf(t51_funct_2, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.58       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.58         ( ( k8_relset_1 @ A @ B @ C @ ( k7_relset_1 @ A @ B @ C @ A ) ) =
% 0.21/0.58           ( A ) ) ) ))).
% 0.21/0.58  thf('9', plain,
% 0.21/0.58      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.58         (((X24) = (k1_xboole_0))
% 0.21/0.58          | ~ (v1_funct_1 @ X23)
% 0.21/0.58          | ~ (v1_funct_2 @ X23 @ X22 @ X24)
% 0.21/0.58          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X24)))
% 0.21/0.58          | ((k8_relset_1 @ X22 @ X24 @ X23 @ 
% 0.21/0.58              (k7_relset_1 @ X22 @ X24 @ X23 @ X22)) = (X22)))),
% 0.21/0.58      inference('cnf', [status(esa)], [t51_funct_2])).
% 0.21/0.58  thf('10', plain,
% 0.21/0.58      ((((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.58          (k7_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.58           (k2_struct_0 @ sk_A)))
% 0.21/0.58          = (k2_struct_0 @ sk_A))
% 0.21/0.58        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.21/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.58        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.58  thf('11', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.21/0.58      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.58  thf(redefinition_k7_relset_1, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.58       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.21/0.58  thf('12', plain,
% 0.21/0.58      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.21/0.58          | ((k7_relset_1 @ X13 @ X14 @ X12 @ X15) = (k9_relat_1 @ X12 @ X15)))),
% 0.21/0.58      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.21/0.58  thf('13', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((k7_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.58           X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.58  thf('14', plain,
% 0.21/0.58      (![X25 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf('15', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(t38_relset_1, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.58       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.21/0.58         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.21/0.58  thf('16', plain,
% 0.21/0.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.58         (((k7_relset_1 @ X16 @ X17 @ X18 @ X16)
% 0.21/0.58            = (k2_relset_1 @ X16 @ X17 @ X18))
% 0.21/0.58          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.21/0.58      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.21/0.58  thf('17', plain,
% 0.21/0.58      (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.58         (u1_struct_0 @ sk_A))
% 0.21/0.58         = (k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.21/0.58      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.58  thf('18', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.58       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.58  thf('19', plain,
% 0.21/0.58      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.58         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 0.21/0.58          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.21/0.58      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.58  thf('20', plain,
% 0.21/0.58      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.58         = (k2_relat_1 @ sk_C))),
% 0.21/0.58      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.58  thf('21', plain,
% 0.21/0.58      (((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.58         (u1_struct_0 @ sk_A)) = (k2_relat_1 @ sk_C))),
% 0.21/0.58      inference('demod', [status(thm)], ['17', '20'])).
% 0.21/0.58  thf('22', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('23', plain,
% 0.21/0.58      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.21/0.58          | ((k7_relset_1 @ X13 @ X14 @ X12 @ X15) = (k9_relat_1 @ X12 @ X15)))),
% 0.21/0.58      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.21/0.58  thf('24', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.58           X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.58  thf('25', plain,
% 0.21/0.58      (((k9_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)) = (k2_relat_1 @ sk_C))),
% 0.21/0.58      inference('demod', [status(thm)], ['21', '24'])).
% 0.21/0.58  thf('26', plain,
% 0.21/0.58      ((((k9_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)) = (k2_relat_1 @ sk_C))
% 0.21/0.58        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.58      inference('sup+', [status(thm)], ['14', '25'])).
% 0.21/0.58  thf('27', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('28', plain,
% 0.21/0.58      (((k9_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)) = (k2_relat_1 @ sk_C))),
% 0.21/0.58      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.58  thf('29', plain,
% 0.21/0.58      (![X25 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf('30', plain,
% 0.21/0.58      (![X25 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf('31', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(t39_relset_1, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.21/0.58       ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.21/0.58           ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.21/0.58         ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.21/0.58           ( k1_relset_1 @ B @ A @ C ) ) ) ))).
% 0.21/0.58  thf('32', plain,
% 0.21/0.58      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.58         (((k8_relset_1 @ X19 @ X20 @ X21 @ 
% 0.21/0.58            (k7_relset_1 @ X19 @ X20 @ X21 @ X19))
% 0.21/0.58            = (k1_relset_1 @ X19 @ X20 @ X21))
% 0.21/0.58          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.21/0.58      inference('cnf', [status(esa)], [t39_relset_1])).
% 0.21/0.58  thf('33', plain,
% 0.21/0.58      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.58         (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.58          (u1_struct_0 @ sk_A)))
% 0.21/0.58         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.21/0.58      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.58  thf('34', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.58           X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.58  thf('35', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.58       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.58  thf('36', plain,
% 0.21/0.58      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.58         (((k1_relset_1 @ X7 @ X8 @ X6) = (k1_relat_1 @ X6))
% 0.21/0.58          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.21/0.58      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.58  thf('37', plain,
% 0.21/0.58      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.58         = (k1_relat_1 @ sk_C))),
% 0.21/0.58      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.58  thf('38', plain,
% 0.21/0.58      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.58         (k9_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))) = (k1_relat_1 @ sk_C))),
% 0.21/0.58      inference('demod', [status(thm)], ['33', '34', '37'])).
% 0.21/0.58  thf('39', plain,
% 0.21/0.58      (((k9_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)) = (k2_relat_1 @ sk_C))),
% 0.21/0.58      inference('demod', [status(thm)], ['21', '24'])).
% 0.21/0.58  thf('40', plain,
% 0.21/0.58      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.58         (k2_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.21/0.58      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.58  thf('41', plain,
% 0.21/0.58      ((((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.58          (k2_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))
% 0.21/0.58        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.58      inference('sup+', [status(thm)], ['30', '40'])).
% 0.21/0.58  thf('42', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('43', plain,
% 0.21/0.58      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.58         (k2_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.21/0.58      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.58  thf('44', plain,
% 0.21/0.58      ((((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.58          (k2_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))
% 0.21/0.58        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.58      inference('sup+', [status(thm)], ['29', '43'])).
% 0.21/0.58  thf('45', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('46', plain,
% 0.21/0.58      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.58         (k2_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.21/0.58      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.58  thf('47', plain,
% 0.21/0.58      (![X25 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf('48', plain,
% 0.21/0.58      (![X25 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf('49', plain,
% 0.21/0.58      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('50', plain,
% 0.21/0.58      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.21/0.58        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.58      inference('sup+', [status(thm)], ['48', '49'])).
% 0.21/0.58  thf('51', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('52', plain,
% 0.21/0.58      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.58      inference('demod', [status(thm)], ['50', '51'])).
% 0.21/0.58  thf('53', plain,
% 0.21/0.58      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.21/0.58        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.58      inference('sup+', [status(thm)], ['47', '52'])).
% 0.21/0.58  thf('54', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('55', plain,
% 0.21/0.58      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.21/0.58      inference('demod', [status(thm)], ['53', '54'])).
% 0.21/0.58  thf('56', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('57', plain,
% 0.21/0.58      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 0.21/0.58        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.21/0.58      inference('demod', [status(thm)], ['10', '13', '28', '46', '55', '56'])).
% 0.21/0.58  thf('58', plain,
% 0.21/0.58      ((((k2_struct_0 @ sk_A) = (k1_xboole_0))
% 0.21/0.58        | ((k2_struct_0 @ sk_B) != (k1_xboole_0)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('59', plain,
% 0.21/0.58      ((((k2_struct_0 @ sk_B) != (k1_xboole_0)))
% 0.21/0.58         <= (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))))),
% 0.21/0.58      inference('split', [status(esa)], ['58'])).
% 0.21/0.58  thf('60', plain,
% 0.21/0.58      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.21/0.58         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.58      inference('split', [status(esa)], ['58'])).
% 0.21/0.58  thf('61', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.58      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.58  thf('62', plain,
% 0.21/0.58      (((m1_subset_1 @ sk_C @ 
% 0.21/0.58         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.21/0.58         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.58      inference('sup+', [status(thm)], ['60', '61'])).
% 0.21/0.58  thf(t113_zfmisc_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.58       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.58  thf('63', plain,
% 0.21/0.58      (![X1 : $i, X2 : $i]:
% 0.21/0.58         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X1) != (k1_xboole_0)))),
% 0.21/0.58      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.58  thf('64', plain,
% 0.21/0.58      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.21/0.58      inference('simplify', [status(thm)], ['63'])).
% 0.21/0.58  thf('65', plain,
% 0.21/0.58      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.21/0.58         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.58      inference('demod', [status(thm)], ['62', '64'])).
% 0.21/0.58  thf(t162_funct_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.58       ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ))).
% 0.21/0.58  thf('66', plain,
% 0.21/0.58      (![X4 : $i, X5 : $i]:
% 0.21/0.58         (((k9_relat_1 @ (k6_relat_1 @ X5) @ X4) = (X4))
% 0.21/0.58          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.21/0.58      inference('cnf', [status(esa)], [t162_funct_1])).
% 0.21/0.58  thf('67', plain,
% 0.21/0.58      ((((k9_relat_1 @ (k6_relat_1 @ k1_xboole_0) @ sk_C) = (sk_C)))
% 0.21/0.58         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['65', '66'])).
% 0.21/0.58  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.21/0.58  thf('68', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.58      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.21/0.58  thf(t150_relat_1, axiom,
% 0.21/0.58    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.58  thf('69', plain,
% 0.21/0.58      (![X3 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.21/0.58      inference('cnf', [status(esa)], [t150_relat_1])).
% 0.21/0.58  thf('70', plain,
% 0.21/0.58      ((((k1_xboole_0) = (sk_C))) <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.58      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.21/0.58  thf('71', plain,
% 0.21/0.58      (![X25 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf('72', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('73', plain,
% 0.21/0.58      (((m1_subset_1 @ sk_C @ 
% 0.21/0.58         (k1_zfmisc_1 @ 
% 0.21/0.58          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.21/0.58        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.58      inference('sup+', [status(thm)], ['71', '72'])).
% 0.21/0.58  thf('74', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('75', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.21/0.58      inference('demod', [status(thm)], ['73', '74'])).
% 0.21/0.58  thf('76', plain,
% 0.21/0.58      (((m1_subset_1 @ k1_xboole_0 @ 
% 0.21/0.58         (k1_zfmisc_1 @ 
% 0.21/0.58          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B)))))
% 0.21/0.58         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.58      inference('sup+', [status(thm)], ['70', '75'])).
% 0.21/0.58  thf('77', plain,
% 0.21/0.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.58         (((k8_relset_1 @ X16 @ X17 @ X18 @ X17)
% 0.21/0.58            = (k1_relset_1 @ X16 @ X17 @ X18))
% 0.21/0.58          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.21/0.58      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.21/0.58  thf('78', plain,
% 0.21/0.58      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.21/0.58          k1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.21/0.58          = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.21/0.58             k1_xboole_0)))
% 0.21/0.58         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['76', '77'])).
% 0.21/0.58  thf('79', plain,
% 0.21/0.58      (![X25 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf('80', plain,
% 0.21/0.58      ((((k1_xboole_0) = (sk_C))) <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.58      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.21/0.58  thf('81', plain,
% 0.21/0.58      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.58         = (k1_relat_1 @ sk_C))),
% 0.21/0.58      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.58  thf('82', plain,
% 0.21/0.58      ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.58          k1_xboole_0) = (k1_relat_1 @ sk_C)))
% 0.21/0.58         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.58      inference('sup+', [status(thm)], ['80', '81'])).
% 0.21/0.58  thf('83', plain,
% 0.21/0.58      ((((k1_xboole_0) = (sk_C))) <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.58      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.21/0.58  thf(t60_relat_1, axiom,
% 0.21/0.58    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.58     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.58  thf('84', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.58      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.58  thf('85', plain,
% 0.21/0.58      ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.58          k1_xboole_0) = (k1_xboole_0)))
% 0.21/0.58         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.58      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.21/0.58  thf('86', plain,
% 0.21/0.58      (((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.21/0.58           k1_xboole_0) = (k1_xboole_0))
% 0.21/0.58         | ~ (l1_struct_0 @ sk_B)))
% 0.21/0.58         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.58      inference('sup+', [status(thm)], ['79', '85'])).
% 0.21/0.58  thf('87', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('88', plain,
% 0.21/0.58      ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.21/0.58          k1_xboole_0) = (k1_xboole_0)))
% 0.21/0.58         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.58      inference('demod', [status(thm)], ['86', '87'])).
% 0.21/0.58  thf('89', plain,
% 0.21/0.58      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.21/0.58          k1_xboole_0 @ (k2_struct_0 @ sk_B)) = (k1_xboole_0)))
% 0.21/0.58         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.58      inference('demod', [status(thm)], ['78', '88'])).
% 0.21/0.58  thf('90', plain,
% 0.21/0.58      (![X25 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf('91', plain,
% 0.21/0.58      ((((k1_xboole_0) = (sk_C))) <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.58      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.21/0.58  thf('92', plain,
% 0.21/0.58      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.58         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('93', plain,
% 0.21/0.58      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.58          k1_xboole_0 @ (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A)))
% 0.21/0.58         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['91', '92'])).
% 0.21/0.58  thf('94', plain,
% 0.21/0.58      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.21/0.58         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.58      inference('split', [status(esa)], ['58'])).
% 0.21/0.58  thf('95', plain,
% 0.21/0.58      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.58          k1_xboole_0 @ (k2_struct_0 @ sk_B)) != (k1_xboole_0)))
% 0.21/0.58         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.58      inference('demod', [status(thm)], ['93', '94'])).
% 0.21/0.58  thf('96', plain,
% 0.21/0.58      (((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.21/0.58           k1_xboole_0 @ (k2_struct_0 @ sk_B)) != (k1_xboole_0))
% 0.21/0.58         | ~ (l1_struct_0 @ sk_B)))
% 0.21/0.58         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['90', '95'])).
% 0.21/0.58  thf('97', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('98', plain,
% 0.21/0.58      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.21/0.58          k1_xboole_0 @ (k2_struct_0 @ sk_B)) != (k1_xboole_0)))
% 0.21/0.58         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.21/0.58      inference('demod', [status(thm)], ['96', '97'])).
% 0.21/0.58  thf('99', plain, (~ (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.58      inference('simplify_reflect-', [status(thm)], ['89', '98'])).
% 0.21/0.58  thf('100', plain,
% 0.21/0.58      (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))) | 
% 0.21/0.58       (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.58      inference('split', [status(esa)], ['58'])).
% 0.21/0.58  thf('101', plain, (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.21/0.58      inference('sat_resolution*', [status(thm)], ['99', '100'])).
% 0.21/0.58  thf('102', plain, (((k2_struct_0 @ sk_B) != (k1_xboole_0))),
% 0.21/0.58      inference('simpl_trail', [status(thm)], ['59', '101'])).
% 0.21/0.58  thf('103', plain,
% 0.21/0.58      (![X25 : $i]:
% 0.21/0.58         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.58  thf('104', plain,
% 0.21/0.58      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.58         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('105', plain,
% 0.21/0.58      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.58          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))
% 0.21/0.58        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.58      inference('sup-', [status(thm)], ['103', '104'])).
% 0.21/0.58  thf('106', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('107', plain,
% 0.21/0.58      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.58         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.21/0.58      inference('demod', [status(thm)], ['105', '106'])).
% 0.21/0.58  thf('108', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.21/0.58      inference('demod', [status(thm)], ['73', '74'])).
% 0.21/0.58  thf('109', plain,
% 0.21/0.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.58         (((k8_relset_1 @ X16 @ X17 @ X18 @ X17)
% 0.21/0.58            = (k1_relset_1 @ X16 @ X17 @ X18))
% 0.21/0.58          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.21/0.58      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.21/0.58  thf('110', plain,
% 0.21/0.58      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.58         (k2_struct_0 @ sk_B))
% 0.21/0.58         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 0.21/0.58      inference('sup-', [status(thm)], ['108', '109'])).
% 0.21/0.58  thf('111', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ 
% 0.21/0.58        (k1_zfmisc_1 @ 
% 0.21/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.21/0.58      inference('demod', [status(thm)], ['73', '74'])).
% 0.21/0.58  thf('112', plain,
% 0.21/0.58      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.58         (((k1_relset_1 @ X7 @ X8 @ X6) = (k1_relat_1 @ X6))
% 0.21/0.58          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.21/0.58      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.58  thf('113', plain,
% 0.21/0.58      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.21/0.58         = (k1_relat_1 @ sk_C))),
% 0.21/0.58      inference('sup-', [status(thm)], ['111', '112'])).
% 0.21/0.58  thf('114', plain,
% 0.21/0.58      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.21/0.58         (k2_struct_0 @ sk_B)) = (k1_relat_1 @ sk_C))),
% 0.21/0.58      inference('demod', [status(thm)], ['110', '113'])).
% 0.21/0.58  thf('115', plain, (((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))),
% 0.21/0.58      inference('demod', [status(thm)], ['107', '114'])).
% 0.21/0.58  thf('116', plain, ($false),
% 0.21/0.58      inference('simplify_reflect-', [status(thm)], ['57', '102', '115'])).
% 0.21/0.58  
% 0.21/0.58  % SZS output end Refutation
% 0.21/0.58  
% 0.21/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
