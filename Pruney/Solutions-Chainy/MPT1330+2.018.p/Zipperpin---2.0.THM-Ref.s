%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uvOJL0M0FB

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:44 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 810 expanded)
%              Number of leaves         :   35 ( 240 expanded)
%              Depth                    :   19
%              Number of atoms          : 1243 (13718 expanded)
%              Number of equality atoms :  111 (1140 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
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

thf('9',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('11',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( v1_partfun1 @ X26 @ X27 )
      | ~ ( v1_funct_2 @ X26 @ X27 @ X28 )
      | ~ ( v1_funct_1 @ X26 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('15',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','18'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('20',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_partfun1 @ X30 @ X29 )
      | ( ( k1_relat_1 @ X30 )
        = X29 )
      | ~ ( v4_relat_1 @ X30 @ X29 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('21',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('23',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('25',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('26',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('28',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v4_relat_1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('29',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','26','29'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('31',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('32',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['9','32'])).

thf('34',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('39',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('41',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('43',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('45',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k8_relset_1 @ X23 @ X24 @ X25 @ X24 )
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('46',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
      = ( k1_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('48',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('49',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('51',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v4_relat_1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('52',plain,
    ( ( v4_relat_1 @ sk_C @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('53',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v4_relat_1 @ X9 @ X10 )
      | ( r1_tarski @ ( k1_relat_1 @ X9 ) @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('54',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('56',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('57',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('58',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','58'])).

thf('60',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','59'])).

thf('61',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('62',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('63',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('64',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','67'])).

thf('69',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('70',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
       != k1_xboole_0 )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','70'])).

thf('72',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ( k2_struct_0 @ sk_A )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['60','73'])).

thf('75',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('76',plain,(
    ( k2_struct_0 @ sk_B )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['74','75'])).

thf('77',plain,(
    ( k2_struct_0 @ sk_B )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['37','76'])).

thf('78',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['35','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['8','78'])).

thf('80',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k8_relset_1 @ X23 @ X24 @ X25 @ X24 )
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('81',plain,
    ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('83',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('84',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('86',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['83','86'])).

thf('88',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['82','89'])).

thf('91',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['35','77'])).

thf('94',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['81','94'])).

thf('96',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('97',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['35','77'])).

thf('102',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('104',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( v1_partfun1 @ X26 @ X27 )
      | ~ ( v1_funct_2 @ X26 @ X27 @ X28 )
      | ~ ( v1_funct_1 @ X26 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('106',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_partfun1 @ X30 @ X29 )
      | ( ( k1_relat_1 @ X30 )
        = X29 )
      | ~ ( v4_relat_1 @ X30 @ X29 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('111',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('113',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v4_relat_1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('115',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['111','112','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('118',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['103','118'])).

thf('120',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ( k2_struct_0 @ sk_B )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['37','76'])).

thf('123',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['121','122'])).

thf('124',plain,(
    ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['102','123'])).

thf('125',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['95','124'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uvOJL0M0FB
% 0.11/0.32  % Computer   : n009.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 20:18:11 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running portfolio for 600 s
% 0.11/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.32  % Number of cores: 8
% 0.11/0.32  % Python version: Python 3.6.8
% 0.11/0.33  % Running in FO mode
% 0.52/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.68  % Solved by: fo/fo7.sh
% 0.52/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.68  % done 461 iterations in 0.255s
% 0.52/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.68  % SZS output start Refutation
% 0.52/0.68  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.52/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.52/0.68  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.52/0.68  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.52/0.68  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.52/0.68  thf(sk_C_type, type, sk_C: $i).
% 0.52/0.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.52/0.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.52/0.68  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.52/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.68  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.52/0.68  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.52/0.68  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.52/0.68  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.52/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.68  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.52/0.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.52/0.68  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.52/0.68  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.52/0.68  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.52/0.68  thf(d3_struct_0, axiom,
% 0.52/0.68    (![A:$i]:
% 0.52/0.68     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.52/0.68  thf('0', plain,
% 0.52/0.68      (![X31 : $i]:
% 0.52/0.68         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.52/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.68  thf('1', plain,
% 0.52/0.68      (![X31 : $i]:
% 0.52/0.68         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.52/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.68  thf(t52_tops_2, conjecture,
% 0.52/0.68    (![A:$i]:
% 0.52/0.68     ( ( l1_struct_0 @ A ) =>
% 0.52/0.68       ( ![B:$i]:
% 0.52/0.68         ( ( l1_struct_0 @ B ) =>
% 0.52/0.68           ( ![C:$i]:
% 0.52/0.68             ( ( ( v1_funct_1 @ C ) & 
% 0.52/0.68                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.52/0.68                 ( m1_subset_1 @
% 0.52/0.68                   C @ 
% 0.52/0.68                   ( k1_zfmisc_1 @
% 0.52/0.68                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.52/0.68               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.52/0.68                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.52/0.68                 ( ( k8_relset_1 @
% 0.52/0.68                     ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.52/0.68                     ( k2_struct_0 @ B ) ) =
% 0.52/0.68                   ( k2_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.52/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.68    (~( ![A:$i]:
% 0.52/0.68        ( ( l1_struct_0 @ A ) =>
% 0.52/0.68          ( ![B:$i]:
% 0.52/0.68            ( ( l1_struct_0 @ B ) =>
% 0.52/0.68              ( ![C:$i]:
% 0.52/0.68                ( ( ( v1_funct_1 @ C ) & 
% 0.52/0.68                    ( v1_funct_2 @
% 0.52/0.68                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.52/0.68                    ( m1_subset_1 @
% 0.52/0.68                      C @ 
% 0.52/0.68                      ( k1_zfmisc_1 @
% 0.52/0.68                        ( k2_zfmisc_1 @
% 0.52/0.68                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.52/0.68                  ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.52/0.68                      ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.52/0.68                    ( ( k8_relset_1 @
% 0.52/0.68                        ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.52/0.68                        ( k2_struct_0 @ B ) ) =
% 0.52/0.68                      ( k2_struct_0 @ A ) ) ) ) ) ) ) ) )),
% 0.52/0.68    inference('cnf.neg', [status(esa)], [t52_tops_2])).
% 0.52/0.68  thf('2', plain,
% 0.52/0.68      ((m1_subset_1 @ sk_C @ 
% 0.52/0.68        (k1_zfmisc_1 @ 
% 0.52/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.52/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.68  thf('3', plain,
% 0.52/0.68      (((m1_subset_1 @ sk_C @ 
% 0.52/0.68         (k1_zfmisc_1 @ 
% 0.52/0.68          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.52/0.68        | ~ (l1_struct_0 @ sk_A))),
% 0.52/0.68      inference('sup+', [status(thm)], ['1', '2'])).
% 0.52/0.68  thf('4', plain, ((l1_struct_0 @ sk_A)),
% 0.52/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.68  thf('5', plain,
% 0.52/0.68      ((m1_subset_1 @ sk_C @ 
% 0.52/0.68        (k1_zfmisc_1 @ 
% 0.52/0.68         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.52/0.68      inference('demod', [status(thm)], ['3', '4'])).
% 0.52/0.68  thf('6', plain,
% 0.52/0.68      (((m1_subset_1 @ sk_C @ 
% 0.52/0.68         (k1_zfmisc_1 @ 
% 0.52/0.68          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.52/0.68        | ~ (l1_struct_0 @ sk_B))),
% 0.52/0.68      inference('sup+', [status(thm)], ['0', '5'])).
% 0.52/0.68  thf('7', plain, ((l1_struct_0 @ sk_B)),
% 0.52/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.68  thf('8', plain,
% 0.52/0.68      ((m1_subset_1 @ sk_C @ 
% 0.52/0.68        (k1_zfmisc_1 @ 
% 0.52/0.68         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.52/0.68      inference('demod', [status(thm)], ['6', '7'])).
% 0.52/0.68  thf('9', plain,
% 0.52/0.68      (![X31 : $i]:
% 0.52/0.68         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.52/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.68  thf('10', plain,
% 0.52/0.68      ((m1_subset_1 @ sk_C @ 
% 0.52/0.68        (k1_zfmisc_1 @ 
% 0.52/0.68         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.52/0.68      inference('demod', [status(thm)], ['3', '4'])).
% 0.52/0.68  thf(cc5_funct_2, axiom,
% 0.52/0.68    (![A:$i,B:$i]:
% 0.52/0.68     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.52/0.68       ( ![C:$i]:
% 0.52/0.68         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.68           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.52/0.68             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.52/0.68  thf('11', plain,
% 0.52/0.68      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.52/0.68         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.52/0.68          | (v1_partfun1 @ X26 @ X27)
% 0.52/0.68          | ~ (v1_funct_2 @ X26 @ X27 @ X28)
% 0.52/0.68          | ~ (v1_funct_1 @ X26)
% 0.52/0.68          | (v1_xboole_0 @ X28))),
% 0.52/0.68      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.52/0.68  thf('12', plain,
% 0.52/0.68      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.52/0.68        | ~ (v1_funct_1 @ sk_C)
% 0.52/0.68        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.52/0.68        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.52/0.68      inference('sup-', [status(thm)], ['10', '11'])).
% 0.52/0.68  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 0.52/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.68  thf('14', plain,
% 0.52/0.68      (![X31 : $i]:
% 0.52/0.68         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.52/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.68  thf('15', plain,
% 0.52/0.68      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.52/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.68  thf('16', plain,
% 0.52/0.68      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.52/0.68        | ~ (l1_struct_0 @ sk_A))),
% 0.52/0.68      inference('sup+', [status(thm)], ['14', '15'])).
% 0.52/0.68  thf('17', plain, ((l1_struct_0 @ sk_A)),
% 0.52/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.68  thf('18', plain,
% 0.52/0.68      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.52/0.68      inference('demod', [status(thm)], ['16', '17'])).
% 0.52/0.68  thf('19', plain,
% 0.52/0.68      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.52/0.68        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.52/0.68      inference('demod', [status(thm)], ['12', '13', '18'])).
% 0.52/0.68  thf(d4_partfun1, axiom,
% 0.52/0.68    (![A:$i,B:$i]:
% 0.52/0.68     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.52/0.68       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.52/0.68  thf('20', plain,
% 0.52/0.68      (![X29 : $i, X30 : $i]:
% 0.52/0.68         (~ (v1_partfun1 @ X30 @ X29)
% 0.52/0.68          | ((k1_relat_1 @ X30) = (X29))
% 0.52/0.68          | ~ (v4_relat_1 @ X30 @ X29)
% 0.52/0.68          | ~ (v1_relat_1 @ X30))),
% 0.52/0.68      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.52/0.68  thf('21', plain,
% 0.52/0.68      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.52/0.68        | ~ (v1_relat_1 @ sk_C)
% 0.52/0.68        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.52/0.68        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.52/0.68      inference('sup-', [status(thm)], ['19', '20'])).
% 0.52/0.68  thf('22', plain,
% 0.52/0.68      ((m1_subset_1 @ sk_C @ 
% 0.52/0.68        (k1_zfmisc_1 @ 
% 0.52/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.52/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.68  thf(cc2_relat_1, axiom,
% 0.52/0.68    (![A:$i]:
% 0.52/0.68     ( ( v1_relat_1 @ A ) =>
% 0.52/0.68       ( ![B:$i]:
% 0.52/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.52/0.68  thf('23', plain,
% 0.52/0.68      (![X7 : $i, X8 : $i]:
% 0.52/0.68         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.52/0.68          | (v1_relat_1 @ X7)
% 0.52/0.68          | ~ (v1_relat_1 @ X8))),
% 0.52/0.68      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.52/0.68  thf('24', plain,
% 0.52/0.68      ((~ (v1_relat_1 @ 
% 0.52/0.68           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.52/0.68        | (v1_relat_1 @ sk_C))),
% 0.52/0.68      inference('sup-', [status(thm)], ['22', '23'])).
% 0.52/0.68  thf(fc6_relat_1, axiom,
% 0.52/0.68    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.52/0.68  thf('25', plain,
% 0.52/0.68      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 0.52/0.68      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.52/0.68  thf('26', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.68      inference('demod', [status(thm)], ['24', '25'])).
% 0.52/0.68  thf('27', plain,
% 0.52/0.68      ((m1_subset_1 @ sk_C @ 
% 0.52/0.68        (k1_zfmisc_1 @ 
% 0.52/0.68         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.52/0.68      inference('demod', [status(thm)], ['3', '4'])).
% 0.52/0.68  thf(cc2_relset_1, axiom,
% 0.52/0.68    (![A:$i,B:$i,C:$i]:
% 0.52/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.68       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.52/0.68  thf('28', plain,
% 0.52/0.68      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.52/0.68         ((v4_relat_1 @ X16 @ X17)
% 0.52/0.69          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.52/0.69      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.52/0.69  thf('29', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.52/0.69      inference('sup-', [status(thm)], ['27', '28'])).
% 0.52/0.69  thf('30', plain,
% 0.52/0.69      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.52/0.69        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.52/0.69      inference('demod', [status(thm)], ['21', '26', '29'])).
% 0.52/0.69  thf(l13_xboole_0, axiom,
% 0.52/0.69    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.52/0.69  thf('31', plain,
% 0.52/0.69      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.69      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.52/0.69  thf('32', plain,
% 0.52/0.69      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 0.52/0.69        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.52/0.69      inference('sup-', [status(thm)], ['30', '31'])).
% 0.52/0.69  thf('33', plain,
% 0.52/0.69      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.52/0.69        | ~ (l1_struct_0 @ sk_B)
% 0.52/0.69        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.52/0.69      inference('sup+', [status(thm)], ['9', '32'])).
% 0.52/0.69  thf('34', plain, ((l1_struct_0 @ sk_B)),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.69  thf('35', plain,
% 0.52/0.69      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.52/0.69        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.52/0.69      inference('demod', [status(thm)], ['33', '34'])).
% 0.52/0.69  thf('36', plain,
% 0.52/0.69      ((((k2_struct_0 @ sk_A) = (k1_xboole_0))
% 0.52/0.69        | ((k2_struct_0 @ sk_B) != (k1_xboole_0)))),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.69  thf('37', plain,
% 0.52/0.69      ((((k2_struct_0 @ sk_B) != (k1_xboole_0)))
% 0.52/0.69         <= (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))))),
% 0.52/0.69      inference('split', [status(esa)], ['36'])).
% 0.52/0.69  thf('38', plain,
% 0.52/0.69      (![X31 : $i]:
% 0.52/0.69         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.52/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.69  thf('39', plain,
% 0.52/0.69      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.52/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.69      inference('split', [status(esa)], ['36'])).
% 0.52/0.69  thf('40', plain,
% 0.52/0.69      ((m1_subset_1 @ sk_C @ 
% 0.52/0.69        (k1_zfmisc_1 @ 
% 0.52/0.69         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.52/0.69      inference('demod', [status(thm)], ['3', '4'])).
% 0.52/0.69  thf('41', plain,
% 0.52/0.69      (((m1_subset_1 @ sk_C @ 
% 0.52/0.69         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.52/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.69      inference('sup+', [status(thm)], ['39', '40'])).
% 0.52/0.69  thf('42', plain,
% 0.52/0.69      ((((m1_subset_1 @ sk_C @ 
% 0.52/0.69          (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B))))
% 0.52/0.69         | ~ (l1_struct_0 @ sk_B)))
% 0.52/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.69      inference('sup+', [status(thm)], ['38', '41'])).
% 0.52/0.69  thf('43', plain, ((l1_struct_0 @ sk_B)),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.69  thf('44', plain,
% 0.52/0.69      (((m1_subset_1 @ sk_C @ 
% 0.52/0.69         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B)))))
% 0.52/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.69      inference('demod', [status(thm)], ['42', '43'])).
% 0.52/0.69  thf(t38_relset_1, axiom,
% 0.52/0.69    (![A:$i,B:$i,C:$i]:
% 0.52/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.69       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.52/0.69         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.52/0.69  thf('45', plain,
% 0.52/0.69      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.52/0.69         (((k8_relset_1 @ X23 @ X24 @ X25 @ X24)
% 0.52/0.69            = (k1_relset_1 @ X23 @ X24 @ X25))
% 0.52/0.69          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.52/0.69      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.52/0.69  thf('46', plain,
% 0.52/0.69      ((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.52/0.69          (k2_struct_0 @ sk_B))
% 0.52/0.69          = (k1_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C)))
% 0.52/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.69      inference('sup-', [status(thm)], ['44', '45'])).
% 0.52/0.69  thf('47', plain,
% 0.52/0.69      (((m1_subset_1 @ sk_C @ 
% 0.52/0.69         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B)))))
% 0.52/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.69      inference('demod', [status(thm)], ['42', '43'])).
% 0.52/0.69  thf(redefinition_k1_relset_1, axiom,
% 0.52/0.69    (![A:$i,B:$i,C:$i]:
% 0.52/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.69       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.52/0.69  thf('48', plain,
% 0.52/0.69      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.52/0.69         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 0.52/0.69          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.52/0.69      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.52/0.69  thf('49', plain,
% 0.52/0.69      ((((k1_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.52/0.69          = (k1_relat_1 @ sk_C)))
% 0.52/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.69      inference('sup-', [status(thm)], ['47', '48'])).
% 0.52/0.69  thf('50', plain,
% 0.52/0.69      (((m1_subset_1 @ sk_C @ 
% 0.52/0.69         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.52/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.69      inference('sup+', [status(thm)], ['39', '40'])).
% 0.52/0.69  thf('51', plain,
% 0.52/0.69      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.52/0.69         ((v4_relat_1 @ X16 @ X17)
% 0.52/0.69          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.52/0.69      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.52/0.69  thf('52', plain,
% 0.52/0.69      (((v4_relat_1 @ sk_C @ k1_xboole_0))
% 0.52/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.69      inference('sup-', [status(thm)], ['50', '51'])).
% 0.52/0.69  thf(d18_relat_1, axiom,
% 0.52/0.69    (![A:$i,B:$i]:
% 0.52/0.69     ( ( v1_relat_1 @ B ) =>
% 0.52/0.69       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.52/0.69  thf('53', plain,
% 0.52/0.69      (![X9 : $i, X10 : $i]:
% 0.52/0.69         (~ (v4_relat_1 @ X9 @ X10)
% 0.52/0.69          | (r1_tarski @ (k1_relat_1 @ X9) @ X10)
% 0.52/0.69          | ~ (v1_relat_1 @ X9))),
% 0.52/0.69      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.52/0.69  thf('54', plain,
% 0.52/0.69      (((~ (v1_relat_1 @ sk_C)
% 0.52/0.69         | (r1_tarski @ (k1_relat_1 @ sk_C) @ k1_xboole_0)))
% 0.52/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.69      inference('sup-', [status(thm)], ['52', '53'])).
% 0.52/0.69  thf('55', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.69      inference('demod', [status(thm)], ['24', '25'])).
% 0.52/0.69  thf('56', plain,
% 0.52/0.69      (((r1_tarski @ (k1_relat_1 @ sk_C) @ k1_xboole_0))
% 0.52/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.69      inference('demod', [status(thm)], ['54', '55'])).
% 0.52/0.69  thf(t3_xboole_1, axiom,
% 0.52/0.69    (![A:$i]:
% 0.52/0.69     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.52/0.69  thf('57', plain,
% 0.52/0.69      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (r1_tarski @ X1 @ k1_xboole_0))),
% 0.52/0.69      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.52/0.69  thf('58', plain,
% 0.52/0.69      ((((k1_relat_1 @ sk_C) = (k1_xboole_0)))
% 0.52/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.69      inference('sup-', [status(thm)], ['56', '57'])).
% 0.52/0.69  thf('59', plain,
% 0.52/0.69      ((((k1_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.52/0.69          = (k1_xboole_0)))
% 0.52/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.69      inference('demod', [status(thm)], ['49', '58'])).
% 0.52/0.69  thf('60', plain,
% 0.52/0.69      ((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.52/0.69          (k2_struct_0 @ sk_B)) = (k1_xboole_0)))
% 0.52/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.69      inference('demod', [status(thm)], ['46', '59'])).
% 0.52/0.69  thf('61', plain,
% 0.52/0.69      (![X31 : $i]:
% 0.52/0.69         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.52/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.69  thf('62', plain,
% 0.52/0.69      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.52/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.69      inference('split', [status(esa)], ['36'])).
% 0.52/0.69  thf('63', plain,
% 0.52/0.69      (![X31 : $i]:
% 0.52/0.69         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.52/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.69  thf('64', plain,
% 0.52/0.69      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.52/0.69         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.69  thf('65', plain,
% 0.52/0.69      ((((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.52/0.69          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))
% 0.52/0.69        | ~ (l1_struct_0 @ sk_A))),
% 0.52/0.69      inference('sup-', [status(thm)], ['63', '64'])).
% 0.52/0.69  thf('66', plain, ((l1_struct_0 @ sk_A)),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.69  thf('67', plain,
% 0.52/0.69      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.52/0.69         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.52/0.69      inference('demod', [status(thm)], ['65', '66'])).
% 0.52/0.69  thf('68', plain,
% 0.52/0.69      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.52/0.69          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A)))
% 0.52/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.69      inference('sup-', [status(thm)], ['62', '67'])).
% 0.52/0.69  thf('69', plain,
% 0.52/0.69      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.52/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.69      inference('split', [status(esa)], ['36'])).
% 0.52/0.69  thf('70', plain,
% 0.52/0.69      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.52/0.69          (k2_struct_0 @ sk_B)) != (k1_xboole_0)))
% 0.52/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.69      inference('demod', [status(thm)], ['68', '69'])).
% 0.52/0.69  thf('71', plain,
% 0.52/0.69      (((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.52/0.69           (k2_struct_0 @ sk_B)) != (k1_xboole_0))
% 0.52/0.69         | ~ (l1_struct_0 @ sk_B)))
% 0.52/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.69      inference('sup-', [status(thm)], ['61', '70'])).
% 0.52/0.69  thf('72', plain, ((l1_struct_0 @ sk_B)),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.69  thf('73', plain,
% 0.52/0.69      ((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.52/0.69          (k2_struct_0 @ sk_B)) != (k1_xboole_0)))
% 0.52/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.52/0.69      inference('demod', [status(thm)], ['71', '72'])).
% 0.52/0.69  thf('74', plain, (~ (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.52/0.69      inference('simplify_reflect-', [status(thm)], ['60', '73'])).
% 0.52/0.69  thf('75', plain,
% 0.52/0.69      (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))) | 
% 0.52/0.69       (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.52/0.69      inference('split', [status(esa)], ['36'])).
% 0.52/0.69  thf('76', plain, (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.52/0.69      inference('sat_resolution*', [status(thm)], ['74', '75'])).
% 0.52/0.69  thf('77', plain, (((k2_struct_0 @ sk_B) != (k1_xboole_0))),
% 0.52/0.69      inference('simpl_trail', [status(thm)], ['37', '76'])).
% 0.52/0.69  thf('78', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.52/0.69      inference('simplify_reflect-', [status(thm)], ['35', '77'])).
% 0.52/0.69  thf('79', plain,
% 0.52/0.69      ((m1_subset_1 @ sk_C @ 
% 0.52/0.69        (k1_zfmisc_1 @ 
% 0.52/0.69         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))))),
% 0.52/0.69      inference('demod', [status(thm)], ['8', '78'])).
% 0.52/0.69  thf('80', plain,
% 0.52/0.69      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.52/0.69         (((k8_relset_1 @ X23 @ X24 @ X25 @ X24)
% 0.52/0.69            = (k1_relset_1 @ X23 @ X24 @ X25))
% 0.52/0.69          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.52/0.69      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.52/0.69  thf('81', plain,
% 0.52/0.69      (((k8_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.52/0.69         (k2_struct_0 @ sk_B))
% 0.52/0.69         = (k1_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 0.52/0.69      inference('sup-', [status(thm)], ['79', '80'])).
% 0.52/0.69  thf('82', plain,
% 0.52/0.69      (![X31 : $i]:
% 0.52/0.69         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.52/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.69  thf('83', plain,
% 0.52/0.69      (![X31 : $i]:
% 0.52/0.69         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.52/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.69  thf('84', plain,
% 0.52/0.69      ((m1_subset_1 @ sk_C @ 
% 0.52/0.69        (k1_zfmisc_1 @ 
% 0.52/0.69         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.69  thf('85', plain,
% 0.52/0.69      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.52/0.69         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 0.52/0.69          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.52/0.69      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.52/0.69  thf('86', plain,
% 0.52/0.69      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.52/0.69         = (k1_relat_1 @ sk_C))),
% 0.52/0.69      inference('sup-', [status(thm)], ['84', '85'])).
% 0.52/0.69  thf('87', plain,
% 0.52/0.69      ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.52/0.69          = (k1_relat_1 @ sk_C))
% 0.52/0.69        | ~ (l1_struct_0 @ sk_B))),
% 0.52/0.69      inference('sup+', [status(thm)], ['83', '86'])).
% 0.52/0.69  thf('88', plain, ((l1_struct_0 @ sk_B)),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.69  thf('89', plain,
% 0.52/0.69      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.52/0.69         = (k1_relat_1 @ sk_C))),
% 0.52/0.69      inference('demod', [status(thm)], ['87', '88'])).
% 0.52/0.69  thf('90', plain,
% 0.52/0.69      ((((k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.52/0.69          = (k1_relat_1 @ sk_C))
% 0.52/0.69        | ~ (l1_struct_0 @ sk_A))),
% 0.52/0.69      inference('sup+', [status(thm)], ['82', '89'])).
% 0.52/0.69  thf('91', plain, ((l1_struct_0 @ sk_A)),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.69  thf('92', plain,
% 0.52/0.69      (((k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.52/0.69         = (k1_relat_1 @ sk_C))),
% 0.52/0.69      inference('demod', [status(thm)], ['90', '91'])).
% 0.52/0.69  thf('93', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.52/0.69      inference('simplify_reflect-', [status(thm)], ['35', '77'])).
% 0.52/0.69  thf('94', plain,
% 0.52/0.69      (((k1_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.52/0.69         = (k1_relat_1 @ sk_C))),
% 0.52/0.69      inference('demod', [status(thm)], ['92', '93'])).
% 0.52/0.69  thf('95', plain,
% 0.52/0.69      (((k8_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.52/0.69         (k2_struct_0 @ sk_B)) = (k1_relat_1 @ sk_C))),
% 0.52/0.69      inference('demod', [status(thm)], ['81', '94'])).
% 0.52/0.69  thf('96', plain,
% 0.52/0.69      (![X31 : $i]:
% 0.52/0.69         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.52/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.69  thf('97', plain,
% 0.52/0.69      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.52/0.69         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.69  thf('98', plain,
% 0.52/0.69      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.52/0.69          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))
% 0.52/0.69        | ~ (l1_struct_0 @ sk_B))),
% 0.52/0.69      inference('sup-', [status(thm)], ['96', '97'])).
% 0.52/0.69  thf('99', plain, ((l1_struct_0 @ sk_B)),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.69  thf('100', plain,
% 0.52/0.69      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.52/0.69         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.52/0.69      inference('demod', [status(thm)], ['98', '99'])).
% 0.52/0.69  thf('101', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.52/0.69      inference('simplify_reflect-', [status(thm)], ['35', '77'])).
% 0.52/0.69  thf('102', plain,
% 0.52/0.69      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.52/0.69         (k2_struct_0 @ sk_B)) != (k1_relat_1 @ sk_C))),
% 0.52/0.69      inference('demod', [status(thm)], ['100', '101'])).
% 0.52/0.69  thf('103', plain,
% 0.52/0.69      (![X31 : $i]:
% 0.52/0.69         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.52/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.52/0.69  thf('104', plain,
% 0.52/0.69      ((m1_subset_1 @ sk_C @ 
% 0.52/0.69        (k1_zfmisc_1 @ 
% 0.52/0.69         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.69  thf('105', plain,
% 0.52/0.69      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.52/0.69         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.52/0.69          | (v1_partfun1 @ X26 @ X27)
% 0.52/0.69          | ~ (v1_funct_2 @ X26 @ X27 @ X28)
% 0.52/0.69          | ~ (v1_funct_1 @ X26)
% 0.52/0.69          | (v1_xboole_0 @ X28))),
% 0.52/0.69      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.52/0.69  thf('106', plain,
% 0.52/0.69      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.52/0.69        | ~ (v1_funct_1 @ sk_C)
% 0.52/0.69        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.52/0.69        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.52/0.69      inference('sup-', [status(thm)], ['104', '105'])).
% 0.52/0.69  thf('107', plain, ((v1_funct_1 @ sk_C)),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.69  thf('108', plain,
% 0.52/0.69      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.69  thf('109', plain,
% 0.52/0.69      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.52/0.69        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.52/0.69      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.52/0.69  thf('110', plain,
% 0.52/0.69      (![X29 : $i, X30 : $i]:
% 0.52/0.69         (~ (v1_partfun1 @ X30 @ X29)
% 0.52/0.69          | ((k1_relat_1 @ X30) = (X29))
% 0.52/0.69          | ~ (v4_relat_1 @ X30 @ X29)
% 0.52/0.69          | ~ (v1_relat_1 @ X30))),
% 0.52/0.69      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.52/0.69  thf('111', plain,
% 0.52/0.69      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.52/0.69        | ~ (v1_relat_1 @ sk_C)
% 0.52/0.69        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.52/0.69        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.52/0.69      inference('sup-', [status(thm)], ['109', '110'])).
% 0.52/0.69  thf('112', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.69      inference('demod', [status(thm)], ['24', '25'])).
% 0.52/0.69  thf('113', plain,
% 0.52/0.69      ((m1_subset_1 @ sk_C @ 
% 0.52/0.69        (k1_zfmisc_1 @ 
% 0.52/0.69         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.69  thf('114', plain,
% 0.52/0.69      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.52/0.69         ((v4_relat_1 @ X16 @ X17)
% 0.52/0.69          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.52/0.69      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.52/0.69  thf('115', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.52/0.69      inference('sup-', [status(thm)], ['113', '114'])).
% 0.52/0.69  thf('116', plain,
% 0.52/0.69      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.52/0.69        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.52/0.69      inference('demod', [status(thm)], ['111', '112', '115'])).
% 0.52/0.69  thf('117', plain,
% 0.52/0.69      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.69      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.52/0.69  thf('118', plain,
% 0.52/0.69      ((((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))
% 0.52/0.69        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.52/0.69      inference('sup-', [status(thm)], ['116', '117'])).
% 0.52/0.69  thf('119', plain,
% 0.52/0.69      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.52/0.69        | ~ (l1_struct_0 @ sk_B)
% 0.52/0.69        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.52/0.69      inference('sup+', [status(thm)], ['103', '118'])).
% 0.52/0.69  thf('120', plain, ((l1_struct_0 @ sk_B)),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.69  thf('121', plain,
% 0.52/0.69      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.52/0.69        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.52/0.69      inference('demod', [status(thm)], ['119', '120'])).
% 0.52/0.69  thf('122', plain, (((k2_struct_0 @ sk_B) != (k1_xboole_0))),
% 0.52/0.69      inference('simpl_trail', [status(thm)], ['37', '76'])).
% 0.52/0.69  thf('123', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.52/0.69      inference('simplify_reflect-', [status(thm)], ['121', '122'])).
% 0.52/0.69  thf('124', plain,
% 0.52/0.69      (((k8_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.52/0.69         (k2_struct_0 @ sk_B)) != (k1_relat_1 @ sk_C))),
% 0.52/0.69      inference('demod', [status(thm)], ['102', '123'])).
% 0.52/0.69  thf('125', plain, ($false),
% 0.52/0.69      inference('simplify_reflect-', [status(thm)], ['95', '124'])).
% 0.52/0.69  
% 0.52/0.69  % SZS output end Refutation
% 0.52/0.69  
% 0.52/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
