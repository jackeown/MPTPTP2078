%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Vg83RCDCSj

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:03 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 273 expanded)
%              Number of leaves         :   45 (  97 expanded)
%              Depth                    :   24
%              Number of atoms          : 1279 (6000 expanded)
%              Number of equality atoms :   63 ( 250 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(t186_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( v1_xboole_0 @ C )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ C )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ! [E: $i] :
              ( ( ( v1_funct_1 @ E )
                & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) )
             => ! [F: $i] :
                  ( ( m1_subset_1 @ F @ B )
                 => ( ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ ( k1_relset_1 @ C @ A @ E ) )
                   => ( ( B = k1_xboole_0 )
                      | ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F )
                        = ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ~ ( v1_xboole_0 @ C )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ C )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
           => ! [E: $i] :
                ( ( ( v1_funct_1 @ E )
                  & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) )
               => ! [F: $i] :
                    ( ( m1_subset_1 @ F @ B )
                   => ( ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ ( k1_relset_1 @ C @ A @ E ) )
                     => ( ( B = k1_xboole_0 )
                        | ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F )
                          = ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t186_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc6_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ~ ( v1_xboole_0 @ C )
              & ( v1_funct_2 @ C @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( v1_xboole_0 @ X35 )
      | ( v1_xboole_0 @ X36 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ~ ( v1_xboole_0 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc6_funct_2])).

thf('2',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v5_relat_1 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('10',plain,(
    v5_relat_1 @ sk_E @ sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('13',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('16',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('17',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('20',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('21',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t14_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) )).

thf('24',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X25 ) @ X26 )
      | ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[t14_relset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('27',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ X49 @ X50 )
      | ( X51 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_funct_2 @ X52 @ X50 @ X51 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X52 @ X49 ) @ X51 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ ( k1_relat_1 @ sk_E ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('30',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_partfun1 @ X29 @ X30 )
      | ( v1_funct_2 @ X29 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('31',plain,
    ( ( v1_funct_2 @ sk_D @ sk_B @ ( k1_relat_1 @ sk_E ) )
    | ~ ( v1_partfun1 @ sk_D @ sk_B )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v1_funct_2 @ sk_D @ sk_B @ ( k1_relat_1 @ sk_E ) )
    | ~ ( v1_partfun1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('35',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( v1_partfun1 @ X32 @ X33 )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X34 )
      | ~ ( v1_funct_1 @ X32 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('36',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C )
    | ( v1_partfun1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_partfun1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_partfun1 @ sk_D @ sk_B ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    v1_funct_2 @ sk_D @ sk_B @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['33','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','42','43'])).

thf('45',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['13','44'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('46',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X38 @ ( k1_relat_1 @ X39 ) )
      | ( ( k7_partfun1 @ X40 @ X39 @ X38 )
        = ( k1_funct_1 @ X39 @ X38 ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v5_relat_1 @ X39 @ X40 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_E )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('49',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('50',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['47','50','51'])).

thf('53',plain,
    ( ( ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
      = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( v1_xboole_0 @ sk_B )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','52'])).

thf('54',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('57',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t185_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( v1_xboole_0 @ C )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ C )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ! [E: $i] :
              ( ( ( v1_funct_1 @ E )
                & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) )
             => ! [F: $i] :
                  ( ( m1_subset_1 @ F @ B )
                 => ( ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ ( k1_relset_1 @ C @ A @ E ) )
                   => ( ( B = k1_xboole_0 )
                      | ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F )
                        = ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )).

thf('58',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( m1_subset_1 @ X44 @ X42 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ X42 @ X43 @ X46 @ X41 @ X45 ) @ X44 )
        = ( k1_funct_1 @ X45 @ ( k1_funct_1 @ X41 @ X44 ) ) )
      | ( X42 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X42 @ X43 @ X41 ) @ ( k1_relset_1 @ X43 @ X46 @ X45 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X46 ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ( v1_xboole_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t185_funct_2])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ X1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('61',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relset_1 @ sk_C @ X1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf('64',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relset_1 @ sk_C @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['56','65'])).

thf('67',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('68',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('71',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['55','72'])).

thf('74',plain,(
    ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['54','73'])).

thf('75',plain,
    ( ( ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['53','74'])).

thf('76',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('78',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('79',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_B @ k1_xboole_0 ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['76','79'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('81',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('82',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['80','82'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('84',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('85',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('88',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('89',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    sk_D = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['89','90'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('92',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('93',plain,(
    v1_xboole_0 @ sk_B ),
    inference(demod,[status(thm)],['7','91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('95',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['95','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Vg83RCDCSj
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:03:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.53/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.53/0.71  % Solved by: fo/fo7.sh
% 0.53/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.71  % done 494 iterations in 0.254s
% 0.53/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.53/0.71  % SZS output start Refutation
% 0.53/0.71  thf(sk_D_type, type, sk_D: $i).
% 0.53/0.71  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.53/0.71  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.53/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.53/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.71  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.53/0.71  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.53/0.71  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.53/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.53/0.71  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 0.53/0.71  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.53/0.71  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.53/0.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.53/0.71  thf(sk_C_type, type, sk_C: $i).
% 0.53/0.71  thf(sk_F_type, type, sk_F: $i).
% 0.53/0.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.53/0.71  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.53/0.71  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 0.53/0.71  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.53/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.53/0.71  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.53/0.71  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.53/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.71  thf(sk_E_type, type, sk_E: $i).
% 0.53/0.71  thf(t186_funct_2, conjecture,
% 0.53/0.71    (![A:$i,B:$i,C:$i]:
% 0.53/0.71     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.53/0.71       ( ![D:$i]:
% 0.53/0.71         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.53/0.71             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.53/0.71           ( ![E:$i]:
% 0.53/0.71             ( ( ( v1_funct_1 @ E ) & 
% 0.53/0.71                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.53/0.71               ( ![F:$i]:
% 0.53/0.71                 ( ( m1_subset_1 @ F @ B ) =>
% 0.53/0.71                   ( ( r1_tarski @
% 0.53/0.71                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.53/0.71                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.53/0.71                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.53/0.71                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.53/0.71                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.53/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.71    (~( ![A:$i,B:$i,C:$i]:
% 0.53/0.71        ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.53/0.71          ( ![D:$i]:
% 0.53/0.71            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.53/0.71                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.53/0.71              ( ![E:$i]:
% 0.53/0.71                ( ( ( v1_funct_1 @ E ) & 
% 0.53/0.71                    ( m1_subset_1 @
% 0.53/0.71                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.53/0.71                  ( ![F:$i]:
% 0.53/0.71                    ( ( m1_subset_1 @ F @ B ) =>
% 0.53/0.71                      ( ( r1_tarski @
% 0.53/0.71                          ( k2_relset_1 @ B @ C @ D ) @ 
% 0.53/0.71                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.53/0.71                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.53/0.71                          ( ( k1_funct_1 @
% 0.53/0.71                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.53/0.71                            ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.53/0.71    inference('cnf.neg', [status(esa)], [t186_funct_2])).
% 0.53/0.71  thf('0', plain,
% 0.53/0.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf(cc6_funct_2, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.53/0.71       ( ![C:$i]:
% 0.53/0.71         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.71           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.53/0.71             ( ( v1_funct_1 @ C ) & ( ~( v1_xboole_0 @ C ) ) & 
% 0.53/0.71               ( v1_funct_2 @ C @ A @ B ) ) ) ) ) ))).
% 0.53/0.71  thf('1', plain,
% 0.53/0.71      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.53/0.71         ((v1_xboole_0 @ X35)
% 0.53/0.71          | (v1_xboole_0 @ X36)
% 0.53/0.71          | ~ (v1_funct_1 @ X37)
% 0.53/0.71          | ~ (v1_funct_2 @ X37 @ X35 @ X36)
% 0.53/0.71          | ~ (v1_xboole_0 @ X37)
% 0.53/0.71          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.53/0.71      inference('cnf', [status(esa)], [cc6_funct_2])).
% 0.53/0.71  thf('2', plain,
% 0.53/0.71      ((~ (v1_xboole_0 @ sk_D)
% 0.53/0.71        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 0.53/0.71        | ~ (v1_funct_1 @ sk_D)
% 0.53/0.71        | (v1_xboole_0 @ sk_C)
% 0.53/0.71        | (v1_xboole_0 @ sk_B))),
% 0.53/0.71      inference('sup-', [status(thm)], ['0', '1'])).
% 0.53/0.71  thf('3', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('5', plain,
% 0.53/0.71      ((~ (v1_xboole_0 @ sk_D) | (v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B))),
% 0.53/0.71      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.53/0.71  thf('6', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('7', plain, (((v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ sk_D))),
% 0.53/0.71      inference('clc', [status(thm)], ['5', '6'])).
% 0.53/0.71  thf('8', plain,
% 0.53/0.71      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf(cc2_relset_1, axiom,
% 0.53/0.71    (![A:$i,B:$i,C:$i]:
% 0.53/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.71       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.53/0.71  thf('9', plain,
% 0.53/0.71      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.53/0.71         ((v5_relat_1 @ X16 @ X18)
% 0.53/0.71          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.53/0.71      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.53/0.71  thf('10', plain, ((v5_relat_1 @ sk_E @ sk_A)),
% 0.53/0.71      inference('sup-', [status(thm)], ['8', '9'])).
% 0.53/0.71  thf('11', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf(t2_subset, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( m1_subset_1 @ A @ B ) =>
% 0.53/0.71       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.53/0.71  thf('12', plain,
% 0.53/0.71      (![X8 : $i, X9 : $i]:
% 0.53/0.71         ((r2_hidden @ X8 @ X9)
% 0.53/0.71          | (v1_xboole_0 @ X9)
% 0.53/0.71          | ~ (m1_subset_1 @ X8 @ X9))),
% 0.53/0.71      inference('cnf', [status(esa)], [t2_subset])).
% 0.53/0.71  thf('13', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_F @ sk_B))),
% 0.53/0.71      inference('sup-', [status(thm)], ['11', '12'])).
% 0.53/0.71  thf('14', plain,
% 0.53/0.71      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 0.53/0.71        (k1_relset_1 @ sk_C @ sk_A @ sk_E))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('15', plain,
% 0.53/0.71      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf(redefinition_k1_relset_1, axiom,
% 0.53/0.71    (![A:$i,B:$i,C:$i]:
% 0.53/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.71       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.53/0.71  thf('16', plain,
% 0.53/0.71      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.53/0.71         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 0.53/0.71          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.53/0.71      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.53/0.71  thf('17', plain,
% 0.53/0.71      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.53/0.71      inference('sup-', [status(thm)], ['15', '16'])).
% 0.53/0.71  thf('18', plain,
% 0.53/0.71      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ (k1_relat_1 @ sk_E))),
% 0.53/0.71      inference('demod', [status(thm)], ['14', '17'])).
% 0.53/0.71  thf('19', plain,
% 0.53/0.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf(redefinition_k2_relset_1, axiom,
% 0.53/0.71    (![A:$i,B:$i,C:$i]:
% 0.53/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.71       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.53/0.71  thf('20', plain,
% 0.53/0.71      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.53/0.71         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 0.53/0.71          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.53/0.71      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.53/0.71  thf('21', plain,
% 0.53/0.71      (((k2_relset_1 @ sk_B @ sk_C @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.53/0.71      inference('sup-', [status(thm)], ['19', '20'])).
% 0.53/0.71  thf('22', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 0.53/0.71      inference('demod', [status(thm)], ['18', '21'])).
% 0.53/0.71  thf('23', plain,
% 0.53/0.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf(t14_relset_1, axiom,
% 0.53/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.71     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.53/0.71       ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B ) =>
% 0.53/0.71         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ))).
% 0.53/0.71  thf('24', plain,
% 0.53/0.71      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.53/0.71         (~ (r1_tarski @ (k2_relat_1 @ X25) @ X26)
% 0.53/0.71          | (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 0.53/0.71          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.53/0.71      inference('cnf', [status(esa)], [t14_relset_1])).
% 0.53/0.71  thf('25', plain,
% 0.53/0.71      (![X0 : $i]:
% 0.53/0.71         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.53/0.71          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.53/0.71      inference('sup-', [status(thm)], ['23', '24'])).
% 0.53/0.71  thf('26', plain,
% 0.53/0.71      ((m1_subset_1 @ sk_D @ 
% 0.53/0.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_E))))),
% 0.53/0.71      inference('sup-', [status(thm)], ['22', '25'])).
% 0.53/0.71  thf(t7_funct_2, axiom,
% 0.53/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.71     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.53/0.71         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.71       ( ( r2_hidden @ C @ A ) =>
% 0.53/0.71         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.53/0.71           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.53/0.71  thf('27', plain,
% 0.53/0.71      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 0.53/0.71         (~ (r2_hidden @ X49 @ X50)
% 0.53/0.71          | ((X51) = (k1_xboole_0))
% 0.53/0.71          | ~ (v1_funct_1 @ X52)
% 0.53/0.71          | ~ (v1_funct_2 @ X52 @ X50 @ X51)
% 0.53/0.71          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 0.53/0.71          | (r2_hidden @ (k1_funct_1 @ X52 @ X49) @ X51))),
% 0.53/0.71      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.53/0.71  thf('28', plain,
% 0.53/0.71      (![X0 : $i]:
% 0.53/0.71         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_relat_1 @ sk_E))
% 0.53/0.71          | ~ (v1_funct_2 @ sk_D @ sk_B @ (k1_relat_1 @ sk_E))
% 0.53/0.71          | ~ (v1_funct_1 @ sk_D)
% 0.53/0.71          | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.53/0.71          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.53/0.71      inference('sup-', [status(thm)], ['26', '27'])).
% 0.53/0.71  thf('29', plain,
% 0.53/0.71      ((m1_subset_1 @ sk_D @ 
% 0.53/0.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_E))))),
% 0.53/0.71      inference('sup-', [status(thm)], ['22', '25'])).
% 0.53/0.71  thf(cc1_funct_2, axiom,
% 0.53/0.71    (![A:$i,B:$i,C:$i]:
% 0.53/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.71       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.53/0.71         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 0.53/0.71  thf('30', plain,
% 0.53/0.71      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.53/0.71         (~ (v1_funct_1 @ X29)
% 0.53/0.71          | ~ (v1_partfun1 @ X29 @ X30)
% 0.53/0.71          | (v1_funct_2 @ X29 @ X30 @ X31)
% 0.53/0.71          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.53/0.71      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.53/0.71  thf('31', plain,
% 0.53/0.71      (((v1_funct_2 @ sk_D @ sk_B @ (k1_relat_1 @ sk_E))
% 0.53/0.71        | ~ (v1_partfun1 @ sk_D @ sk_B)
% 0.53/0.71        | ~ (v1_funct_1 @ sk_D))),
% 0.53/0.71      inference('sup-', [status(thm)], ['29', '30'])).
% 0.53/0.71  thf('32', plain, ((v1_funct_1 @ sk_D)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('33', plain,
% 0.53/0.71      (((v1_funct_2 @ sk_D @ sk_B @ (k1_relat_1 @ sk_E))
% 0.53/0.71        | ~ (v1_partfun1 @ sk_D @ sk_B))),
% 0.53/0.71      inference('demod', [status(thm)], ['31', '32'])).
% 0.53/0.71  thf('34', plain,
% 0.53/0.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf(cc5_funct_2, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.53/0.71       ( ![C:$i]:
% 0.53/0.71         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.71           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.53/0.71             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.53/0.71  thf('35', plain,
% 0.53/0.71      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.53/0.71         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.53/0.71          | (v1_partfun1 @ X32 @ X33)
% 0.53/0.71          | ~ (v1_funct_2 @ X32 @ X33 @ X34)
% 0.53/0.71          | ~ (v1_funct_1 @ X32)
% 0.53/0.71          | (v1_xboole_0 @ X34))),
% 0.53/0.71      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.53/0.71  thf('36', plain,
% 0.53/0.71      (((v1_xboole_0 @ sk_C)
% 0.53/0.71        | ~ (v1_funct_1 @ sk_D)
% 0.53/0.71        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 0.53/0.71        | (v1_partfun1 @ sk_D @ sk_B))),
% 0.53/0.71      inference('sup-', [status(thm)], ['34', '35'])).
% 0.53/0.71  thf('37', plain, ((v1_funct_1 @ sk_D)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('38', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('39', plain, (((v1_xboole_0 @ sk_C) | (v1_partfun1 @ sk_D @ sk_B))),
% 0.53/0.71      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.53/0.71  thf('40', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('41', plain, ((v1_partfun1 @ sk_D @ sk_B)),
% 0.53/0.71      inference('clc', [status(thm)], ['39', '40'])).
% 0.53/0.71  thf('42', plain, ((v1_funct_2 @ sk_D @ sk_B @ (k1_relat_1 @ sk_E))),
% 0.53/0.71      inference('demod', [status(thm)], ['33', '41'])).
% 0.53/0.71  thf('43', plain, ((v1_funct_1 @ sk_D)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('44', plain,
% 0.53/0.71      (![X0 : $i]:
% 0.53/0.71         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_relat_1 @ sk_E))
% 0.53/0.71          | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.53/0.71          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.53/0.71      inference('demod', [status(thm)], ['28', '42', '43'])).
% 0.53/0.71  thf('45', plain,
% 0.53/0.71      (((v1_xboole_0 @ sk_B)
% 0.53/0.71        | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.53/0.71        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k1_relat_1 @ sk_E)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['13', '44'])).
% 0.53/0.71  thf(d8_partfun1, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.53/0.71       ( ![C:$i]:
% 0.53/0.71         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.53/0.71           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.53/0.71  thf('46', plain,
% 0.53/0.71      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.53/0.71         (~ (r2_hidden @ X38 @ (k1_relat_1 @ X39))
% 0.53/0.71          | ((k7_partfun1 @ X40 @ X39 @ X38) = (k1_funct_1 @ X39 @ X38))
% 0.53/0.71          | ~ (v1_funct_1 @ X39)
% 0.53/0.71          | ~ (v5_relat_1 @ X39 @ X40)
% 0.53/0.71          | ~ (v1_relat_1 @ X39))),
% 0.53/0.71      inference('cnf', [status(esa)], [d8_partfun1])).
% 0.53/0.71  thf('47', plain,
% 0.53/0.71      (![X0 : $i]:
% 0.53/0.71         (((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.53/0.71          | (v1_xboole_0 @ sk_B)
% 0.53/0.71          | ~ (v1_relat_1 @ sk_E)
% 0.53/0.71          | ~ (v5_relat_1 @ sk_E @ X0)
% 0.53/0.71          | ~ (v1_funct_1 @ sk_E)
% 0.53/0.71          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.53/0.71              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.53/0.71      inference('sup-', [status(thm)], ['45', '46'])).
% 0.53/0.71  thf('48', plain,
% 0.53/0.71      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf(cc1_relset_1, axiom,
% 0.53/0.71    (![A:$i,B:$i,C:$i]:
% 0.53/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.71       ( v1_relat_1 @ C ) ))).
% 0.53/0.71  thf('49', plain,
% 0.53/0.71      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.53/0.71         ((v1_relat_1 @ X13)
% 0.53/0.71          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.53/0.71      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.53/0.71  thf('50', plain, ((v1_relat_1 @ sk_E)),
% 0.53/0.71      inference('sup-', [status(thm)], ['48', '49'])).
% 0.53/0.71  thf('51', plain, ((v1_funct_1 @ sk_E)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('52', plain,
% 0.53/0.71      (![X0 : $i]:
% 0.53/0.71         (((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.53/0.71          | (v1_xboole_0 @ sk_B)
% 0.53/0.71          | ~ (v5_relat_1 @ sk_E @ X0)
% 0.53/0.71          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.53/0.71              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.53/0.71      inference('demod', [status(thm)], ['47', '50', '51'])).
% 0.53/0.71  thf('53', plain,
% 0.53/0.71      ((((k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.53/0.71          = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.53/0.71        | (v1_xboole_0 @ sk_B)
% 0.53/0.71        | ((k1_relat_1 @ sk_E) = (k1_xboole_0)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['10', '52'])).
% 0.53/0.71  thf('54', plain,
% 0.53/0.71      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 0.53/0.71         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('55', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('56', plain,
% 0.53/0.71      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.53/0.71      inference('sup-', [status(thm)], ['15', '16'])).
% 0.53/0.71  thf('57', plain,
% 0.53/0.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf(t185_funct_2, axiom,
% 0.53/0.71    (![A:$i,B:$i,C:$i]:
% 0.53/0.71     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.53/0.71       ( ![D:$i]:
% 0.53/0.71         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.53/0.71             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.53/0.71           ( ![E:$i]:
% 0.53/0.71             ( ( ( v1_funct_1 @ E ) & 
% 0.53/0.71                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.53/0.71               ( ![F:$i]:
% 0.53/0.71                 ( ( m1_subset_1 @ F @ B ) =>
% 0.53/0.71                   ( ( r1_tarski @
% 0.53/0.71                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.53/0.71                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.53/0.71                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.53/0.71                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.53/0.71                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.53/0.71  thf('58', plain,
% 0.53/0.71      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.53/0.71         (~ (v1_funct_1 @ X41)
% 0.53/0.71          | ~ (v1_funct_2 @ X41 @ X42 @ X43)
% 0.53/0.71          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 0.53/0.71          | ~ (m1_subset_1 @ X44 @ X42)
% 0.53/0.71          | ((k1_funct_1 @ (k8_funct_2 @ X42 @ X43 @ X46 @ X41 @ X45) @ X44)
% 0.53/0.71              = (k1_funct_1 @ X45 @ (k1_funct_1 @ X41 @ X44)))
% 0.53/0.71          | ((X42) = (k1_xboole_0))
% 0.53/0.71          | ~ (r1_tarski @ (k2_relset_1 @ X42 @ X43 @ X41) @ 
% 0.53/0.71               (k1_relset_1 @ X43 @ X46 @ X45))
% 0.53/0.71          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X46)))
% 0.53/0.71          | ~ (v1_funct_1 @ X45)
% 0.53/0.71          | (v1_xboole_0 @ X43))),
% 0.53/0.71      inference('cnf', [status(esa)], [t185_funct_2])).
% 0.53/0.71  thf('59', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.71         ((v1_xboole_0 @ sk_C)
% 0.53/0.71          | ~ (v1_funct_1 @ X0)
% 0.53/0.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 0.53/0.71          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 0.53/0.71               (k1_relset_1 @ sk_C @ X1 @ X0))
% 0.53/0.71          | ((sk_B) = (k1_xboole_0))
% 0.53/0.71          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 0.53/0.71              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.53/0.71          | ~ (m1_subset_1 @ X2 @ sk_B)
% 0.53/0.71          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 0.53/0.71          | ~ (v1_funct_1 @ sk_D))),
% 0.53/0.71      inference('sup-', [status(thm)], ['57', '58'])).
% 0.53/0.71  thf('60', plain,
% 0.53/0.71      (((k2_relset_1 @ sk_B @ sk_C @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.53/0.71      inference('sup-', [status(thm)], ['19', '20'])).
% 0.53/0.71  thf('61', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('62', plain, ((v1_funct_1 @ sk_D)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('63', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.71         ((v1_xboole_0 @ sk_C)
% 0.53/0.71          | ~ (v1_funct_1 @ X0)
% 0.53/0.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 0.53/0.71          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relset_1 @ sk_C @ X1 @ X0))
% 0.53/0.71          | ((sk_B) = (k1_xboole_0))
% 0.53/0.71          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 0.53/0.71              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.53/0.71          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 0.53/0.71      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 0.53/0.71  thf('64', plain, (((sk_B) != (k1_xboole_0))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('65', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.71         ((v1_xboole_0 @ sk_C)
% 0.53/0.71          | ~ (v1_funct_1 @ X0)
% 0.53/0.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 0.53/0.71          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relset_1 @ sk_C @ X1 @ X0))
% 0.53/0.71          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 0.53/0.71              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.53/0.71          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 0.53/0.71      inference('simplify_reflect-', [status(thm)], ['63', '64'])).
% 0.53/0.71  thf('66', plain,
% 0.53/0.71      (![X0 : $i]:
% 0.53/0.71         (~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))
% 0.53/0.71          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.53/0.71          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ X0)
% 0.53/0.71              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.53/0.71          | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))
% 0.53/0.71          | ~ (v1_funct_1 @ sk_E)
% 0.53/0.71          | (v1_xboole_0 @ sk_C))),
% 0.53/0.71      inference('sup-', [status(thm)], ['56', '65'])).
% 0.53/0.71  thf('67', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 0.53/0.71      inference('demod', [status(thm)], ['18', '21'])).
% 0.53/0.71  thf('68', plain,
% 0.53/0.71      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('69', plain, ((v1_funct_1 @ sk_E)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('70', plain,
% 0.53/0.71      (![X0 : $i]:
% 0.53/0.71         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.53/0.71          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ X0)
% 0.53/0.71              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.53/0.71          | (v1_xboole_0 @ sk_C))),
% 0.53/0.71      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 0.53/0.71  thf('71', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('72', plain,
% 0.53/0.71      (![X0 : $i]:
% 0.53/0.71         (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ X0)
% 0.53/0.71            = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.53/0.71          | ~ (m1_subset_1 @ X0 @ sk_B))),
% 0.53/0.71      inference('clc', [status(thm)], ['70', '71'])).
% 0.53/0.71  thf('73', plain,
% 0.53/0.71      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 0.53/0.71         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['55', '72'])).
% 0.53/0.71  thf('74', plain,
% 0.53/0.71      (((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.53/0.71         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.53/0.71      inference('demod', [status(thm)], ['54', '73'])).
% 0.53/0.71  thf('75', plain,
% 0.53/0.71      ((((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.53/0.71          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.53/0.71        | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 0.53/0.71        | (v1_xboole_0 @ sk_B))),
% 0.53/0.71      inference('sup-', [status(thm)], ['53', '74'])).
% 0.53/0.71  thf('76', plain,
% 0.53/0.71      (((v1_xboole_0 @ sk_B) | ((k1_relat_1 @ sk_E) = (k1_xboole_0)))),
% 0.53/0.71      inference('simplify', [status(thm)], ['75'])).
% 0.53/0.71  thf('77', plain,
% 0.53/0.71      ((m1_subset_1 @ sk_D @ 
% 0.53/0.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_E))))),
% 0.53/0.71      inference('sup-', [status(thm)], ['22', '25'])).
% 0.53/0.71  thf(t3_subset, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.53/0.71  thf('78', plain,
% 0.53/0.71      (![X10 : $i, X11 : $i]:
% 0.53/0.71         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.53/0.71      inference('cnf', [status(esa)], [t3_subset])).
% 0.53/0.71  thf('79', plain,
% 0.53/0.71      ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_E)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['77', '78'])).
% 0.53/0.71  thf('80', plain,
% 0.53/0.71      (((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_B @ k1_xboole_0))
% 0.53/0.71        | (v1_xboole_0 @ sk_B))),
% 0.53/0.71      inference('sup+', [status(thm)], ['76', '79'])).
% 0.53/0.71  thf(t113_zfmisc_1, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.53/0.71       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.53/0.71  thf('81', plain,
% 0.53/0.71      (![X6 : $i, X7 : $i]:
% 0.53/0.71         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 0.53/0.71      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.53/0.71  thf('82', plain,
% 0.53/0.71      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.71      inference('simplify', [status(thm)], ['81'])).
% 0.53/0.71  thf('83', plain, (((r1_tarski @ sk_D @ k1_xboole_0) | (v1_xboole_0 @ sk_B))),
% 0.53/0.71      inference('demod', [status(thm)], ['80', '82'])).
% 0.53/0.71  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.53/0.71  thf('84', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.53/0.71      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.53/0.71  thf(d10_xboole_0, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.53/0.71  thf('85', plain,
% 0.53/0.71      (![X1 : $i, X3 : $i]:
% 0.53/0.71         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.53/0.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.53/0.71  thf('86', plain,
% 0.53/0.71      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['84', '85'])).
% 0.53/0.71  thf('87', plain, (((v1_xboole_0 @ sk_B) | ((sk_D) = (k1_xboole_0)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['83', '86'])).
% 0.53/0.71  thf(l13_xboole_0, axiom,
% 0.53/0.71    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.53/0.71  thf('88', plain,
% 0.53/0.71      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.53/0.71      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.53/0.71  thf('89', plain, ((((sk_D) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['87', '88'])).
% 0.53/0.71  thf('90', plain, (((sk_B) != (k1_xboole_0))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('91', plain, (((sk_D) = (k1_xboole_0))),
% 0.53/0.71      inference('simplify_reflect-', [status(thm)], ['89', '90'])).
% 0.53/0.71  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.53/0.71  thf('92', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.53/0.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.53/0.71  thf('93', plain, ((v1_xboole_0 @ sk_B)),
% 0.53/0.71      inference('demod', [status(thm)], ['7', '91', '92'])).
% 0.53/0.71  thf('94', plain,
% 0.53/0.71      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.53/0.71      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.53/0.71  thf('95', plain, (((sk_B) = (k1_xboole_0))),
% 0.53/0.71      inference('sup-', [status(thm)], ['93', '94'])).
% 0.53/0.71  thf('96', plain, (((sk_B) != (k1_xboole_0))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('97', plain, ($false),
% 0.53/0.71      inference('simplify_reflect-', [status(thm)], ['95', '96'])).
% 0.53/0.71  
% 0.53/0.71  % SZS output end Refutation
% 0.53/0.71  
% 0.53/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
