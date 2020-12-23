%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B4NSYsMnvh

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:52 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 127 expanded)
%              Number of leaves         :   37 (  54 expanded)
%              Depth                    :   14
%              Number of atoms          :  772 (1983 expanded)
%              Number of equality atoms :   28 (  57 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(t24_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ ( k6_partfun1 @ B ) )
           => ( ( k2_relset_1 @ A @ B @ C )
              = B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( r2_relset_1 @ B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ ( k6_partfun1 @ B ) )
             => ( ( k2_relset_1 @ A @ B @ C )
                = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('7',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['4','7'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('10',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = sk_B )
    | ( r2_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('13',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( ( k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35 )
        = ( k5_relat_1 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C )
      = ( k5_relat_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r2_relset_1 @ sk_B @ sk_B @ ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k6_partfun1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('20',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('21',plain,(
    r2_relset_1 @ sk_B @ sk_B @ ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('24',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('31',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( X20 = X23 )
      | ~ ( r2_relset_1 @ X21 @ X22 @ X20 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_B @ sk_B @ ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C ) @ X0 )
      | ( ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) )
    | ( ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','32'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('34',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('35',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('36',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,
    ( ( k6_relat_1 @ sk_B )
    = ( k5_relat_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['17','18','37'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('39',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) ) @ ( k2_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf(t60_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_tarski @ A @ B )
        & ( r2_xboole_0 @ B @ A ) ) )).

thf('40',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r2_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t60_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_xboole_0 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( r2_xboole_0 @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k6_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('43',plain,(
    ! [X10: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('44',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('47',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( r2_xboole_0 @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['42','43','44','47'])).

thf('49',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup-',[status(thm)],['10','48'])).

thf('50',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('52',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('53',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ( k2_relat_1 @ sk_C )
 != sk_B ),
    inference(demod,[status(thm)],['50','53'])).

thf('55',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['49','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B4NSYsMnvh
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:42:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.44/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.64  % Solved by: fo/fo7.sh
% 0.44/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.64  % done 417 iterations in 0.194s
% 0.44/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.64  % SZS output start Refutation
% 0.44/0.64  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.44/0.64  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.44/0.64  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.44/0.64  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.44/0.64  thf(sk_C_type, type, sk_C: $i).
% 0.44/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.64  thf(sk_D_type, type, sk_D: $i).
% 0.44/0.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.44/0.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.64  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.44/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.44/0.64  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.44/0.64  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.44/0.64  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.44/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.64  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.44/0.64  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.44/0.64  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.44/0.64  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.44/0.64  thf(t24_funct_2, conjecture,
% 0.44/0.64    (![A:$i,B:$i,C:$i]:
% 0.44/0.64     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.44/0.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.64       ( ![D:$i]:
% 0.44/0.64         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.44/0.64             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.44/0.64           ( ( r2_relset_1 @
% 0.44/0.64               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.44/0.64               ( k6_partfun1 @ B ) ) =>
% 0.44/0.64             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.44/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.64    (~( ![A:$i,B:$i,C:$i]:
% 0.44/0.64        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.44/0.64            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.64          ( ![D:$i]:
% 0.44/0.64            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.44/0.64                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.44/0.64              ( ( r2_relset_1 @
% 0.44/0.64                  B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.44/0.64                  ( k6_partfun1 @ B ) ) =>
% 0.44/0.64                ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ) )),
% 0.44/0.64    inference('cnf.neg', [status(esa)], [t24_funct_2])).
% 0.44/0.64  thf('0', plain,
% 0.44/0.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf(cc2_relset_1, axiom,
% 0.44/0.64    (![A:$i,B:$i,C:$i]:
% 0.44/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.64       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.44/0.64  thf('1', plain,
% 0.44/0.64      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.44/0.64         ((v5_relat_1 @ X14 @ X16)
% 0.44/0.64          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.44/0.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.44/0.64  thf('2', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.44/0.64      inference('sup-', [status(thm)], ['0', '1'])).
% 0.44/0.64  thf(d19_relat_1, axiom,
% 0.44/0.64    (![A:$i,B:$i]:
% 0.44/0.64     ( ( v1_relat_1 @ B ) =>
% 0.44/0.64       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.44/0.64  thf('3', plain,
% 0.44/0.64      (![X5 : $i, X6 : $i]:
% 0.44/0.64         (~ (v5_relat_1 @ X5 @ X6)
% 0.44/0.64          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 0.44/0.64          | ~ (v1_relat_1 @ X5))),
% 0.44/0.64      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.44/0.64  thf('4', plain,
% 0.44/0.64      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.44/0.64      inference('sup-', [status(thm)], ['2', '3'])).
% 0.44/0.64  thf('5', plain,
% 0.44/0.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf(cc1_relset_1, axiom,
% 0.44/0.64    (![A:$i,B:$i,C:$i]:
% 0.44/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.64       ( v1_relat_1 @ C ) ))).
% 0.44/0.64  thf('6', plain,
% 0.44/0.64      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.44/0.64         ((v1_relat_1 @ X11)
% 0.44/0.64          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.44/0.64      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.44/0.64  thf('7', plain, ((v1_relat_1 @ sk_C)),
% 0.44/0.64      inference('sup-', [status(thm)], ['5', '6'])).
% 0.44/0.64  thf('8', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.44/0.64      inference('demod', [status(thm)], ['4', '7'])).
% 0.44/0.64  thf(d8_xboole_0, axiom,
% 0.44/0.64    (![A:$i,B:$i]:
% 0.44/0.64     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.44/0.64       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.44/0.64  thf('9', plain,
% 0.44/0.64      (![X0 : $i, X2 : $i]:
% 0.44/0.64         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.44/0.64      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.44/0.64  thf('10', plain,
% 0.44/0.64      ((((k2_relat_1 @ sk_C) = (sk_B))
% 0.44/0.64        | (r2_xboole_0 @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.44/0.64      inference('sup-', [status(thm)], ['8', '9'])).
% 0.44/0.64  thf('11', plain,
% 0.44/0.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('12', plain,
% 0.44/0.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf(redefinition_k1_partfun1, axiom,
% 0.44/0.64    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.44/0.64     ( ( ( v1_funct_1 @ E ) & 
% 0.44/0.64         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.44/0.64         ( v1_funct_1 @ F ) & 
% 0.44/0.64         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.44/0.64       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.44/0.64  thf('13', plain,
% 0.44/0.64      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.44/0.64          | ~ (v1_funct_1 @ X32)
% 0.44/0.64          | ~ (v1_funct_1 @ X35)
% 0.44/0.64          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.44/0.64          | ((k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35)
% 0.44/0.64              = (k5_relat_1 @ X32 @ X35)))),
% 0.44/0.64      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.44/0.64  thf('14', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.64         (((k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0)
% 0.44/0.64            = (k5_relat_1 @ sk_D @ X0))
% 0.44/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.44/0.64          | ~ (v1_funct_1 @ X0)
% 0.44/0.64          | ~ (v1_funct_1 @ sk_D))),
% 0.44/0.64      inference('sup-', [status(thm)], ['12', '13'])).
% 0.44/0.64  thf('15', plain, ((v1_funct_1 @ sk_D)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('16', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.64         (((k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0)
% 0.44/0.64            = (k5_relat_1 @ sk_D @ X0))
% 0.44/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.44/0.64          | ~ (v1_funct_1 @ X0))),
% 0.44/0.64      inference('demod', [status(thm)], ['14', '15'])).
% 0.44/0.64  thf('17', plain,
% 0.44/0.64      ((~ (v1_funct_1 @ sk_C)
% 0.44/0.64        | ((k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.44/0.64            = (k5_relat_1 @ sk_D @ sk_C)))),
% 0.44/0.64      inference('sup-', [status(thm)], ['11', '16'])).
% 0.44/0.64  thf('18', plain, ((v1_funct_1 @ sk_C)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('19', plain,
% 0.44/0.64      ((r2_relset_1 @ sk_B @ sk_B @ 
% 0.44/0.64        (k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.44/0.64        (k6_partfun1 @ sk_B))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf(redefinition_k6_partfun1, axiom,
% 0.44/0.64    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.44/0.64  thf('20', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 0.44/0.64      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.44/0.64  thf('21', plain,
% 0.44/0.64      ((r2_relset_1 @ sk_B @ sk_B @ 
% 0.44/0.64        (k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.44/0.64        (k6_relat_1 @ sk_B))),
% 0.44/0.64      inference('demod', [status(thm)], ['19', '20'])).
% 0.44/0.64  thf('22', plain,
% 0.44/0.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('23', plain,
% 0.44/0.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf(dt_k1_partfun1, axiom,
% 0.44/0.64    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.44/0.64     ( ( ( v1_funct_1 @ E ) & 
% 0.44/0.64         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.44/0.64         ( v1_funct_1 @ F ) & 
% 0.44/0.64         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.44/0.64       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.44/0.64         ( m1_subset_1 @
% 0.44/0.64           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.44/0.64           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.44/0.64  thf('24', plain,
% 0.44/0.64      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.44/0.64          | ~ (v1_funct_1 @ X24)
% 0.44/0.64          | ~ (v1_funct_1 @ X27)
% 0.44/0.64          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.44/0.64          | (m1_subset_1 @ (k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27) @ 
% 0.44/0.64             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X29))))),
% 0.44/0.64      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.44/0.64  thf('25', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.64         ((m1_subset_1 @ (k1_partfun1 @ sk_B @ sk_A @ X2 @ X0 @ sk_D @ X1) @ 
% 0.44/0.64           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.44/0.64          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.44/0.64          | ~ (v1_funct_1 @ X1)
% 0.44/0.64          | ~ (v1_funct_1 @ sk_D))),
% 0.44/0.64      inference('sup-', [status(thm)], ['23', '24'])).
% 0.44/0.64  thf('26', plain, ((v1_funct_1 @ sk_D)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('27', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.64         ((m1_subset_1 @ (k1_partfun1 @ sk_B @ sk_A @ X2 @ X0 @ sk_D @ X1) @ 
% 0.44/0.64           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.44/0.64          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.44/0.64          | ~ (v1_funct_1 @ X1))),
% 0.44/0.64      inference('demod', [status(thm)], ['25', '26'])).
% 0.44/0.64  thf('28', plain,
% 0.44/0.64      ((~ (v1_funct_1 @ sk_C)
% 0.44/0.64        | (m1_subset_1 @ 
% 0.44/0.64           (k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.44/0.64           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B))))),
% 0.44/0.64      inference('sup-', [status(thm)], ['22', '27'])).
% 0.44/0.64  thf('29', plain, ((v1_funct_1 @ sk_C)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('30', plain,
% 0.44/0.64      ((m1_subset_1 @ 
% 0.44/0.64        (k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.44/0.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B)))),
% 0.44/0.64      inference('demod', [status(thm)], ['28', '29'])).
% 0.44/0.64  thf(redefinition_r2_relset_1, axiom,
% 0.44/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.64     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.44/0.64         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.64       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.44/0.64  thf('31', plain,
% 0.44/0.64      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.44/0.64          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.44/0.64          | ((X20) = (X23))
% 0.44/0.64          | ~ (r2_relset_1 @ X21 @ X22 @ X20 @ X23))),
% 0.44/0.64      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.44/0.64  thf('32', plain,
% 0.44/0.64      (![X0 : $i]:
% 0.44/0.64         (~ (r2_relset_1 @ sk_B @ sk_B @ 
% 0.44/0.64             (k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) @ X0)
% 0.44/0.64          | ((k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) = (X0))
% 0.44/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B))))),
% 0.44/0.64      inference('sup-', [status(thm)], ['30', '31'])).
% 0.44/0.64  thf('33', plain,
% 0.44/0.64      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_B) @ 
% 0.44/0.64           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B)))
% 0.44/0.64        | ((k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.44/0.64            = (k6_relat_1 @ sk_B)))),
% 0.44/0.64      inference('sup-', [status(thm)], ['21', '32'])).
% 0.44/0.64  thf(dt_k6_partfun1, axiom,
% 0.44/0.64    (![A:$i]:
% 0.44/0.64     ( ( m1_subset_1 @
% 0.44/0.64         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.44/0.64       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.44/0.64  thf('34', plain,
% 0.44/0.64      (![X31 : $i]:
% 0.44/0.64         (m1_subset_1 @ (k6_partfun1 @ X31) @ 
% 0.44/0.64          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 0.44/0.64      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.44/0.64  thf('35', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 0.44/0.64      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.44/0.64  thf('36', plain,
% 0.44/0.64      (![X31 : $i]:
% 0.44/0.64         (m1_subset_1 @ (k6_relat_1 @ X31) @ 
% 0.44/0.64          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 0.44/0.64      inference('demod', [status(thm)], ['34', '35'])).
% 0.44/0.64  thf('37', plain,
% 0.44/0.64      (((k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.44/0.64         = (k6_relat_1 @ sk_B))),
% 0.44/0.64      inference('demod', [status(thm)], ['33', '36'])).
% 0.44/0.64  thf('38', plain, (((k6_relat_1 @ sk_B) = (k5_relat_1 @ sk_D @ sk_C))),
% 0.44/0.64      inference('demod', [status(thm)], ['17', '18', '37'])).
% 0.44/0.64  thf(t45_relat_1, axiom,
% 0.44/0.64    (![A:$i]:
% 0.44/0.64     ( ( v1_relat_1 @ A ) =>
% 0.44/0.64       ( ![B:$i]:
% 0.44/0.64         ( ( v1_relat_1 @ B ) =>
% 0.44/0.64           ( r1_tarski @
% 0.44/0.64             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.44/0.64  thf('39', plain,
% 0.44/0.64      (![X7 : $i, X8 : $i]:
% 0.44/0.64         (~ (v1_relat_1 @ X7)
% 0.44/0.64          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X8 @ X7)) @ 
% 0.44/0.64             (k2_relat_1 @ X7))
% 0.44/0.64          | ~ (v1_relat_1 @ X8))),
% 0.44/0.64      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.44/0.64  thf(t60_xboole_1, axiom,
% 0.44/0.64    (![A:$i,B:$i]: ( ~( ( r1_tarski @ A @ B ) & ( r2_xboole_0 @ B @ A ) ) ))).
% 0.44/0.64  thf('40', plain,
% 0.44/0.64      (![X3 : $i, X4 : $i]:
% 0.44/0.64         (~ (r1_tarski @ X3 @ X4) | ~ (r2_xboole_0 @ X4 @ X3))),
% 0.44/0.64      inference('cnf', [status(esa)], [t60_xboole_1])).
% 0.44/0.65  thf('41', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         (~ (v1_relat_1 @ X1)
% 0.44/0.65          | ~ (v1_relat_1 @ X0)
% 0.44/0.65          | ~ (r2_xboole_0 @ (k2_relat_1 @ X0) @ 
% 0.44/0.65               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 0.44/0.65      inference('sup-', [status(thm)], ['39', '40'])).
% 0.44/0.65  thf('42', plain,
% 0.44/0.65      ((~ (r2_xboole_0 @ (k2_relat_1 @ sk_C) @ 
% 0.44/0.65           (k2_relat_1 @ (k6_relat_1 @ sk_B)))
% 0.44/0.65        | ~ (v1_relat_1 @ sk_C)
% 0.44/0.65        | ~ (v1_relat_1 @ sk_D))),
% 0.44/0.65      inference('sup-', [status(thm)], ['38', '41'])).
% 0.44/0.65  thf(t71_relat_1, axiom,
% 0.44/0.65    (![A:$i]:
% 0.44/0.65     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.44/0.65       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.44/0.65  thf('43', plain, (![X10 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 0.44/0.65      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.44/0.65  thf('44', plain, ((v1_relat_1 @ sk_C)),
% 0.44/0.65      inference('sup-', [status(thm)], ['5', '6'])).
% 0.44/0.65  thf('45', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('46', plain,
% 0.44/0.65      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.44/0.65         ((v1_relat_1 @ X11)
% 0.44/0.65          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.44/0.65      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.44/0.65  thf('47', plain, ((v1_relat_1 @ sk_D)),
% 0.44/0.65      inference('sup-', [status(thm)], ['45', '46'])).
% 0.44/0.65  thf('48', plain, (~ (r2_xboole_0 @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.44/0.65      inference('demod', [status(thm)], ['42', '43', '44', '47'])).
% 0.44/0.65  thf('49', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.44/0.65      inference('sup-', [status(thm)], ['10', '48'])).
% 0.44/0.65  thf('50', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('51', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(redefinition_k2_relset_1, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i]:
% 0.44/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.65       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.44/0.65  thf('52', plain,
% 0.44/0.65      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.44/0.65         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.44/0.65          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.44/0.65      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.44/0.65  thf('53', plain,
% 0.44/0.65      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.44/0.65      inference('sup-', [status(thm)], ['51', '52'])).
% 0.44/0.65  thf('54', plain, (((k2_relat_1 @ sk_C) != (sk_B))),
% 0.44/0.65      inference('demod', [status(thm)], ['50', '53'])).
% 0.44/0.65  thf('55', plain, ($false),
% 0.44/0.65      inference('simplify_reflect-', [status(thm)], ['49', '54'])).
% 0.44/0.65  
% 0.44/0.65  % SZS output end Refutation
% 0.44/0.65  
% 0.44/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
