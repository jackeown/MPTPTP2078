%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8s72SGpdwq

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:04 EST 2020

% Result     : Theorem 2.82s
% Output     : Refutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 326 expanded)
%              Number of leaves         :   40 ( 112 expanded)
%              Depth                    :   14
%              Number of atoms          : 1096 (6578 expanded)
%              Number of equality atoms :   34 (  81 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('1',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('3',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','3'])).

thf(t29_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
           => ( ( v2_funct_1 @ C )
              & ( v2_funct_2 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
             => ( ( v2_funct_1 @ C )
                & ( v2_funct_2 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_funct_2])).

thf('5',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('9',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('10',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_funct_2,axiom,(
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

thf('12',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( r2_relset_1 @ X32 @ X32 @ ( k1_partfun1 @ X32 @ X33 @ X33 @ X32 @ X31 @ X34 ) @ ( k6_partfun1 @ X32 ) )
      | ( ( k2_relset_1 @ X33 @ X32 @ X34 )
        = X32 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X33 @ X32 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('13',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('14',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( r2_relset_1 @ X32 @ X32 @ ( k1_partfun1 @ X32 @ X33 @ X33 @ X32 @ X31 @ X34 ) @ ( k6_relat_1 @ X32 ) )
      | ( ( k2_relset_1 @ X33 @ X32 @ X34 )
        = X32 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X33 @ X32 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('22',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['19','22','23','24','25'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('27',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_relat_1 @ X21 )
       != X20 )
      | ( v2_funct_2 @ X21 @ X20 )
      | ~ ( v5_relat_1 @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('28',plain,(
    ! [X21: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v5_relat_1 @ X21 @ ( k2_relat_1 @ X21 ) )
      | ( v2_funct_2 @ X21 @ ( k2_relat_1 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('31',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v5_relat_1 @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('32',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['19','22','23','24','25'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('35',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('36',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['29','32','33','36'])).

thf('38',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('39',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('41',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['7','41'])).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('43',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('45',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('46',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('51',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('58',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( X16 = X19 )
      | ~ ( r2_relset_1 @ X17 @ X18 @ X16 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','59'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('61',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('62',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('63',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
           => ( ( ( C = k1_xboole_0 )
                & ( B != k1_xboole_0 ) )
              | ( v2_funct_1 @ D ) ) ) ) ) )).

thf('66',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X38 @ X36 @ X36 @ X37 @ X39 @ X35 ) )
      | ( v2_funct_1 @ X39 )
      | ( X37 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X38 @ X36 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['64','70'])).

thf('72',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72','73','74','75'])).

thf('77',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['5'])).

thf('78',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['39','40'])).

thf('79',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['77','78'])).

thf('80',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['76','79'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('81',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('82',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['47','80','81'])).

thf('83',plain,(
    $false ),
    inference(demod,[status(thm)],['42','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8s72SGpdwq
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:24:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.82/3.02  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.82/3.02  % Solved by: fo/fo7.sh
% 2.82/3.02  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.82/3.02  % done 2852 iterations in 2.572s
% 2.82/3.02  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.82/3.02  % SZS output start Refutation
% 2.82/3.02  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.82/3.02  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.82/3.02  thf(sk_C_type, type, sk_C: $i).
% 2.82/3.02  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.82/3.02  thf(sk_A_type, type, sk_A: $i).
% 2.82/3.02  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.82/3.02  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.82/3.02  thf(sk_B_type, type, sk_B: $i).
% 2.82/3.02  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.82/3.02  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.82/3.02  thf(sk_D_type, type, sk_D: $i).
% 2.82/3.02  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.82/3.02  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.82/3.02  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.82/3.02  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.82/3.02  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 2.82/3.02  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.82/3.02  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 2.82/3.02  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.82/3.02  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.82/3.02  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.82/3.02  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.82/3.02  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.82/3.02  thf(l13_xboole_0, axiom,
% 2.82/3.02    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 2.82/3.02  thf('0', plain,
% 2.82/3.02      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.82/3.02      inference('cnf', [status(esa)], [l13_xboole_0])).
% 2.82/3.02  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 2.82/3.02  thf('1', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.82/3.02      inference('cnf', [status(esa)], [t81_relat_1])).
% 2.82/3.02  thf(fc4_funct_1, axiom,
% 2.82/3.02    (![A:$i]:
% 2.82/3.02     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 2.82/3.02       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 2.82/3.02  thf('2', plain, (![X6 : $i]: (v2_funct_1 @ (k6_relat_1 @ X6))),
% 2.82/3.02      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.82/3.02  thf('3', plain, ((v2_funct_1 @ k1_xboole_0)),
% 2.82/3.02      inference('sup+', [status(thm)], ['1', '2'])).
% 2.82/3.02  thf('4', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 2.82/3.02      inference('sup+', [status(thm)], ['0', '3'])).
% 2.82/3.02  thf(t29_funct_2, conjecture,
% 2.82/3.02    (![A:$i,B:$i,C:$i]:
% 2.82/3.02     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.82/3.02         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.82/3.02       ( ![D:$i]:
% 2.82/3.02         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.82/3.02             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.82/3.02           ( ( r2_relset_1 @
% 2.82/3.02               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.82/3.02               ( k6_partfun1 @ A ) ) =>
% 2.82/3.02             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 2.82/3.02  thf(zf_stmt_0, negated_conjecture,
% 2.82/3.02    (~( ![A:$i,B:$i,C:$i]:
% 2.82/3.02        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.82/3.02            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.82/3.02          ( ![D:$i]:
% 2.82/3.02            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.82/3.02                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.82/3.02              ( ( r2_relset_1 @
% 2.82/3.02                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.82/3.02                  ( k6_partfun1 @ A ) ) =>
% 2.82/3.02                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 2.82/3.02    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 2.82/3.02  thf('5', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 2.82/3.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.02  thf('6', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.82/3.02      inference('split', [status(esa)], ['5'])).
% 2.82/3.02  thf('7', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.82/3.02      inference('sup-', [status(thm)], ['4', '6'])).
% 2.82/3.02  thf('8', plain,
% 2.82/3.02      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.82/3.02        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.82/3.02        (k6_partfun1 @ sk_A))),
% 2.82/3.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.02  thf(redefinition_k6_partfun1, axiom,
% 2.82/3.02    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.82/3.02  thf('9', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 2.82/3.02      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.82/3.02  thf('10', plain,
% 2.82/3.02      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.82/3.02        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.82/3.02        (k6_relat_1 @ sk_A))),
% 2.82/3.02      inference('demod', [status(thm)], ['8', '9'])).
% 2.82/3.02  thf('11', plain,
% 2.82/3.02      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.82/3.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.02  thf(t24_funct_2, axiom,
% 2.82/3.02    (![A:$i,B:$i,C:$i]:
% 2.82/3.02     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.82/3.02         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.82/3.02       ( ![D:$i]:
% 2.82/3.02         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.82/3.02             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.82/3.02           ( ( r2_relset_1 @
% 2.82/3.02               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 2.82/3.02               ( k6_partfun1 @ B ) ) =>
% 2.82/3.02             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 2.82/3.02  thf('12', plain,
% 2.82/3.02      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 2.82/3.02         (~ (v1_funct_1 @ X31)
% 2.82/3.02          | ~ (v1_funct_2 @ X31 @ X32 @ X33)
% 2.82/3.02          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 2.82/3.02          | ~ (r2_relset_1 @ X32 @ X32 @ 
% 2.82/3.02               (k1_partfun1 @ X32 @ X33 @ X33 @ X32 @ X31 @ X34) @ 
% 2.82/3.02               (k6_partfun1 @ X32))
% 2.82/3.02          | ((k2_relset_1 @ X33 @ X32 @ X34) = (X32))
% 2.82/3.02          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 2.82/3.02          | ~ (v1_funct_2 @ X34 @ X33 @ X32)
% 2.82/3.02          | ~ (v1_funct_1 @ X34))),
% 2.82/3.02      inference('cnf', [status(esa)], [t24_funct_2])).
% 2.82/3.02  thf('13', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 2.82/3.02      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.82/3.02  thf('14', plain,
% 2.82/3.02      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 2.82/3.02         (~ (v1_funct_1 @ X31)
% 2.82/3.02          | ~ (v1_funct_2 @ X31 @ X32 @ X33)
% 2.82/3.02          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 2.82/3.02          | ~ (r2_relset_1 @ X32 @ X32 @ 
% 2.82/3.02               (k1_partfun1 @ X32 @ X33 @ X33 @ X32 @ X31 @ X34) @ 
% 2.82/3.02               (k6_relat_1 @ X32))
% 2.82/3.02          | ((k2_relset_1 @ X33 @ X32 @ X34) = (X32))
% 2.82/3.02          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 2.82/3.02          | ~ (v1_funct_2 @ X34 @ X33 @ X32)
% 2.82/3.02          | ~ (v1_funct_1 @ X34))),
% 2.82/3.02      inference('demod', [status(thm)], ['12', '13'])).
% 2.82/3.02  thf('15', plain,
% 2.82/3.02      (![X0 : $i]:
% 2.82/3.02         (~ (v1_funct_1 @ X0)
% 2.82/3.02          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.82/3.02          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.82/3.02          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.82/3.02          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.82/3.02               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.82/3.02               (k6_relat_1 @ sk_A))
% 2.82/3.02          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.82/3.02          | ~ (v1_funct_1 @ sk_C))),
% 2.82/3.02      inference('sup-', [status(thm)], ['11', '14'])).
% 2.82/3.02  thf('16', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.82/3.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.02  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 2.82/3.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.02  thf('18', plain,
% 2.82/3.02      (![X0 : $i]:
% 2.82/3.02         (~ (v1_funct_1 @ X0)
% 2.82/3.02          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.82/3.02          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.82/3.02          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.82/3.02          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.82/3.02               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.82/3.02               (k6_relat_1 @ sk_A)))),
% 2.82/3.02      inference('demod', [status(thm)], ['15', '16', '17'])).
% 2.82/3.02  thf('19', plain,
% 2.82/3.02      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 2.82/3.02        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.82/3.02        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.82/3.02        | ~ (v1_funct_1 @ sk_D))),
% 2.82/3.02      inference('sup-', [status(thm)], ['10', '18'])).
% 2.82/3.02  thf('20', plain,
% 2.82/3.02      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.82/3.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.02  thf(redefinition_k2_relset_1, axiom,
% 2.82/3.02    (![A:$i,B:$i,C:$i]:
% 2.82/3.02     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.82/3.02       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.82/3.02  thf('21', plain,
% 2.82/3.02      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.82/3.02         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 2.82/3.02          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 2.82/3.02      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.82/3.02  thf('22', plain,
% 2.82/3.02      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.82/3.02      inference('sup-', [status(thm)], ['20', '21'])).
% 2.82/3.02  thf('23', plain,
% 2.82/3.02      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.82/3.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.02  thf('24', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.82/3.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.02  thf('25', plain, ((v1_funct_1 @ sk_D)),
% 2.82/3.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.02  thf('26', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.82/3.02      inference('demod', [status(thm)], ['19', '22', '23', '24', '25'])).
% 2.82/3.02  thf(d3_funct_2, axiom,
% 2.82/3.02    (![A:$i,B:$i]:
% 2.82/3.02     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 2.82/3.02       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 2.82/3.02  thf('27', plain,
% 2.82/3.02      (![X20 : $i, X21 : $i]:
% 2.82/3.02         (((k2_relat_1 @ X21) != (X20))
% 2.82/3.02          | (v2_funct_2 @ X21 @ X20)
% 2.82/3.02          | ~ (v5_relat_1 @ X21 @ X20)
% 2.82/3.02          | ~ (v1_relat_1 @ X21))),
% 2.82/3.02      inference('cnf', [status(esa)], [d3_funct_2])).
% 2.82/3.02  thf('28', plain,
% 2.82/3.02      (![X21 : $i]:
% 2.82/3.02         (~ (v1_relat_1 @ X21)
% 2.82/3.02          | ~ (v5_relat_1 @ X21 @ (k2_relat_1 @ X21))
% 2.82/3.02          | (v2_funct_2 @ X21 @ (k2_relat_1 @ X21)))),
% 2.82/3.02      inference('simplify', [status(thm)], ['27'])).
% 2.82/3.02  thf('29', plain,
% 2.82/3.02      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 2.82/3.02        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 2.82/3.02        | ~ (v1_relat_1 @ sk_D))),
% 2.82/3.02      inference('sup-', [status(thm)], ['26', '28'])).
% 2.82/3.02  thf('30', plain,
% 2.82/3.02      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.82/3.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.02  thf(cc2_relset_1, axiom,
% 2.82/3.02    (![A:$i,B:$i,C:$i]:
% 2.82/3.02     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.82/3.03       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.82/3.03  thf('31', plain,
% 2.82/3.03      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.82/3.03         ((v5_relat_1 @ X10 @ X12)
% 2.82/3.03          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 2.82/3.03      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.82/3.03  thf('32', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 2.82/3.03      inference('sup-', [status(thm)], ['30', '31'])).
% 2.82/3.03  thf('33', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.82/3.03      inference('demod', [status(thm)], ['19', '22', '23', '24', '25'])).
% 2.82/3.03  thf('34', plain,
% 2.82/3.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf(cc1_relset_1, axiom,
% 2.82/3.03    (![A:$i,B:$i,C:$i]:
% 2.82/3.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.82/3.03       ( v1_relat_1 @ C ) ))).
% 2.82/3.03  thf('35', plain,
% 2.82/3.03      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.82/3.03         ((v1_relat_1 @ X7)
% 2.82/3.03          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 2.82/3.03      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.82/3.03  thf('36', plain, ((v1_relat_1 @ sk_D)),
% 2.82/3.03      inference('sup-', [status(thm)], ['34', '35'])).
% 2.82/3.03  thf('37', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 2.82/3.03      inference('demod', [status(thm)], ['29', '32', '33', '36'])).
% 2.82/3.03  thf('38', plain,
% 2.82/3.03      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 2.82/3.03      inference('split', [status(esa)], ['5'])).
% 2.82/3.03  thf('39', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 2.82/3.03      inference('sup-', [status(thm)], ['37', '38'])).
% 2.82/3.03  thf('40', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 2.82/3.03      inference('split', [status(esa)], ['5'])).
% 2.82/3.03  thf('41', plain, (~ ((v2_funct_1 @ sk_C))),
% 2.82/3.03      inference('sat_resolution*', [status(thm)], ['39', '40'])).
% 2.82/3.03  thf('42', plain, (~ (v1_xboole_0 @ sk_C)),
% 2.82/3.03      inference('simpl_trail', [status(thm)], ['7', '41'])).
% 2.82/3.03  thf(fc4_zfmisc_1, axiom,
% 2.82/3.03    (![A:$i,B:$i]:
% 2.82/3.03     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 2.82/3.03  thf('43', plain,
% 2.82/3.03      (![X1 : $i, X2 : $i]:
% 2.82/3.03         (~ (v1_xboole_0 @ X1) | (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X2)))),
% 2.82/3.03      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 2.82/3.03  thf('44', plain,
% 2.82/3.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf(cc1_subset_1, axiom,
% 2.82/3.03    (![A:$i]:
% 2.82/3.03     ( ( v1_xboole_0 @ A ) =>
% 2.82/3.03       ( ![B:$i]:
% 2.82/3.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 2.82/3.03  thf('45', plain,
% 2.82/3.03      (![X3 : $i, X4 : $i]:
% 2.82/3.03         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 2.82/3.03          | (v1_xboole_0 @ X3)
% 2.82/3.03          | ~ (v1_xboole_0 @ X4))),
% 2.82/3.03      inference('cnf', [status(esa)], [cc1_subset_1])).
% 2.82/3.03  thf('46', plain,
% 2.82/3.03      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 2.82/3.03      inference('sup-', [status(thm)], ['44', '45'])).
% 2.82/3.03  thf('47', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C))),
% 2.82/3.03      inference('sup-', [status(thm)], ['43', '46'])).
% 2.82/3.03  thf('48', plain,
% 2.82/3.03      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.82/3.03        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.82/3.03        (k6_relat_1 @ sk_A))),
% 2.82/3.03      inference('demod', [status(thm)], ['8', '9'])).
% 2.82/3.03  thf('49', plain,
% 2.82/3.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('50', plain,
% 2.82/3.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf(dt_k1_partfun1, axiom,
% 2.82/3.03    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.82/3.03     ( ( ( v1_funct_1 @ E ) & 
% 2.82/3.03         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.82/3.03         ( v1_funct_1 @ F ) & 
% 2.82/3.03         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.82/3.03       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.82/3.03         ( m1_subset_1 @
% 2.82/3.03           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.82/3.03           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.82/3.03  thf('51', plain,
% 2.82/3.03      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 2.82/3.03         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 2.82/3.03          | ~ (v1_funct_1 @ X22)
% 2.82/3.03          | ~ (v1_funct_1 @ X25)
% 2.82/3.03          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 2.82/3.03          | (m1_subset_1 @ (k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25) @ 
% 2.82/3.03             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X27))))),
% 2.82/3.03      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.82/3.03  thf('52', plain,
% 2.82/3.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.82/3.03         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.82/3.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.82/3.03          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.82/3.03          | ~ (v1_funct_1 @ X1)
% 2.82/3.03          | ~ (v1_funct_1 @ sk_C))),
% 2.82/3.03      inference('sup-', [status(thm)], ['50', '51'])).
% 2.82/3.03  thf('53', plain, ((v1_funct_1 @ sk_C)),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('54', plain,
% 2.82/3.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.82/3.03         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.82/3.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.82/3.03          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.82/3.03          | ~ (v1_funct_1 @ X1))),
% 2.82/3.03      inference('demod', [status(thm)], ['52', '53'])).
% 2.82/3.03  thf('55', plain,
% 2.82/3.03      ((~ (v1_funct_1 @ sk_D)
% 2.82/3.03        | (m1_subset_1 @ 
% 2.82/3.03           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.82/3.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.82/3.03      inference('sup-', [status(thm)], ['49', '54'])).
% 2.82/3.03  thf('56', plain, ((v1_funct_1 @ sk_D)),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('57', plain,
% 2.82/3.03      ((m1_subset_1 @ 
% 2.82/3.03        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.82/3.03        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.82/3.03      inference('demod', [status(thm)], ['55', '56'])).
% 2.82/3.03  thf(redefinition_r2_relset_1, axiom,
% 2.82/3.03    (![A:$i,B:$i,C:$i,D:$i]:
% 2.82/3.03     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.82/3.03         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.82/3.03       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.82/3.03  thf('58', plain,
% 2.82/3.03      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 2.82/3.03         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 2.82/3.03          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 2.82/3.03          | ((X16) = (X19))
% 2.82/3.03          | ~ (r2_relset_1 @ X17 @ X18 @ X16 @ X19))),
% 2.82/3.03      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.82/3.03  thf('59', plain,
% 2.82/3.03      (![X0 : $i]:
% 2.82/3.03         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.82/3.03             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 2.82/3.03          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 2.82/3.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.82/3.03      inference('sup-', [status(thm)], ['57', '58'])).
% 2.82/3.03  thf('60', plain,
% 2.82/3.03      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 2.82/3.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.82/3.03        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.82/3.03            = (k6_relat_1 @ sk_A)))),
% 2.82/3.03      inference('sup-', [status(thm)], ['48', '59'])).
% 2.82/3.03  thf(dt_k6_partfun1, axiom,
% 2.82/3.03    (![A:$i]:
% 2.82/3.03     ( ( m1_subset_1 @
% 2.82/3.03         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 2.82/3.03       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 2.82/3.03  thf('61', plain,
% 2.82/3.03      (![X29 : $i]:
% 2.82/3.03         (m1_subset_1 @ (k6_partfun1 @ X29) @ 
% 2.82/3.03          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 2.82/3.03      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 2.82/3.03  thf('62', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 2.82/3.03      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.82/3.03  thf('63', plain,
% 2.82/3.03      (![X29 : $i]:
% 2.82/3.03         (m1_subset_1 @ (k6_relat_1 @ X29) @ 
% 2.82/3.03          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 2.82/3.03      inference('demod', [status(thm)], ['61', '62'])).
% 2.82/3.03  thf('64', plain,
% 2.82/3.03      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.82/3.03         = (k6_relat_1 @ sk_A))),
% 2.82/3.03      inference('demod', [status(thm)], ['60', '63'])).
% 2.82/3.03  thf('65', plain,
% 2.82/3.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf(t26_funct_2, axiom,
% 2.82/3.03    (![A:$i,B:$i,C:$i,D:$i]:
% 2.82/3.03     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.82/3.03         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.82/3.03       ( ![E:$i]:
% 2.82/3.03         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.82/3.03             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.82/3.03           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 2.82/3.03             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 2.82/3.03               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 2.82/3.03  thf('66', plain,
% 2.82/3.03      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 2.82/3.03         (~ (v1_funct_1 @ X35)
% 2.82/3.03          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 2.82/3.03          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 2.82/3.03          | ~ (v2_funct_1 @ (k1_partfun1 @ X38 @ X36 @ X36 @ X37 @ X39 @ X35))
% 2.82/3.03          | (v2_funct_1 @ X39)
% 2.82/3.03          | ((X37) = (k1_xboole_0))
% 2.82/3.03          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X36)))
% 2.82/3.03          | ~ (v1_funct_2 @ X39 @ X38 @ X36)
% 2.82/3.03          | ~ (v1_funct_1 @ X39))),
% 2.82/3.03      inference('cnf', [status(esa)], [t26_funct_2])).
% 2.82/3.03  thf('67', plain,
% 2.82/3.03      (![X0 : $i, X1 : $i]:
% 2.82/3.03         (~ (v1_funct_1 @ X0)
% 2.82/3.03          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.82/3.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.82/3.03          | ((sk_A) = (k1_xboole_0))
% 2.82/3.03          | (v2_funct_1 @ X0)
% 2.82/3.03          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 2.82/3.03          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.82/3.03          | ~ (v1_funct_1 @ sk_D))),
% 2.82/3.03      inference('sup-', [status(thm)], ['65', '66'])).
% 2.82/3.03  thf('68', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('69', plain, ((v1_funct_1 @ sk_D)),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('70', plain,
% 2.82/3.03      (![X0 : $i, X1 : $i]:
% 2.82/3.03         (~ (v1_funct_1 @ X0)
% 2.82/3.03          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.82/3.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.82/3.03          | ((sk_A) = (k1_xboole_0))
% 2.82/3.03          | (v2_funct_1 @ X0)
% 2.82/3.03          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 2.82/3.03      inference('demod', [status(thm)], ['67', '68', '69'])).
% 2.82/3.03  thf('71', plain,
% 2.82/3.03      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 2.82/3.03        | (v2_funct_1 @ sk_C)
% 2.82/3.03        | ((sk_A) = (k1_xboole_0))
% 2.82/3.03        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 2.82/3.03        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.82/3.03        | ~ (v1_funct_1 @ sk_C))),
% 2.82/3.03      inference('sup-', [status(thm)], ['64', '70'])).
% 2.82/3.03  thf('72', plain, (![X6 : $i]: (v2_funct_1 @ (k6_relat_1 @ X6))),
% 2.82/3.03      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.82/3.03  thf('73', plain,
% 2.82/3.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('74', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('75', plain, ((v1_funct_1 @ sk_C)),
% 2.82/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.03  thf('76', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 2.82/3.03      inference('demod', [status(thm)], ['71', '72', '73', '74', '75'])).
% 2.82/3.03  thf('77', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.82/3.03      inference('split', [status(esa)], ['5'])).
% 2.82/3.03  thf('78', plain, (~ ((v2_funct_1 @ sk_C))),
% 2.82/3.03      inference('sat_resolution*', [status(thm)], ['39', '40'])).
% 2.82/3.03  thf('79', plain, (~ (v2_funct_1 @ sk_C)),
% 2.82/3.03      inference('simpl_trail', [status(thm)], ['77', '78'])).
% 2.82/3.03  thf('80', plain, (((sk_A) = (k1_xboole_0))),
% 2.82/3.03      inference('clc', [status(thm)], ['76', '79'])).
% 2.82/3.03  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.82/3.03  thf('81', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.82/3.03      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.82/3.03  thf('82', plain, ((v1_xboole_0 @ sk_C)),
% 2.82/3.03      inference('demod', [status(thm)], ['47', '80', '81'])).
% 2.82/3.03  thf('83', plain, ($false), inference('demod', [status(thm)], ['42', '82'])).
% 2.82/3.03  
% 2.82/3.03  % SZS output end Refutation
% 2.82/3.03  
% 2.82/3.03  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
