%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JML8gP7sI3

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:51 EST 2020

% Result     : Theorem 0.56s
% Output     : Refutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 289 expanded)
%              Number of leaves         :   29 (  99 expanded)
%              Depth                    :   12
%              Number of atoms          :  893 (5430 expanded)
%              Number of equality atoms :   29 (  56 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t33_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ~ ( v1_xboole_0 @ C )
         => ! [D: $i] :
              ( ( ( v1_funct_1 @ D )
                & ( v1_funct_2 @ D @ A @ B )
                & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
             => ! [E: $i] :
                  ( ( ( v1_funct_1 @ E )
                    & ( v1_funct_2 @ E @ B @ C )
                    & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
                 => ( ( ( v2_funct_2 @ D @ B )
                      & ( v2_funct_2 @ E @ C ) )
                   => ( v2_funct_2 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ~ ( v1_xboole_0 @ B )
       => ! [C: $i] :
            ( ~ ( v1_xboole_0 @ C )
           => ! [D: $i] :
                ( ( ( v1_funct_1 @ D )
                  & ( v1_funct_2 @ D @ A @ B )
                  & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
               => ! [E: $i] :
                    ( ( ( v1_funct_1 @ E )
                      & ( v1_funct_2 @ E @ B @ C )
                      & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
                   => ( ( ( v2_funct_2 @ D @ B )
                        & ( v2_funct_2 @ E @ C ) )
                     => ( v2_funct_2 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_funct_2])).

thf('0',plain,(
    ~ ( v2_funct_2 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('3',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 )
        = ( k5_relat_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v2_funct_2 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','9'])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) )
        = ( k9_relat_1 @ X11 @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('12',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v4_relat_1 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('14',plain,(
    v4_relat_1 @ sk_E @ sk_B ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13
        = ( k7_relat_1 @ X13 @ X14 ) )
      | ~ ( v4_relat_1 @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( sk_E
      = ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('18',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('19',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( sk_E
    = ( k7_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['16','19'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('22',plain,
    ( ( ( k2_relat_1 @ sk_E )
      = ( k9_relat_1 @ sk_E @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    v2_funct_2 @ sk_E @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('24',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v2_funct_2 @ X22 @ X21 )
      | ( ( k2_relat_1 @ X22 )
        = X21 )
      | ~ ( v5_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v5_relat_1 @ sk_E @ sk_C )
    | ( ( k2_relat_1 @ sk_E )
      = sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['17','18'])).

thf('27',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v5_relat_1 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('29',plain,(
    v5_relat_1 @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k2_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['25','26','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['17','18'])).

thf('32',plain,
    ( sk_C
    = ( k9_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['22','30','31'])).

thf('33',plain,(
    v2_funct_2 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v2_funct_2 @ X22 @ X21 )
      | ( ( k2_relat_1 @ X22 )
        = X21 )
      | ~ ( v5_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v5_relat_1 @ sk_D @ sk_B )
    | ( ( k2_relat_1 @ sk_D )
      = sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('38',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v5_relat_1 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('41',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_B ),
    inference(demod,[status(thm)],['35','38','41'])).

thf('43',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) )
        = ( k9_relat_1 @ X11 @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('44',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_relat_1 @ X22 )
       != X21 )
      | ( v2_funct_2 @ X22 @ X21 )
      | ~ ( v5_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('45',plain,(
    ! [X22: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v5_relat_1 @ X22 @ ( k2_relat_1 @ X22 ) )
      | ( v2_funct_2 @ X22 @ ( k2_relat_1 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v5_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v2_funct_2 @ ( k5_relat_1 @ X0 @ X1 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ ( k5_relat_1 @ sk_D @ X0 ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_D @ X0 ) )
      | ( v2_funct_2 @ ( k5_relat_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['42','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['36','37'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ ( k5_relat_1 @ sk_D @ X0 ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_D @ X0 ) )
      | ( v2_funct_2 @ ( k5_relat_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( v5_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_C )
    | ~ ( v1_relat_1 @ sk_E )
    | ( v2_funct_2 @ ( k5_relat_1 @ sk_D @ sk_E ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['32','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('53',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v5_relat_1 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('61',plain,(
    v5_relat_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ sk_C ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('63',plain,(
    v5_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['17','18'])).

thf('65',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('66',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('67',plain,(
    v1_relat_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('69',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    v2_funct_2 @ ( k5_relat_1 @ sk_D @ sk_E ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference(demod,[status(thm)],['50','63','64','69'])).

thf('71',plain,
    ( ( v2_funct_2 @ ( k5_relat_1 @ sk_D @ sk_E ) @ ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['11','70'])).

thf('72',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_B ),
    inference(demod,[status(thm)],['35','38','41'])).

thf('73',plain,
    ( sk_C
    = ( k9_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['22','30','31'])).

thf('74',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['36','37'])).

thf('75',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['17','18'])).

thf('76',plain,(
    v2_funct_2 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['71','72','73','74','75'])).

thf('77',plain,(
    $false ),
    inference(demod,[status(thm)],['10','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JML8gP7sI3
% 0.15/0.34  % Computer   : n025.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 13:49:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.56/0.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.56/0.72  % Solved by: fo/fo7.sh
% 0.56/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.56/0.72  % done 333 iterations in 0.263s
% 0.56/0.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.56/0.72  % SZS output start Refutation
% 0.56/0.72  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.56/0.72  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.56/0.72  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.56/0.72  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.56/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.56/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.56/0.72  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.56/0.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.56/0.72  thf(sk_D_type, type, sk_D: $i).
% 0.56/0.72  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.56/0.72  thf(sk_E_type, type, sk_E: $i).
% 0.56/0.72  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.56/0.72  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.56/0.72  thf(sk_C_type, type, sk_C: $i).
% 0.56/0.72  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.56/0.72  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.56/0.72  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.56/0.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.56/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.56/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.56/0.72  thf(t33_funct_2, conjecture,
% 0.56/0.72    (![A:$i,B:$i]:
% 0.56/0.72     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.56/0.72       ( ![C:$i]:
% 0.56/0.72         ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.56/0.72           ( ![D:$i]:
% 0.56/0.72             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.56/0.72                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.56/0.72               ( ![E:$i]:
% 0.56/0.72                 ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.56/0.72                     ( m1_subset_1 @
% 0.56/0.72                       E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.56/0.72                   ( ( ( v2_funct_2 @ D @ B ) & ( v2_funct_2 @ E @ C ) ) =>
% 0.56/0.72                     ( v2_funct_2 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) @ C ) ) ) ) ) ) ) ) ))).
% 0.56/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.56/0.72    (~( ![A:$i,B:$i]:
% 0.56/0.72        ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.56/0.72          ( ![C:$i]:
% 0.56/0.72            ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.56/0.72              ( ![D:$i]:
% 0.56/0.72                ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.56/0.72                    ( m1_subset_1 @
% 0.56/0.72                      D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.56/0.72                  ( ![E:$i]:
% 0.56/0.72                    ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.56/0.72                        ( m1_subset_1 @
% 0.56/0.72                          E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.56/0.72                      ( ( ( v2_funct_2 @ D @ B ) & ( v2_funct_2 @ E @ C ) ) =>
% 0.56/0.72                        ( v2_funct_2 @
% 0.56/0.72                          ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.56/0.72    inference('cnf.neg', [status(esa)], [t33_funct_2])).
% 0.56/0.72  thf('0', plain,
% 0.56/0.72      (~ (v2_funct_2 @ 
% 0.56/0.72          (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ sk_C)),
% 0.56/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.72  thf('1', plain,
% 0.56/0.72      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.56/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.72  thf('2', plain,
% 0.56/0.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.56/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.72  thf(redefinition_k1_partfun1, axiom,
% 0.56/0.72    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.56/0.72     ( ( ( v1_funct_1 @ E ) & 
% 0.56/0.72         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.56/0.72         ( v1_funct_1 @ F ) & 
% 0.56/0.72         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.56/0.72       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.56/0.72  thf('3', plain,
% 0.56/0.72      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.56/0.72         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.56/0.72          | ~ (v1_funct_1 @ X29)
% 0.56/0.72          | ~ (v1_funct_1 @ X32)
% 0.56/0.72          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.56/0.72          | ((k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32)
% 0.56/0.72              = (k5_relat_1 @ X29 @ X32)))),
% 0.56/0.72      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.56/0.72  thf('4', plain,
% 0.56/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.72         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 0.56/0.72            = (k5_relat_1 @ sk_D @ X0))
% 0.56/0.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.56/0.72          | ~ (v1_funct_1 @ X0)
% 0.56/0.72          | ~ (v1_funct_1 @ sk_D))),
% 0.56/0.72      inference('sup-', [status(thm)], ['2', '3'])).
% 0.56/0.72  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 0.56/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.72  thf('6', plain,
% 0.56/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.72         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 0.56/0.72            = (k5_relat_1 @ sk_D @ X0))
% 0.56/0.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.56/0.72          | ~ (v1_funct_1 @ X0))),
% 0.56/0.72      inference('demod', [status(thm)], ['4', '5'])).
% 0.56/0.72  thf('7', plain,
% 0.56/0.72      ((~ (v1_funct_1 @ sk_E)
% 0.56/0.72        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.56/0.72            = (k5_relat_1 @ sk_D @ sk_E)))),
% 0.56/0.72      inference('sup-', [status(thm)], ['1', '6'])).
% 0.56/0.72  thf('8', plain, ((v1_funct_1 @ sk_E)),
% 0.56/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.72  thf('9', plain,
% 0.56/0.72      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.56/0.72         = (k5_relat_1 @ sk_D @ sk_E))),
% 0.56/0.72      inference('demod', [status(thm)], ['7', '8'])).
% 0.56/0.72  thf('10', plain, (~ (v2_funct_2 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_C)),
% 0.56/0.72      inference('demod', [status(thm)], ['0', '9'])).
% 0.56/0.72  thf(t160_relat_1, axiom,
% 0.56/0.72    (![A:$i]:
% 0.56/0.72     ( ( v1_relat_1 @ A ) =>
% 0.56/0.72       ( ![B:$i]:
% 0.56/0.72         ( ( v1_relat_1 @ B ) =>
% 0.56/0.72           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.56/0.72             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.56/0.72  thf('11', plain,
% 0.56/0.72      (![X11 : $i, X12 : $i]:
% 0.56/0.72         (~ (v1_relat_1 @ X11)
% 0.56/0.72          | ((k2_relat_1 @ (k5_relat_1 @ X12 @ X11))
% 0.56/0.72              = (k9_relat_1 @ X11 @ (k2_relat_1 @ X12)))
% 0.56/0.72          | ~ (v1_relat_1 @ X12))),
% 0.56/0.72      inference('cnf', [status(esa)], [t160_relat_1])).
% 0.56/0.72  thf('12', plain,
% 0.56/0.72      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.56/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.72  thf(cc2_relset_1, axiom,
% 0.56/0.72    (![A:$i,B:$i,C:$i]:
% 0.56/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.56/0.72       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.56/0.72  thf('13', plain,
% 0.56/0.72      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.56/0.72         ((v4_relat_1 @ X18 @ X19)
% 0.56/0.72          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.56/0.72      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.56/0.72  thf('14', plain, ((v4_relat_1 @ sk_E @ sk_B)),
% 0.56/0.72      inference('sup-', [status(thm)], ['12', '13'])).
% 0.56/0.72  thf(t209_relat_1, axiom,
% 0.56/0.72    (![A:$i,B:$i]:
% 0.56/0.72     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.56/0.72       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.56/0.72  thf('15', plain,
% 0.56/0.72      (![X13 : $i, X14 : $i]:
% 0.56/0.72         (((X13) = (k7_relat_1 @ X13 @ X14))
% 0.56/0.72          | ~ (v4_relat_1 @ X13 @ X14)
% 0.56/0.72          | ~ (v1_relat_1 @ X13))),
% 0.56/0.72      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.56/0.72  thf('16', plain,
% 0.56/0.72      ((~ (v1_relat_1 @ sk_E) | ((sk_E) = (k7_relat_1 @ sk_E @ sk_B)))),
% 0.56/0.72      inference('sup-', [status(thm)], ['14', '15'])).
% 0.56/0.72  thf('17', plain,
% 0.56/0.72      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.56/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.72  thf(cc1_relset_1, axiom,
% 0.56/0.72    (![A:$i,B:$i,C:$i]:
% 0.56/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.56/0.72       ( v1_relat_1 @ C ) ))).
% 0.56/0.72  thf('18', plain,
% 0.56/0.72      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.56/0.72         ((v1_relat_1 @ X15)
% 0.56/0.72          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.56/0.72      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.56/0.72  thf('19', plain, ((v1_relat_1 @ sk_E)),
% 0.56/0.72      inference('sup-', [status(thm)], ['17', '18'])).
% 0.56/0.72  thf('20', plain, (((sk_E) = (k7_relat_1 @ sk_E @ sk_B))),
% 0.56/0.72      inference('demod', [status(thm)], ['16', '19'])).
% 0.56/0.72  thf(t148_relat_1, axiom,
% 0.56/0.72    (![A:$i,B:$i]:
% 0.56/0.72     ( ( v1_relat_1 @ B ) =>
% 0.56/0.72       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.56/0.72  thf('21', plain,
% 0.56/0.72      (![X9 : $i, X10 : $i]:
% 0.56/0.72         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 0.56/0.72          | ~ (v1_relat_1 @ X9))),
% 0.56/0.72      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.56/0.72  thf('22', plain,
% 0.56/0.72      ((((k2_relat_1 @ sk_E) = (k9_relat_1 @ sk_E @ sk_B))
% 0.56/0.72        | ~ (v1_relat_1 @ sk_E))),
% 0.56/0.72      inference('sup+', [status(thm)], ['20', '21'])).
% 0.56/0.72  thf('23', plain, ((v2_funct_2 @ sk_E @ sk_C)),
% 0.56/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.72  thf(d3_funct_2, axiom,
% 0.56/0.72    (![A:$i,B:$i]:
% 0.56/0.72     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.56/0.72       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.56/0.72  thf('24', plain,
% 0.56/0.72      (![X21 : $i, X22 : $i]:
% 0.56/0.72         (~ (v2_funct_2 @ X22 @ X21)
% 0.56/0.72          | ((k2_relat_1 @ X22) = (X21))
% 0.56/0.72          | ~ (v5_relat_1 @ X22 @ X21)
% 0.56/0.72          | ~ (v1_relat_1 @ X22))),
% 0.56/0.72      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.56/0.72  thf('25', plain,
% 0.56/0.72      ((~ (v1_relat_1 @ sk_E)
% 0.56/0.72        | ~ (v5_relat_1 @ sk_E @ sk_C)
% 0.56/0.72        | ((k2_relat_1 @ sk_E) = (sk_C)))),
% 0.56/0.72      inference('sup-', [status(thm)], ['23', '24'])).
% 0.56/0.72  thf('26', plain, ((v1_relat_1 @ sk_E)),
% 0.56/0.72      inference('sup-', [status(thm)], ['17', '18'])).
% 0.56/0.72  thf('27', plain,
% 0.56/0.72      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.56/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.72  thf('28', plain,
% 0.56/0.72      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.56/0.72         ((v5_relat_1 @ X18 @ X20)
% 0.56/0.72          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.56/0.72      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.56/0.72  thf('29', plain, ((v5_relat_1 @ sk_E @ sk_C)),
% 0.56/0.72      inference('sup-', [status(thm)], ['27', '28'])).
% 0.56/0.72  thf('30', plain, (((k2_relat_1 @ sk_E) = (sk_C))),
% 0.56/0.72      inference('demod', [status(thm)], ['25', '26', '29'])).
% 0.56/0.72  thf('31', plain, ((v1_relat_1 @ sk_E)),
% 0.56/0.72      inference('sup-', [status(thm)], ['17', '18'])).
% 0.56/0.72  thf('32', plain, (((sk_C) = (k9_relat_1 @ sk_E @ sk_B))),
% 0.56/0.72      inference('demod', [status(thm)], ['22', '30', '31'])).
% 0.56/0.72  thf('33', plain, ((v2_funct_2 @ sk_D @ sk_B)),
% 0.56/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.72  thf('34', plain,
% 0.56/0.72      (![X21 : $i, X22 : $i]:
% 0.56/0.72         (~ (v2_funct_2 @ X22 @ X21)
% 0.56/0.72          | ((k2_relat_1 @ X22) = (X21))
% 0.56/0.72          | ~ (v5_relat_1 @ X22 @ X21)
% 0.56/0.72          | ~ (v1_relat_1 @ X22))),
% 0.56/0.72      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.56/0.72  thf('35', plain,
% 0.56/0.72      ((~ (v1_relat_1 @ sk_D)
% 0.56/0.72        | ~ (v5_relat_1 @ sk_D @ sk_B)
% 0.56/0.72        | ((k2_relat_1 @ sk_D) = (sk_B)))),
% 0.56/0.72      inference('sup-', [status(thm)], ['33', '34'])).
% 0.56/0.72  thf('36', plain,
% 0.56/0.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.56/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.72  thf('37', plain,
% 0.56/0.72      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.56/0.72         ((v1_relat_1 @ X15)
% 0.56/0.72          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.56/0.72      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.56/0.72  thf('38', plain, ((v1_relat_1 @ sk_D)),
% 0.56/0.72      inference('sup-', [status(thm)], ['36', '37'])).
% 0.56/0.72  thf('39', plain,
% 0.56/0.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.56/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.72  thf('40', plain,
% 0.56/0.72      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.56/0.72         ((v5_relat_1 @ X18 @ X20)
% 0.56/0.72          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.56/0.72      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.56/0.72  thf('41', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 0.56/0.72      inference('sup-', [status(thm)], ['39', '40'])).
% 0.56/0.72  thf('42', plain, (((k2_relat_1 @ sk_D) = (sk_B))),
% 0.56/0.72      inference('demod', [status(thm)], ['35', '38', '41'])).
% 0.56/0.72  thf('43', plain,
% 0.56/0.72      (![X11 : $i, X12 : $i]:
% 0.56/0.72         (~ (v1_relat_1 @ X11)
% 0.56/0.72          | ((k2_relat_1 @ (k5_relat_1 @ X12 @ X11))
% 0.56/0.72              = (k9_relat_1 @ X11 @ (k2_relat_1 @ X12)))
% 0.56/0.72          | ~ (v1_relat_1 @ X12))),
% 0.56/0.72      inference('cnf', [status(esa)], [t160_relat_1])).
% 0.56/0.72  thf('44', plain,
% 0.56/0.72      (![X21 : $i, X22 : $i]:
% 0.56/0.72         (((k2_relat_1 @ X22) != (X21))
% 0.56/0.72          | (v2_funct_2 @ X22 @ X21)
% 0.56/0.72          | ~ (v5_relat_1 @ X22 @ X21)
% 0.56/0.72          | ~ (v1_relat_1 @ X22))),
% 0.56/0.72      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.56/0.72  thf('45', plain,
% 0.56/0.72      (![X22 : $i]:
% 0.56/0.72         (~ (v1_relat_1 @ X22)
% 0.56/0.72          | ~ (v5_relat_1 @ X22 @ (k2_relat_1 @ X22))
% 0.56/0.72          | (v2_funct_2 @ X22 @ (k2_relat_1 @ X22)))),
% 0.56/0.72      inference('simplify', [status(thm)], ['44'])).
% 0.56/0.72  thf('46', plain,
% 0.56/0.72      (![X0 : $i, X1 : $i]:
% 0.56/0.72         (~ (v5_relat_1 @ (k5_relat_1 @ X0 @ X1) @ 
% 0.56/0.72             (k9_relat_1 @ X1 @ (k2_relat_1 @ X0)))
% 0.56/0.72          | ~ (v1_relat_1 @ X0)
% 0.56/0.72          | ~ (v1_relat_1 @ X1)
% 0.56/0.72          | (v2_funct_2 @ (k5_relat_1 @ X0 @ X1) @ 
% 0.56/0.72             (k2_relat_1 @ (k5_relat_1 @ X0 @ X1)))
% 0.56/0.72          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 0.56/0.72      inference('sup-', [status(thm)], ['43', '45'])).
% 0.56/0.72  thf('47', plain,
% 0.56/0.72      (![X0 : $i]:
% 0.56/0.72         (~ (v5_relat_1 @ (k5_relat_1 @ sk_D @ X0) @ (k9_relat_1 @ X0 @ sk_B))
% 0.56/0.72          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_D @ X0))
% 0.56/0.72          | (v2_funct_2 @ (k5_relat_1 @ sk_D @ X0) @ 
% 0.56/0.72             (k2_relat_1 @ (k5_relat_1 @ sk_D @ X0)))
% 0.56/0.72          | ~ (v1_relat_1 @ X0)
% 0.56/0.72          | ~ (v1_relat_1 @ sk_D))),
% 0.56/0.72      inference('sup-', [status(thm)], ['42', '46'])).
% 0.56/0.72  thf('48', plain, ((v1_relat_1 @ sk_D)),
% 0.56/0.72      inference('sup-', [status(thm)], ['36', '37'])).
% 0.56/0.72  thf('49', plain,
% 0.56/0.72      (![X0 : $i]:
% 0.56/0.72         (~ (v5_relat_1 @ (k5_relat_1 @ sk_D @ X0) @ (k9_relat_1 @ X0 @ sk_B))
% 0.56/0.72          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_D @ X0))
% 0.56/0.72          | (v2_funct_2 @ (k5_relat_1 @ sk_D @ X0) @ 
% 0.56/0.72             (k2_relat_1 @ (k5_relat_1 @ sk_D @ X0)))
% 0.56/0.72          | ~ (v1_relat_1 @ X0))),
% 0.56/0.72      inference('demod', [status(thm)], ['47', '48'])).
% 0.56/0.72  thf('50', plain,
% 0.56/0.72      ((~ (v5_relat_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_C)
% 0.56/0.72        | ~ (v1_relat_1 @ sk_E)
% 0.56/0.72        | (v2_funct_2 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 0.56/0.72           (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 0.56/0.72        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 0.56/0.72      inference('sup-', [status(thm)], ['32', '49'])).
% 0.56/0.72  thf('51', plain,
% 0.56/0.72      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.56/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.72  thf('52', plain,
% 0.56/0.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.56/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.72  thf(dt_k1_partfun1, axiom,
% 0.56/0.72    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.56/0.72     ( ( ( v1_funct_1 @ E ) & 
% 0.56/0.72         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.56/0.72         ( v1_funct_1 @ F ) & 
% 0.56/0.72         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.56/0.72       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.56/0.72         ( m1_subset_1 @
% 0.56/0.72           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.56/0.72           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.56/0.72  thf('53', plain,
% 0.56/0.72      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.56/0.72         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.56/0.72          | ~ (v1_funct_1 @ X23)
% 0.56/0.72          | ~ (v1_funct_1 @ X26)
% 0.56/0.72          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.56/0.72          | (m1_subset_1 @ (k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26) @ 
% 0.56/0.72             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X28))))),
% 0.56/0.72      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.56/0.72  thf('54', plain,
% 0.56/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.72         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 0.56/0.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.56/0.72          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.56/0.72          | ~ (v1_funct_1 @ X1)
% 0.56/0.72          | ~ (v1_funct_1 @ sk_D))),
% 0.56/0.72      inference('sup-', [status(thm)], ['52', '53'])).
% 0.56/0.72  thf('55', plain, ((v1_funct_1 @ sk_D)),
% 0.56/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.72  thf('56', plain,
% 0.56/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.72         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 0.56/0.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.56/0.72          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.56/0.72          | ~ (v1_funct_1 @ X1))),
% 0.56/0.72      inference('demod', [status(thm)], ['54', '55'])).
% 0.56/0.72  thf('57', plain,
% 0.56/0.72      ((~ (v1_funct_1 @ sk_E)
% 0.56/0.72        | (m1_subset_1 @ 
% 0.56/0.72           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.56/0.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.56/0.72      inference('sup-', [status(thm)], ['51', '56'])).
% 0.56/0.72  thf('58', plain, ((v1_funct_1 @ sk_E)),
% 0.56/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.72  thf('59', plain,
% 0.56/0.72      ((m1_subset_1 @ 
% 0.56/0.72        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.56/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.56/0.72      inference('demod', [status(thm)], ['57', '58'])).
% 0.56/0.72  thf('60', plain,
% 0.56/0.72      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.56/0.72         ((v5_relat_1 @ X18 @ X20)
% 0.56/0.72          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.56/0.72      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.56/0.72  thf('61', plain,
% 0.56/0.72      ((v5_relat_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.56/0.72        sk_C)),
% 0.56/0.72      inference('sup-', [status(thm)], ['59', '60'])).
% 0.56/0.72  thf('62', plain,
% 0.56/0.72      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.56/0.72         = (k5_relat_1 @ sk_D @ sk_E))),
% 0.56/0.72      inference('demod', [status(thm)], ['7', '8'])).
% 0.56/0.72  thf('63', plain, ((v5_relat_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_C)),
% 0.56/0.72      inference('demod', [status(thm)], ['61', '62'])).
% 0.56/0.72  thf('64', plain, ((v1_relat_1 @ sk_E)),
% 0.56/0.72      inference('sup-', [status(thm)], ['17', '18'])).
% 0.56/0.72  thf('65', plain,
% 0.56/0.72      ((m1_subset_1 @ 
% 0.56/0.72        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.56/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.56/0.72      inference('demod', [status(thm)], ['57', '58'])).
% 0.56/0.72  thf('66', plain,
% 0.56/0.72      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.56/0.72         ((v1_relat_1 @ X15)
% 0.56/0.72          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.56/0.72      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.56/0.72  thf('67', plain,
% 0.56/0.72      ((v1_relat_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E))),
% 0.56/0.72      inference('sup-', [status(thm)], ['65', '66'])).
% 0.56/0.72  thf('68', plain,
% 0.56/0.72      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.56/0.72         = (k5_relat_1 @ sk_D @ sk_E))),
% 0.56/0.72      inference('demod', [status(thm)], ['7', '8'])).
% 0.56/0.72  thf('69', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_D @ sk_E))),
% 0.56/0.72      inference('demod', [status(thm)], ['67', '68'])).
% 0.56/0.72  thf('70', plain,
% 0.56/0.72      ((v2_funct_2 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 0.56/0.72        (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 0.56/0.72      inference('demod', [status(thm)], ['50', '63', '64', '69'])).
% 0.56/0.72  thf('71', plain,
% 0.56/0.72      (((v2_funct_2 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 0.56/0.72         (k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)))
% 0.56/0.72        | ~ (v1_relat_1 @ sk_D)
% 0.56/0.72        | ~ (v1_relat_1 @ sk_E))),
% 0.56/0.72      inference('sup+', [status(thm)], ['11', '70'])).
% 0.56/0.72  thf('72', plain, (((k2_relat_1 @ sk_D) = (sk_B))),
% 0.56/0.72      inference('demod', [status(thm)], ['35', '38', '41'])).
% 0.56/0.72  thf('73', plain, (((sk_C) = (k9_relat_1 @ sk_E @ sk_B))),
% 0.56/0.72      inference('demod', [status(thm)], ['22', '30', '31'])).
% 0.56/0.72  thf('74', plain, ((v1_relat_1 @ sk_D)),
% 0.56/0.72      inference('sup-', [status(thm)], ['36', '37'])).
% 0.56/0.72  thf('75', plain, ((v1_relat_1 @ sk_E)),
% 0.56/0.72      inference('sup-', [status(thm)], ['17', '18'])).
% 0.56/0.72  thf('76', plain, ((v2_funct_2 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_C)),
% 0.56/0.72      inference('demod', [status(thm)], ['71', '72', '73', '74', '75'])).
% 0.56/0.72  thf('77', plain, ($false), inference('demod', [status(thm)], ['10', '76'])).
% 0.56/0.72  
% 0.56/0.72  % SZS output end Refutation
% 0.56/0.72  
% 0.56/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
