%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cvhbnpVNjR

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:58 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 139 expanded)
%              Number of leaves         :   34 (  57 expanded)
%              Depth                    :   13
%              Number of atoms          :  850 (2745 expanded)
%              Number of equality atoms :   49 ( 122 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t185_funct_2,conjecture,(
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
                          = ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t185_funct_2])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_F @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ sk_F @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t21_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_relat_1 @ E )
            & ( v1_funct_1 @ E ) )
         => ( ( r2_hidden @ C @ A )
           => ( ( B = k1_xboole_0 )
              | ( ( k1_funct_1 @ ( k5_relat_1 @ D @ E ) @ C )
                = ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ C ) ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_relat_1 @ X35 )
      | ~ ( v1_funct_1 @ X35 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X36 @ X35 ) @ X37 )
        = ( k1_funct_1 @ X35 @ ( k1_funct_1 @ X36 @ X37 ) ) )
      | ( X38 = k1_xboole_0 )
      | ~ ( r2_hidden @ X37 @ X39 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X39 @ X38 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_2])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( sk_C = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X1 ) @ X0 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( sk_C = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X1 ) @ X0 )
        = ( k1_funct_1 @ X1 @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ X0 ) @ sk_F )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d12_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ ( k1_relset_1 @ B @ C @ E ) )
           => ( ( B = k1_xboole_0 )
              | ( ( k8_funct_2 @ A @ B @ C @ D @ E )
                = ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k8_funct_2 @ X27 @ X25 @ X26 @ X28 @ X24 )
        = ( k1_partfun1 @ X27 @ X25 @ X25 @ X26 @ X28 @ X24 ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X27 @ X25 @ X28 ) @ ( k1_relset_1 @ X25 @ X26 @ X24 ) )
      | ( X25 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X27 @ X25 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d12_funct_2])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C ) ) )
      | ( sk_C = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X1 @ sk_C @ X0 ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) )
      | ( ( k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E )
        = ( k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_C ) ) )
      | ( sk_C = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X1 @ sk_C @ X0 ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) )
      | ( ( k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E )
        = ( k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k1_partfun1 @ sk_B_1 @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E ) )
    | ( sk_C = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('20',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 )
        = ( k5_relat_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B_1 @ sk_C @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B_1 @ sk_C @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_B_1 @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k1_partfun1 @ sk_B_1 @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','26','27','28','29'])).

thf('31',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F ) )
    | ( sk_C = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_E )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('36',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('37',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F )
     != ( k1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_F ) )
    | ( sk_C = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34','37'])).

thf('39',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('40',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('41',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('46',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('47',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('49',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('50',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['45','52'])).

thf('54',plain,(
    sk_C = k1_xboole_0 ),
    inference(clc,[status(thm)],['39','53'])).

thf('55',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['48','51'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['0','54','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cvhbnpVNjR
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:39:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.39/1.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.39/1.59  % Solved by: fo/fo7.sh
% 1.39/1.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.39/1.59  % done 1407 iterations in 1.149s
% 1.39/1.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.39/1.59  % SZS output start Refutation
% 1.39/1.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.39/1.59  thf(sk_F_type, type, sk_F: $i).
% 1.39/1.59  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.39/1.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.39/1.59  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.39/1.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.39/1.59  thf(sk_D_type, type, sk_D: $i).
% 1.39/1.59  thf(sk_C_type, type, sk_C: $i).
% 1.39/1.59  thf(sk_B_type, type, sk_B: $i > $i).
% 1.39/1.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.39/1.59  thf(sk_E_type, type, sk_E: $i).
% 1.39/1.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.39/1.59  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.39/1.59  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.39/1.59  thf(sk_A_type, type, sk_A: $i).
% 1.39/1.59  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 1.39/1.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.39/1.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.39/1.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.39/1.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.39/1.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.39/1.59  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.39/1.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.39/1.59  thf(t185_funct_2, conjecture,
% 1.39/1.59    (![A:$i,B:$i,C:$i]:
% 1.39/1.59     ( ( ~( v1_xboole_0 @ C ) ) =>
% 1.39/1.59       ( ![D:$i]:
% 1.39/1.59         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 1.39/1.59             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.39/1.59           ( ![E:$i]:
% 1.39/1.59             ( ( ( v1_funct_1 @ E ) & 
% 1.39/1.59                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 1.39/1.59               ( ![F:$i]:
% 1.39/1.59                 ( ( m1_subset_1 @ F @ B ) =>
% 1.39/1.59                   ( ( r1_tarski @
% 1.39/1.59                       ( k2_relset_1 @ B @ C @ D ) @ 
% 1.39/1.59                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 1.39/1.59                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.39/1.59                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 1.39/1.59                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.39/1.59  thf(zf_stmt_0, negated_conjecture,
% 1.39/1.59    (~( ![A:$i,B:$i,C:$i]:
% 1.39/1.59        ( ( ~( v1_xboole_0 @ C ) ) =>
% 1.39/1.59          ( ![D:$i]:
% 1.39/1.59            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 1.39/1.59                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.39/1.59              ( ![E:$i]:
% 1.39/1.59                ( ( ( v1_funct_1 @ E ) & 
% 1.39/1.59                    ( m1_subset_1 @
% 1.39/1.59                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 1.39/1.59                  ( ![F:$i]:
% 1.39/1.59                    ( ( m1_subset_1 @ F @ B ) =>
% 1.39/1.59                      ( ( r1_tarski @
% 1.39/1.59                          ( k2_relset_1 @ B @ C @ D ) @ 
% 1.39/1.59                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 1.39/1.59                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.39/1.59                          ( ( k1_funct_1 @
% 1.39/1.59                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 1.39/1.59                            ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.39/1.59    inference('cnf.neg', [status(esa)], [t185_funct_2])).
% 1.39/1.59  thf('0', plain, (~ (v1_xboole_0 @ sk_C)),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf('1', plain, ((m1_subset_1 @ sk_F @ sk_B_1)),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf(t2_subset, axiom,
% 1.39/1.59    (![A:$i,B:$i]:
% 1.39/1.59     ( ( m1_subset_1 @ A @ B ) =>
% 1.39/1.59       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 1.39/1.59  thf('2', plain,
% 1.39/1.59      (![X8 : $i, X9 : $i]:
% 1.39/1.59         ((r2_hidden @ X8 @ X9)
% 1.39/1.59          | (v1_xboole_0 @ X9)
% 1.39/1.59          | ~ (m1_subset_1 @ X8 @ X9))),
% 1.39/1.59      inference('cnf', [status(esa)], [t2_subset])).
% 1.39/1.59  thf('3', plain, (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ sk_F @ sk_B_1))),
% 1.39/1.59      inference('sup-', [status(thm)], ['1', '2'])).
% 1.39/1.59  thf('4', plain,
% 1.39/1.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf(t21_funct_2, axiom,
% 1.39/1.59    (![A:$i,B:$i,C:$i,D:$i]:
% 1.39/1.59     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.39/1.59         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.39/1.59       ( ![E:$i]:
% 1.39/1.59         ( ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) ) =>
% 1.39/1.59           ( ( r2_hidden @ C @ A ) =>
% 1.39/1.59             ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.39/1.59               ( ( k1_funct_1 @ ( k5_relat_1 @ D @ E ) @ C ) =
% 1.39/1.59                 ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ C ) ) ) ) ) ) ) ))).
% 1.39/1.59  thf('5', plain,
% 1.39/1.59      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 1.39/1.59         (~ (v1_relat_1 @ X35)
% 1.39/1.59          | ~ (v1_funct_1 @ X35)
% 1.39/1.59          | ((k1_funct_1 @ (k5_relat_1 @ X36 @ X35) @ X37)
% 1.39/1.59              = (k1_funct_1 @ X35 @ (k1_funct_1 @ X36 @ X37)))
% 1.39/1.59          | ((X38) = (k1_xboole_0))
% 1.39/1.59          | ~ (r2_hidden @ X37 @ X39)
% 1.39/1.59          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 1.39/1.59          | ~ (v1_funct_2 @ X36 @ X39 @ X38)
% 1.39/1.59          | ~ (v1_funct_1 @ X36))),
% 1.39/1.59      inference('cnf', [status(esa)], [t21_funct_2])).
% 1.39/1.59  thf('6', plain,
% 1.39/1.59      (![X0 : $i, X1 : $i]:
% 1.39/1.59         (~ (v1_funct_1 @ sk_D)
% 1.39/1.59          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_C)
% 1.39/1.59          | ~ (r2_hidden @ X0 @ sk_B_1)
% 1.39/1.59          | ((sk_C) = (k1_xboole_0))
% 1.39/1.59          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X1) @ X0)
% 1.39/1.59              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D @ X0)))
% 1.39/1.59          | ~ (v1_funct_1 @ X1)
% 1.39/1.59          | ~ (v1_relat_1 @ X1))),
% 1.39/1.59      inference('sup-', [status(thm)], ['4', '5'])).
% 1.39/1.59  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf('8', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_C)),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf('9', plain,
% 1.39/1.59      (![X0 : $i, X1 : $i]:
% 1.39/1.59         (~ (r2_hidden @ X0 @ sk_B_1)
% 1.39/1.59          | ((sk_C) = (k1_xboole_0))
% 1.39/1.59          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X1) @ X0)
% 1.39/1.59              = (k1_funct_1 @ X1 @ (k1_funct_1 @ sk_D @ X0)))
% 1.39/1.59          | ~ (v1_funct_1 @ X1)
% 1.39/1.59          | ~ (v1_relat_1 @ X1))),
% 1.39/1.59      inference('demod', [status(thm)], ['6', '7', '8'])).
% 1.39/1.59  thf('10', plain,
% 1.39/1.59      (![X0 : $i]:
% 1.39/1.59         ((v1_xboole_0 @ sk_B_1)
% 1.39/1.59          | ~ (v1_relat_1 @ X0)
% 1.39/1.59          | ~ (v1_funct_1 @ X0)
% 1.39/1.59          | ((k1_funct_1 @ (k5_relat_1 @ sk_D @ X0) @ sk_F)
% 1.39/1.59              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ sk_F)))
% 1.39/1.59          | ((sk_C) = (k1_xboole_0)))),
% 1.39/1.59      inference('sup-', [status(thm)], ['3', '9'])).
% 1.39/1.59  thf('11', plain,
% 1.39/1.59      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C @ sk_D) @ 
% 1.39/1.59        (k1_relset_1 @ sk_C @ sk_A @ sk_E))),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf('12', plain,
% 1.39/1.59      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf(d12_funct_2, axiom,
% 1.39/1.59    (![A:$i,B:$i,C:$i,D:$i]:
% 1.39/1.59     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.39/1.59         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.39/1.59       ( ![E:$i]:
% 1.39/1.59         ( ( ( v1_funct_1 @ E ) & 
% 1.39/1.59             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.39/1.59           ( ( r1_tarski @
% 1.39/1.59               ( k2_relset_1 @ A @ B @ D ) @ ( k1_relset_1 @ B @ C @ E ) ) =>
% 1.39/1.59             ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.39/1.59               ( ( k8_funct_2 @ A @ B @ C @ D @ E ) =
% 1.39/1.59                 ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) ) ) ) ))).
% 1.39/1.59  thf('13', plain,
% 1.39/1.59      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.39/1.59         (~ (v1_funct_1 @ X24)
% 1.39/1.59          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 1.39/1.59          | ((k8_funct_2 @ X27 @ X25 @ X26 @ X28 @ X24)
% 1.39/1.59              = (k1_partfun1 @ X27 @ X25 @ X25 @ X26 @ X28 @ X24))
% 1.39/1.59          | ~ (r1_tarski @ (k2_relset_1 @ X27 @ X25 @ X28) @ 
% 1.39/1.59               (k1_relset_1 @ X25 @ X26 @ X24))
% 1.39/1.59          | ((X25) = (k1_xboole_0))
% 1.39/1.59          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X25)))
% 1.39/1.59          | ~ (v1_funct_2 @ X28 @ X27 @ X25)
% 1.39/1.59          | ~ (v1_funct_1 @ X28))),
% 1.39/1.59      inference('cnf', [status(esa)], [d12_funct_2])).
% 1.39/1.59  thf('14', plain,
% 1.39/1.59      (![X0 : $i, X1 : $i]:
% 1.39/1.59         (~ (v1_funct_1 @ X0)
% 1.39/1.59          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C)
% 1.39/1.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C)))
% 1.39/1.59          | ((sk_C) = (k1_xboole_0))
% 1.39/1.59          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C @ X0) @ 
% 1.39/1.59               (k1_relset_1 @ sk_C @ sk_A @ sk_E))
% 1.39/1.59          | ((k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E)
% 1.39/1.59              = (k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E))
% 1.39/1.59          | ~ (v1_funct_1 @ sk_E))),
% 1.39/1.59      inference('sup-', [status(thm)], ['12', '13'])).
% 1.39/1.59  thf('15', plain, ((v1_funct_1 @ sk_E)),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf('16', plain,
% 1.39/1.59      (![X0 : $i, X1 : $i]:
% 1.39/1.59         (~ (v1_funct_1 @ X0)
% 1.39/1.59          | ~ (v1_funct_2 @ X0 @ X1 @ sk_C)
% 1.39/1.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_C)))
% 1.39/1.59          | ((sk_C) = (k1_xboole_0))
% 1.39/1.59          | ~ (r1_tarski @ (k2_relset_1 @ X1 @ sk_C @ X0) @ 
% 1.39/1.59               (k1_relset_1 @ sk_C @ sk_A @ sk_E))
% 1.39/1.59          | ((k8_funct_2 @ X1 @ sk_C @ sk_A @ X0 @ sk_E)
% 1.39/1.59              = (k1_partfun1 @ X1 @ sk_C @ sk_C @ sk_A @ X0 @ sk_E)))),
% 1.39/1.59      inference('demod', [status(thm)], ['14', '15'])).
% 1.39/1.59  thf('17', plain,
% 1.39/1.59      ((((k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D @ sk_E)
% 1.39/1.59          = (k1_partfun1 @ sk_B_1 @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E))
% 1.39/1.59        | ((sk_C) = (k1_xboole_0))
% 1.39/1.59        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))
% 1.39/1.59        | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_C)
% 1.39/1.59        | ~ (v1_funct_1 @ sk_D))),
% 1.39/1.59      inference('sup-', [status(thm)], ['11', '16'])).
% 1.39/1.59  thf('18', plain,
% 1.39/1.59      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf('19', plain,
% 1.39/1.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf(redefinition_k1_partfun1, axiom,
% 1.39/1.59    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.39/1.59     ( ( ( v1_funct_1 @ E ) & 
% 1.39/1.59         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.39/1.59         ( v1_funct_1 @ F ) & 
% 1.39/1.59         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.39/1.59       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.39/1.59  thf('20', plain,
% 1.39/1.59      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.39/1.59         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 1.39/1.59          | ~ (v1_funct_1 @ X29)
% 1.39/1.59          | ~ (v1_funct_1 @ X32)
% 1.39/1.59          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 1.39/1.59          | ((k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32)
% 1.39/1.59              = (k5_relat_1 @ X29 @ X32)))),
% 1.39/1.59      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.39/1.59  thf('21', plain,
% 1.39/1.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.39/1.59         (((k1_partfun1 @ sk_B_1 @ sk_C @ X2 @ X1 @ sk_D @ X0)
% 1.39/1.59            = (k5_relat_1 @ sk_D @ X0))
% 1.39/1.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.39/1.59          | ~ (v1_funct_1 @ X0)
% 1.39/1.59          | ~ (v1_funct_1 @ sk_D))),
% 1.39/1.59      inference('sup-', [status(thm)], ['19', '20'])).
% 1.39/1.59  thf('22', plain, ((v1_funct_1 @ sk_D)),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf('23', plain,
% 1.39/1.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.39/1.59         (((k1_partfun1 @ sk_B_1 @ sk_C @ X2 @ X1 @ sk_D @ X0)
% 1.39/1.59            = (k5_relat_1 @ sk_D @ X0))
% 1.39/1.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.39/1.59          | ~ (v1_funct_1 @ X0))),
% 1.39/1.59      inference('demod', [status(thm)], ['21', '22'])).
% 1.39/1.59  thf('24', plain,
% 1.39/1.59      ((~ (v1_funct_1 @ sk_E)
% 1.39/1.59        | ((k1_partfun1 @ sk_B_1 @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E)
% 1.39/1.59            = (k5_relat_1 @ sk_D @ sk_E)))),
% 1.39/1.59      inference('sup-', [status(thm)], ['18', '23'])).
% 1.39/1.59  thf('25', plain, ((v1_funct_1 @ sk_E)),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf('26', plain,
% 1.39/1.59      (((k1_partfun1 @ sk_B_1 @ sk_C @ sk_C @ sk_A @ sk_D @ sk_E)
% 1.39/1.59         = (k5_relat_1 @ sk_D @ sk_E))),
% 1.39/1.59      inference('demod', [status(thm)], ['24', '25'])).
% 1.39/1.59  thf('27', plain,
% 1.39/1.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf('28', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_C)),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf('29', plain, ((v1_funct_1 @ sk_D)),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf('30', plain,
% 1.39/1.59      ((((k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D @ sk_E)
% 1.39/1.59          = (k5_relat_1 @ sk_D @ sk_E))
% 1.39/1.59        | ((sk_C) = (k1_xboole_0)))),
% 1.39/1.59      inference('demod', [status(thm)], ['17', '26', '27', '28', '29'])).
% 1.39/1.59  thf('31', plain,
% 1.39/1.59      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 1.39/1.59         != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf('32', plain,
% 1.39/1.59      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 1.39/1.59          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 1.39/1.59        | ((sk_C) = (k1_xboole_0)))),
% 1.39/1.59      inference('sup-', [status(thm)], ['30', '31'])).
% 1.39/1.59  thf('33', plain,
% 1.39/1.59      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 1.39/1.59          != (k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F))
% 1.39/1.59        | ((sk_C) = (k1_xboole_0))
% 1.39/1.59        | ~ (v1_funct_1 @ sk_E)
% 1.39/1.59        | ~ (v1_relat_1 @ sk_E)
% 1.39/1.59        | (v1_xboole_0 @ sk_B_1)
% 1.39/1.59        | ((sk_C) = (k1_xboole_0)))),
% 1.39/1.59      inference('sup-', [status(thm)], ['10', '32'])).
% 1.39/1.59  thf('34', plain, ((v1_funct_1 @ sk_E)),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf('35', plain,
% 1.39/1.59      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf(cc1_relset_1, axiom,
% 1.39/1.59    (![A:$i,B:$i,C:$i]:
% 1.39/1.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.39/1.59       ( v1_relat_1 @ C ) ))).
% 1.39/1.59  thf('36', plain,
% 1.39/1.59      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.39/1.59         ((v1_relat_1 @ X18)
% 1.39/1.59          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.39/1.59      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.39/1.59  thf('37', plain, ((v1_relat_1 @ sk_E)),
% 1.39/1.59      inference('sup-', [status(thm)], ['35', '36'])).
% 1.39/1.59  thf('38', plain,
% 1.39/1.59      ((((k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F)
% 1.39/1.59          != (k1_funct_1 @ (k5_relat_1 @ sk_D @ sk_E) @ sk_F))
% 1.39/1.59        | ((sk_C) = (k1_xboole_0))
% 1.39/1.59        | (v1_xboole_0 @ sk_B_1)
% 1.39/1.59        | ((sk_C) = (k1_xboole_0)))),
% 1.39/1.59      inference('demod', [status(thm)], ['33', '34', '37'])).
% 1.39/1.59  thf('39', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_C) = (k1_xboole_0)))),
% 1.39/1.59      inference('simplify', [status(thm)], ['38'])).
% 1.39/1.59  thf(l13_xboole_0, axiom,
% 1.39/1.59    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.39/1.59  thf('40', plain,
% 1.39/1.59      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 1.39/1.59      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.39/1.59  thf('41', plain,
% 1.39/1.59      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 1.39/1.59      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.39/1.59  thf('42', plain,
% 1.39/1.59      (![X0 : $i, X1 : $i]:
% 1.39/1.59         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 1.39/1.59      inference('sup+', [status(thm)], ['40', '41'])).
% 1.39/1.59  thf('43', plain, (((sk_B_1) != (k1_xboole_0))),
% 1.39/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.39/1.59  thf('44', plain,
% 1.39/1.59      (![X0 : $i]:
% 1.39/1.59         (((X0) != (k1_xboole_0))
% 1.39/1.59          | ~ (v1_xboole_0 @ X0)
% 1.39/1.59          | ~ (v1_xboole_0 @ sk_B_1))),
% 1.39/1.59      inference('sup-', [status(thm)], ['42', '43'])).
% 1.39/1.59  thf('45', plain,
% 1.39/1.59      ((~ (v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.39/1.59      inference('simplify', [status(thm)], ['44'])).
% 1.39/1.59  thf(t4_subset_1, axiom,
% 1.39/1.59    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.39/1.59  thf('46', plain,
% 1.39/1.59      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 1.39/1.59      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.39/1.59  thf(t3_subset, axiom,
% 1.39/1.59    (![A:$i,B:$i]:
% 1.39/1.59     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.39/1.59  thf('47', plain,
% 1.39/1.59      (![X10 : $i, X11 : $i]:
% 1.39/1.59         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 1.39/1.59      inference('cnf', [status(esa)], [t3_subset])).
% 1.39/1.59  thf('48', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.39/1.59      inference('sup-', [status(thm)], ['46', '47'])).
% 1.39/1.59  thf(d1_xboole_0, axiom,
% 1.39/1.59    (![A:$i]:
% 1.39/1.59     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.39/1.59  thf('49', plain,
% 1.39/1.59      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.39/1.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.39/1.59  thf(t7_ordinal1, axiom,
% 1.39/1.59    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.39/1.59  thf('50', plain,
% 1.39/1.59      (![X16 : $i, X17 : $i]:
% 1.39/1.59         (~ (r2_hidden @ X16 @ X17) | ~ (r1_tarski @ X17 @ X16))),
% 1.39/1.59      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.39/1.59  thf('51', plain,
% 1.39/1.59      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 1.39/1.59      inference('sup-', [status(thm)], ['49', '50'])).
% 1.39/1.59  thf('52', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.39/1.59      inference('sup-', [status(thm)], ['48', '51'])).
% 1.39/1.59  thf('53', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.39/1.59      inference('demod', [status(thm)], ['45', '52'])).
% 1.39/1.59  thf('54', plain, (((sk_C) = (k1_xboole_0))),
% 1.39/1.59      inference('clc', [status(thm)], ['39', '53'])).
% 1.39/1.59  thf('55', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.39/1.59      inference('sup-', [status(thm)], ['48', '51'])).
% 1.39/1.59  thf('56', plain, ($false),
% 1.39/1.59      inference('demod', [status(thm)], ['0', '54', '55'])).
% 1.39/1.59  
% 1.39/1.59  % SZS output end Refutation
% 1.39/1.59  
% 1.39/1.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
