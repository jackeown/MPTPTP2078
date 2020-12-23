%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1697+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pIZW0PGRyo

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:05 EST 2020

% Result     : Theorem 1.77s
% Output     : Refutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :  268 ( 924 expanded)
%              Number of leaves         :   42 ( 288 expanded)
%              Depth                    :   47
%              Number of atoms          : 4270 (34420 expanded)
%              Number of equality atoms :  162 (1149 expanded)
%              Maximal formula depth    :   28 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tmap_1_type,type,(
    k1_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t6_tmap_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( ~ ( v1_xboole_0 @ C )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
             => ! [D: $i] :
                  ( ( ~ ( v1_xboole_0 @ D )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) )
                 => ( ( r1_subset_1 @ C @ D )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ C @ B )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) )
                       => ! [F: $i] :
                            ( ( ( v1_funct_1 @ F )
                              & ( v1_funct_2 @ F @ D @ B )
                              & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) )
                           => ( ( ( k2_partfun1 @ C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) )
                                = ( k2_partfun1 @ D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) )
                              & ( ( k2_partfun1 @ ( k4_subset_1 @ A @ C @ D ) @ B @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C )
                                = E )
                              & ( ( k2_partfun1 @ ( k4_subset_1 @ A @ C @ D ) @ B @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D )
                                = F ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( ~ ( v1_xboole_0 @ C )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
               => ! [D: $i] :
                    ( ( ~ ( v1_xboole_0 @ D )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) )
                   => ( ( r1_subset_1 @ C @ D )
                     => ! [E: $i] :
                          ( ( ( v1_funct_1 @ E )
                            & ( v1_funct_2 @ E @ C @ B )
                            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) )
                         => ! [F: $i] :
                              ( ( ( v1_funct_1 @ F )
                                & ( v1_funct_2 @ F @ D @ B )
                                & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) )
                             => ( ( ( k2_partfun1 @ C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) )
                                  = ( k2_partfun1 @ D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) )
                                & ( ( k2_partfun1 @ ( k4_subset_1 @ A @ C @ D ) @ B @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C )
                                  = E )
                                & ( ( k2_partfun1 @ ( k4_subset_1 @ A @ C @ D ) @ B @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D )
                                  = F ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t6_tmap_1])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_subset_1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r1_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ( ( r1_subset_1 @ A @ B )
      <=> ( r1_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ( v1_xboole_0 @ X28 )
      | ( r1_xboole_0 @ X27 @ X28 )
      | ~ ( r1_subset_1 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_subset_1])).

thf('3',plain,
    ( ( r1_xboole_0 @ sk_C @ sk_D )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r1_xboole_0 @ sk_C @ sk_D ) ),
    inference(clc,[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r1_xboole_0 @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['5','6'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('10',plain,(
    ! [X31: $i,X32: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X31 @ X32 ) @ X31 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('11',plain,(
    r1_tarski @ k1_xboole_0 @ sk_C ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_2 @ D @ A @ B )
        & ( v1_funct_1 @ D ) )
     => ( ( r1_tarski @ C @ A )
       => ( ( ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ D @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) )
            & ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B )
            & ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) )
          | ( ( A != k1_xboole_0 )
            & ( B = k1_xboole_0 ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_1 @ B @ A )
     => ( ( B = k1_xboole_0 )
        & ( A != k1_xboole_0 ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ B @ A )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) )
        & ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ D @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ C @ A )
       => ( ( zip_tseitin_1 @ B @ A )
          | ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) )).

thf('13',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( r1_tarski @ X39 @ X40 )
      | ( zip_tseitin_1 @ X41 @ X40 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( zip_tseitin_0 @ X42 @ X39 @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_E @ X0 @ sk_B @ sk_C )
      | ~ ( v1_funct_2 @ sk_E @ sk_C @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ( zip_tseitin_1 @ sk_B @ sk_C )
      | ~ ( r1_tarski @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_E @ X0 @ sk_B @ sk_C )
      | ( zip_tseitin_1 @ sk_B @ sk_C )
      | ~ ( r1_tarski @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_C )
    | ( zip_tseitin_0 @ sk_E @ k1_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ X33 @ X34 @ X35 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X34 ) ) )
      | ~ ( zip_tseitin_0 @ X35 @ X36 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('20',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_C )
    | ( m1_subset_1 @ ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('22',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_C )
    | ( v1_xboole_0 @ ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('23',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('24',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('25',plain,(
    ! [X43: $i] :
      ( ( X43 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('26',plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_C )
    | ( v1_xboole_0 @ ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X43: $i] :
      ( ( X43 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('30',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_C )
    | ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('32',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X3 )
      = ( k3_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('33',plain,(
    ! [X31: $i,X32: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X31 @ X32 ) @ X31 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    r1_tarski @ k1_xboole_0 @ sk_D ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( r1_tarski @ X39 @ X40 )
      | ( zip_tseitin_1 @ X41 @ X40 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( zip_tseitin_0 @ X42 @ X39 @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_F @ X0 @ sk_B @ sk_D )
      | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B )
      | ~ ( v1_funct_1 @ sk_F )
      | ( zip_tseitin_1 @ sk_B @ sk_D )
      | ~ ( r1_tarski @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_F @ X0 @ sk_B @ sk_D )
      | ( zip_tseitin_1 @ sk_B @ sk_D )
      | ~ ( r1_tarski @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_D )
    | ( zip_tseitin_0 @ sk_F @ k1_xboole_0 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['35','41'])).

thf('43',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ X33 @ X34 @ X35 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X34 ) ) )
      | ~ ( zip_tseitin_0 @ X35 @ X36 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('44',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_D )
    | ( m1_subset_1 @ ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('46',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_D )
    | ( v1_xboole_0 @ ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['23','26'])).

thf('48',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_D )
    | ( v1_xboole_0 @ ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X43: $i] :
      ( ( X43 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('50',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_D )
    | ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tmap_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B )
        & ~ ( v1_xboole_0 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
        & ~ ( v1_xboole_0 @ D )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ C @ B )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( v1_funct_2 @ F @ D @ B )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) )
        & ( v1_funct_2 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( k4_subset_1 @ A @ C @ D ) @ B )
        & ( m1_subset_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ) )).

thf('54',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X22 ) )
      | ( v1_xboole_0 @ X19 )
      | ( v1_xboole_0 @ X20 )
      | ( v1_xboole_0 @ X22 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_2 @ X23 @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X22 @ X20 @ X19 @ X21 @ X18 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ X2 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ X2 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['52','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['51','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X22 ) )
      | ( v1_xboole_0 @ X19 )
      | ( v1_xboole_0 @ X20 )
      | ( v1_xboole_0 @ X22 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_2 @ X23 @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X22 @ X20 @ X19 @ X21 @ X18 @ X23 ) @ ( k4_subset_1 @ X22 @ X19 @ X21 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ ( k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2 ) @ ( k4_subset_1 @ X1 @ sk_C @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ ( k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2 ) @ ( k4_subset_1 @ X1 @ sk_C @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ X0 @ sk_C @ sk_D ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['67','73'])).

thf('75',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ X0 @ sk_C @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['66','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X22 ) )
      | ( v1_xboole_0 @ X19 )
      | ( v1_xboole_0 @ X20 )
      | ( v1_xboole_0 @ X22 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_2 @ X23 @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X22 @ X20 @ X19 @ X21 @ X18 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X22 @ X19 @ X21 ) @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X1 @ sk_C @ X0 ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X1 @ sk_C @ X0 ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X0 @ sk_C @ sk_D ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['82','88'])).

thf('90',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X0 @ sk_C @ sk_D ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['81','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['93','94'])).

thf(d1_tmap_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( ~ ( v1_xboole_0 @ C )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
             => ! [D: $i] :
                  ( ( ~ ( v1_xboole_0 @ D )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ C @ B )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) )
                     => ! [F: $i] :
                          ( ( ( v1_funct_1 @ F )
                            & ( v1_funct_2 @ F @ D @ B )
                            & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) )
                         => ( ( ( k2_partfun1 @ C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) )
                              = ( k2_partfun1 @ D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) )
                           => ! [G: $i] :
                                ( ( ( v1_funct_1 @ G )
                                  & ( v1_funct_2 @ G @ ( k4_subset_1 @ A @ C @ D ) @ B )
                                  & ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) )
                               => ( ( G
                                    = ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) )
                                <=> ( ( ( k2_partfun1 @ ( k4_subset_1 @ A @ C @ D ) @ B @ G @ C )
                                      = E )
                                    & ( ( k2_partfun1 @ ( k4_subset_1 @ A @ C @ D ) @ B @ G @ D )
                                      = F ) ) ) ) ) ) ) ) ) ) ) )).

thf('96',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X8 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_funct_2 @ X11 @ X9 @ X8 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) )
      | ( X14
       != ( k1_tmap_1 @ X10 @ X8 @ X13 @ X9 @ X12 @ X11 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X10 @ X13 @ X9 ) @ X8 @ X14 @ X13 )
        = X12 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X10 @ X13 @ X9 ) @ X8 ) ) )
      | ~ ( v1_funct_2 @ X14 @ ( k4_subset_1 @ X10 @ X13 @ X9 ) @ X8 )
      | ~ ( v1_funct_1 @ X14 )
      | ( ( k2_partfun1 @ X13 @ X8 @ X12 @ ( k9_subset_1 @ X10 @ X13 @ X9 ) )
       != ( k2_partfun1 @ X9 @ X8 @ X11 @ ( k9_subset_1 @ X10 @ X13 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X8 ) ) )
      | ~ ( v1_funct_2 @ X12 @ X13 @ X8 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_xboole_0 @ X13 )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('97',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v1_xboole_0 @ X10 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_2 @ X12 @ X13 @ X8 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X8 ) ) )
      | ( ( k2_partfun1 @ X13 @ X8 @ X12 @ ( k9_subset_1 @ X10 @ X13 @ X9 ) )
       != ( k2_partfun1 @ X9 @ X8 @ X11 @ ( k9_subset_1 @ X10 @ X13 @ X9 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X10 @ X8 @ X13 @ X9 @ X12 @ X11 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X10 @ X8 @ X13 @ X9 @ X12 @ X11 ) @ ( k4_subset_1 @ X10 @ X13 @ X9 ) @ X8 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X10 @ X8 @ X13 @ X9 @ X12 @ X11 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X10 @ X13 @ X9 ) @ X8 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X10 @ X13 @ X9 ) @ X8 @ ( k1_tmap_1 @ X10 @ X8 @ X13 @ X9 @ X12 @ X11 ) @ X13 )
        = X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) )
      | ~ ( v1_funct_2 @ X11 @ X9 @ X8 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_xboole_0 @ X9 )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_E @ sk_C @ sk_B )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['95','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('104',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k9_subset_1 @ X5 @ X7 @ X6 )
        = ( k9_subset_1 @ X5 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_C )
      = ( k9_subset_1 @ sk_A @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('107',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k9_subset_1 @ X26 @ X24 @ X25 )
        = ( k3_xboole_0 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_C )
      = ( k9_subset_1 @ sk_A @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['105','108'])).

thf('110',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X3 )
      = ( k3_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('111',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_C )
      = ( k9_subset_1 @ sk_A @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['105','108'])).

thf('113',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X3 )
      = ( k3_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('114',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('115',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0 ) )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['98','99','100','101','102','109','110','111','112','113','114','115','116','117','118'])).

thf('120',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E ) ),
    inference(split,[status(esa)],['121'])).

thf('123',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_C )
    | ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('124',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_D )
    | ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('125',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k9_subset_1 @ X5 @ X7 @ X6 )
        = ( k9_subset_1 @ X5 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k9_subset_1 @ sk_A @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('129',plain,
    ( ( k9_subset_1 @ sk_A @ sk_C @ sk_D )
    = ( k3_xboole_0 @ sk_D @ sk_C ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X3 )
      = ( k3_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('131',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('132',plain,
    ( ( k9_subset_1 @ sk_A @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['121'])).

thf('134',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( ( k9_subset_1 @ sk_A @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('136',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,
    ( ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_B @ sk_D ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['124','136'])).

thf('138',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_B @ sk_C )
      | ( zip_tseitin_1 @ sk_B @ sk_D ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['123','137'])).

thf('139',plain,
    ( ( ( zip_tseitin_1 @ sk_B @ sk_D )
      | ( zip_tseitin_1 @ sk_B @ sk_C ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X37 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('141',plain,
    ( ( ( zip_tseitin_1 @ sk_B @ sk_C )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X37 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('143',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['141','142'])).

thf('144',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['23','26'])).

thf('147',plain,
    ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
    = ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_C )
    | ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('149',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_D )
    | ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('150',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('151',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('152',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('153',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X8 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_funct_2 @ X11 @ X9 @ X8 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) )
      | ( X14
       != ( k1_tmap_1 @ X10 @ X8 @ X13 @ X9 @ X12 @ X11 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X10 @ X13 @ X9 ) @ X8 @ X14 @ X9 )
        = X11 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X10 @ X13 @ X9 ) @ X8 ) ) )
      | ~ ( v1_funct_2 @ X14 @ ( k4_subset_1 @ X10 @ X13 @ X9 ) @ X8 )
      | ~ ( v1_funct_1 @ X14 )
      | ( ( k2_partfun1 @ X13 @ X8 @ X12 @ ( k9_subset_1 @ X10 @ X13 @ X9 ) )
       != ( k2_partfun1 @ X9 @ X8 @ X11 @ ( k9_subset_1 @ X10 @ X13 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X8 ) ) )
      | ~ ( v1_funct_2 @ X12 @ X13 @ X8 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_xboole_0 @ X13 )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('154',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v1_xboole_0 @ X10 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_2 @ X12 @ X13 @ X8 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X8 ) ) )
      | ( ( k2_partfun1 @ X13 @ X8 @ X12 @ ( k9_subset_1 @ X10 @ X13 @ X9 ) )
       != ( k2_partfun1 @ X9 @ X8 @ X11 @ ( k9_subset_1 @ X10 @ X13 @ X9 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X10 @ X8 @ X13 @ X9 @ X12 @ X11 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X10 @ X8 @ X13 @ X9 @ X12 @ X11 ) @ ( k4_subset_1 @ X10 @ X13 @ X9 ) @ X8 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X10 @ X8 @ X13 @ X9 @ X12 @ X11 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X10 @ X13 @ X9 ) @ X8 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X10 @ X13 @ X9 ) @ X8 @ ( k1_tmap_1 @ X10 @ X8 @ X13 @ X9 @ X12 @ X11 ) @ X9 )
        = X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) )
      | ~ ( v1_funct_2 @ X11 @ X9 @ X8 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_xboole_0 @ X9 )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_E @ sk_C @ sk_B )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['152','154'])).

thf('156',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_C )
      = ( k9_subset_1 @ sk_A @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['105','108'])).

thf('161',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X3 )
      = ( k3_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('162',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_C )
      = ( k9_subset_1 @ sk_A @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['105','108'])).

thf('164',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X3 )
      = ( k3_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('165',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('166',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0 ) )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['155','156','157','158','159','160','161','162','163','164','165','166','167','168','169'])).

thf('171',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['151','171'])).

thf('173',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['150','173'])).

thf('175',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0 ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_B @ sk_D )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference('sup-',[status(thm)],['149','175'])).

thf('177',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_B @ sk_C )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['148','176'])).

thf('178',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_D )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( zip_tseitin_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['177'])).

thf('179',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['121'])).

thf('180',plain,
    ( ( ( sk_F != sk_F )
      | ( zip_tseitin_1 @ sk_B @ sk_C )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_D )
      | ( zip_tseitin_1 @ sk_B @ sk_D ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,
    ( ( ( zip_tseitin_1 @ sk_B @ sk_D )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A )
      | ( zip_tseitin_1 @ sk_B @ sk_C ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['180'])).

thf('182',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X37 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('183',plain,
    ( ( ( zip_tseitin_1 @ sk_B @ sk_C )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_D )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X37 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('185',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_D )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['185'])).

thf('187',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('193',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['192','193'])).

thf('195',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['23','26'])).

thf('198',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
    = sk_F ),
    inference(demod,[status(thm)],['196','197'])).

thf('199',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
    | ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['121'])).

thf('200',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['147','198','199'])).

thf('201',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['122','200'])).

thf('202',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['120','201'])).

thf('203',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['80','202'])).

thf('204',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['203'])).

thf('205',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['65','204'])).

thf('206',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0 ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['205'])).

thf('207',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_B @ sk_D )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','206'])).

thf('208',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_B @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['30','207'])).

thf('209',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_D )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( zip_tseitin_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['208'])).

thf('210',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X37 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('211',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['209','210'])).

thf('212',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X37 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('213',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['213'])).

thf('215',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['216','217'])).

thf('219',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['218','219'])).

thf('221',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['220','221'])).

thf('223',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['23','26'])).

thf('224',plain,(
    $false ),
    inference(demod,[status(thm)],['0','222','223'])).


%------------------------------------------------------------------------------
