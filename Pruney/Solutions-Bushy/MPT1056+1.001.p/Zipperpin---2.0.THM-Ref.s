%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1056+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mTqAsHuCkX

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:59 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 764 expanded)
%              Number of leaves         :   43 ( 235 expanded)
%              Depth                    :   29
%              Number of atoms          : 1742 (20296 expanded)
%              Number of equality atoms :   45 ( 651 expanded)
%              Maximal formula depth    :   21 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t173_funct_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ A @ B )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
             => ! [D: $i] :
                  ( ( ~ ( v1_xboole_0 @ D )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ D @ B )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) )
                     => ( ! [F: $i] :
                            ( ( m1_subset_1 @ F @ A )
                           => ( ( r2_hidden @ F @ D )
                             => ( ( k3_funct_2 @ A @ B @ C @ F )
                                = ( k1_funct_1 @ E @ F ) ) ) )
                       => ( ( k2_partfun1 @ A @ B @ C @ D )
                          = E ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ A @ B )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
               => ! [D: $i] :
                    ( ( ~ ( v1_xboole_0 @ D )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ D @ B )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) )
                       => ( ! [F: $i] :
                              ( ( m1_subset_1 @ F @ A )
                             => ( ( r2_hidden @ F @ D )
                               => ( ( k3_funct_2 @ A @ B @ C @ F )
                                  = ( k1_funct_1 @ E @ F ) ) ) )
                         => ( ( k2_partfun1 @ A @ B @ C @ D )
                            = E ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t173_funct_2])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X35: $i,X36: $i] :
      ( ( r1_tarski @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('3',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('5',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r1_tarski @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X32 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( zip_tseitin_0 @ X34 @ X31 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_C @ X0 @ sk_B @ sk_A )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ( zip_tseitin_1 @ sk_B @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_C @ X0 @ sk_B @ sk_A )
      | ( zip_tseitin_1 @ sk_B @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A )
    | ( zip_tseitin_0 @ sk_C @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ X25 @ X26 @ X27 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X26 ) ) )
      | ~ ( zip_tseitin_0 @ X27 @ X28 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('12',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ( ( k2_partfun1 @ X8 @ X9 @ X7 @ X10 )
        = ( k7_relat_1 @ X7 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k7_relat_1 @ sk_C @ X0 ) )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k7_relat_1 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( k7_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A )
    | ( zip_tseitin_0 @ sk_C @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('21',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( v1_funct_2 @ ( k2_partfun1 @ X25 @ X26 @ X27 @ X28 ) @ X28 @ X26 )
      | ~ ( zip_tseitin_0 @ X27 @ X28 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('22',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A )
    | ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k7_relat_1 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('24',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A )
    | ( v1_funct_2 @ ( k7_relat_1 @ sk_C @ sk_D ) @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( k7_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['12','17'])).

thf(t113_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ! [E: $i] :
                ( ( m1_subset_1 @ E @ A )
               => ( ( k1_funct_1 @ C @ E )
                  = ( k1_funct_1 @ D @ E ) ) )
           => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) )).

thf('26',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_2 @ X19 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( r2_relset_1 @ X20 @ X21 @ X22 @ X19 )
      | ( m1_subset_1 @ ( sk_E @ X19 @ X22 @ X20 ) @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t113_funct_2])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_D @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) )
      | ( m1_subset_1 @ ( sk_E @ ( k7_relat_1 @ sk_C @ sk_D ) @ X0 @ sk_D ) @ sk_D )
      | ( r2_relset_1 @ sk_D @ sk_B @ X0 @ ( k7_relat_1 @ sk_C @ sk_D ) )
      | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_C @ sk_D ) @ sk_D @ sk_B )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('29',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X3 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X4 @ X5 @ X3 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k7_relat_1 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('34',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_D @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) )
      | ( m1_subset_1 @ ( sk_E @ ( k7_relat_1 @ sk_C @ sk_D ) @ X0 @ sk_D ) @ sk_D )
      | ( r2_relset_1 @ sk_D @ sk_B @ X0 @ ( k7_relat_1 @ sk_C @ sk_D ) )
      | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_C @ sk_D ) @ sk_D @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_B @ sk_A )
      | ( r2_relset_1 @ sk_D @ sk_B @ X0 @ ( k7_relat_1 @ sk_C @ sk_D ) )
      | ( m1_subset_1 @ ( sk_E @ ( k7_relat_1 @ sk_C @ sk_D ) @ X0 @ sk_D ) @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X0 @ sk_D @ sk_B )
      | ~ ( v1_funct_1 @ X0 )
      | ( zip_tseitin_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_D @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) )
      | ( m1_subset_1 @ ( sk_E @ ( k7_relat_1 @ sk_C @ sk_D ) @ X0 @ sk_D ) @ sk_D )
      | ( r2_relset_1 @ sk_D @ sk_B @ X0 @ ( k7_relat_1 @ sk_C @ sk_D ) )
      | ( zip_tseitin_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A )
    | ( r2_relset_1 @ sk_D @ sk_B @ sk_E_1 @ ( k7_relat_1 @ sk_C @ sk_D ) )
    | ( m1_subset_1 @ ( sk_E @ ( k7_relat_1 @ sk_C @ sk_D ) @ sk_E_1 @ sk_D ) @ sk_D )
    | ~ ( v1_funct_2 @ sk_E_1 @ sk_D @ sk_B )
    | ~ ( v1_funct_1 @ sk_E_1 ) ),
    inference('sup-',[status(thm)],['19','37'])).

thf('39',plain,(
    v1_funct_2 @ sk_E_1 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A )
    | ( r2_relset_1 @ sk_D @ sk_B @ sk_E_1 @ ( k7_relat_1 @ sk_C @ sk_D ) )
    | ( m1_subset_1 @ ( sk_E @ ( k7_relat_1 @ sk_C @ sk_D ) @ sk_E_1 @ sk_D ) @ sk_D ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( k7_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('43',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('44',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( X15 = X18 )
      | ~ ( r2_relset_1 @ X16 @ X17 @ X15 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_D @ sk_B @ sk_E_1 @ X0 )
      | ( sk_E_1 = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A )
    | ( sk_E_1
      = ( k7_relat_1 @ sk_C @ sk_D ) )
    | ~ ( r2_relset_1 @ sk_D @ sk_B @ sk_E_1 @ ( k7_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    ( k2_partfun1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_C @ X0 )
      = ( k7_relat_1 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('49',plain,(
    ( k7_relat_1 @ sk_C @ sk_D )
 != sk_E_1 ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A )
    | ~ ( r2_relset_1 @ sk_D @ sk_B @ sk_E_1 @ ( k7_relat_1 @ sk_C @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['46','49'])).

thf('51',plain,
    ( ( m1_subset_1 @ ( sk_E @ ( k7_relat_1 @ sk_C @ sk_D ) @ sk_E_1 @ sk_D ) @ sk_D )
    | ( zip_tseitin_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['41','50'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('52',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r2_hidden @ X23 @ X24 )
      | ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('53',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( r2_hidden @ ( sk_E @ ( k7_relat_1 @ sk_C @ sk_D ) @ sk_E_1 @ sk_D ) @ sk_D ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( r2_hidden @ ( sk_E @ ( k7_relat_1 @ sk_C @ sk_D ) @ sk_E_1 @ sk_D ) @ sk_D )
    | ( zip_tseitin_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X44: $i] :
      ( ~ ( r2_hidden @ X44 @ sk_D )
      | ( ( k3_funct_2 @ sk_A @ sk_B @ sk_C @ X44 )
        = ( k1_funct_1 @ sk_E_1 @ X44 ) )
      | ~ ( m1_subset_1 @ X44 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('58',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) )
      | ( m1_subset_1 @ X38 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X44: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_B @ sk_C @ X44 )
        = ( k1_funct_1 @ sk_E_1 @ X44 ) )
      | ~ ( r2_hidden @ X44 @ sk_D ) ) ),
    inference(clc,[status(thm)],['56','59'])).

thf('61',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A )
    | ( ( k3_funct_2 @ sk_A @ sk_B @ sk_C @ ( sk_E @ ( k7_relat_1 @ sk_C @ sk_D ) @ sk_E_1 @ sk_D ) )
      = ( k1_funct_1 @ sk_E_1 @ ( sk_E @ ( k7_relat_1 @ sk_C @ sk_D ) @ sk_E_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['55','60'])).

thf('62',plain,
    ( ( r2_hidden @ ( sk_E @ ( k7_relat_1 @ sk_C @ sk_D ) @ sk_E_1 @ sk_D ) @ sk_D )
    | ( zip_tseitin_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('64',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_E @ ( k7_relat_1 @ sk_C @ sk_D ) @ sk_E_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( ( k3_funct_2 @ A @ B @ C @ D )
        = ( k1_funct_1 @ C @ D ) ) ) )).

thf('66',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( v1_funct_2 @ X11 @ X12 @ X13 )
      | ~ ( v1_funct_1 @ X11 )
      | ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ X12 )
      | ( ( k3_funct_2 @ X12 @ X13 @ X11 @ X14 )
        = ( k1_funct_1 @ X11 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A )
    | ( ( k3_funct_2 @ sk_A @ sk_B @ sk_C @ ( sk_E @ ( k7_relat_1 @ sk_C @ sk_D ) @ sk_E_1 @ sk_D ) )
      = ( k1_funct_1 @ sk_C @ ( sk_E @ ( k7_relat_1 @ sk_C @ sk_D ) @ sk_E_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['64','72'])).

thf('74',plain,
    ( ( ( k1_funct_1 @ sk_E_1 @ ( sk_E @ ( k7_relat_1 @ sk_C @ sk_D ) @ sk_E_1 @ sk_D ) )
      = ( k1_funct_1 @ sk_C @ ( sk_E @ ( k7_relat_1 @ sk_C @ sk_D ) @ sk_E_1 @ sk_D ) ) )
    | ( zip_tseitin_1 @ sk_B @ sk_A )
    | ( zip_tseitin_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['61','73'])).

thf('75',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A )
    | ( ( k1_funct_1 @ sk_E_1 @ ( sk_E @ ( k7_relat_1 @ sk_C @ sk_D ) @ sk_E_1 @ sk_D ) )
      = ( k1_funct_1 @ sk_C @ ( sk_E @ ( k7_relat_1 @ sk_C @ sk_D ) @ sk_E_1 @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,
    ( ( r2_hidden @ ( sk_E @ ( k7_relat_1 @ sk_C @ sk_D ) @ sk_E_1 @ sk_D ) @ sk_D )
    | ( zip_tseitin_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['53','54'])).

thf(t72_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ B )
       => ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k1_funct_1 @ C @ A ) ) ) ) )).

thf('77',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X41 @ X42 )
      | ~ ( v1_relat_1 @ X43 )
      | ~ ( v1_funct_1 @ X43 )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X43 @ X42 ) @ X41 )
        = ( k1_funct_1 @ X43 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t72_funct_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_B @ sk_A )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X0 @ sk_D ) @ ( sk_E @ ( k7_relat_1 @ sk_C @ sk_D ) @ sk_E_1 @ sk_D ) )
        = ( k1_funct_1 @ X0 @ ( sk_E @ ( k7_relat_1 @ sk_C @ sk_D ) @ sk_E_1 @ sk_D ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_2 @ X19 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( r2_relset_1 @ X20 @ X21 @ X22 @ X19 )
      | ( ( k1_funct_1 @ X22 @ ( sk_E @ X19 @ X22 @ X20 ) )
       != ( k1_funct_1 @ X19 @ ( sk_E @ X19 @ X22 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t113_funct_2])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_E_1 @ ( sk_E @ ( k7_relat_1 @ sk_C @ sk_D ) @ sk_E_1 @ sk_D ) )
       != ( k1_funct_1 @ sk_C @ ( sk_E @ ( k7_relat_1 @ sk_C @ sk_D ) @ sk_E_1 @ sk_D ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( zip_tseitin_1 @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_E_1 )
      | ~ ( v1_funct_2 @ sk_E_1 @ sk_D @ X0 )
      | ~ ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ X0 ) ) )
      | ( r2_relset_1 @ sk_D @ X0 @ sk_E_1 @ ( k7_relat_1 @ sk_C @ sk_D ) )
      | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_C @ sk_D ) @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('83',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_E_1 @ ( sk_E @ ( k7_relat_1 @ sk_C @ sk_D ) @ sk_E_1 @ sk_D ) )
       != ( k1_funct_1 @ sk_C @ ( sk_E @ ( k7_relat_1 @ sk_C @ sk_D ) @ sk_E_1 @ sk_D ) ) )
      | ( zip_tseitin_1 @ sk_B @ sk_A )
      | ~ ( v1_funct_2 @ sk_E_1 @ sk_D @ X0 )
      | ~ ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ X0 ) ) )
      | ( r2_relset_1 @ sk_D @ X0 @ sk_E_1 @ ( k7_relat_1 @ sk_C @ sk_D ) )
      | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_C @ sk_D ) @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['80','83','84','85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_E_1 @ ( sk_E @ ( k7_relat_1 @ sk_C @ sk_D ) @ sk_E_1 @ sk_D ) )
       != ( k1_funct_1 @ sk_E_1 @ ( sk_E @ ( k7_relat_1 @ sk_C @ sk_D ) @ sk_E_1 @ sk_D ) ) )
      | ( zip_tseitin_1 @ sk_B @ sk_A )
      | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_C @ sk_D ) @ sk_D @ X0 )
      | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ X0 ) ) )
      | ( r2_relset_1 @ sk_D @ X0 @ sk_E_1 @ ( k7_relat_1 @ sk_C @ sk_D ) )
      | ~ ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_E_1 @ sk_D @ X0 )
      | ( zip_tseitin_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_2 @ sk_E_1 @ sk_D @ X0 )
      | ~ ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ X0 ) ) )
      | ( r2_relset_1 @ sk_D @ X0 @ sk_E_1 @ ( k7_relat_1 @ sk_C @ sk_D ) )
      | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_C @ sk_D ) @ sk_D @ X0 )
      | ( zip_tseitin_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A )
    | ( zip_tseitin_1 @ sk_B @ sk_A )
    | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( r2_relset_1 @ sk_D @ sk_B @ sk_E_1 @ ( k7_relat_1 @ sk_C @ sk_D ) )
    | ~ ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_E_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['18','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_funct_2 @ sk_E_1 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A )
    | ( zip_tseitin_1 @ sk_B @ sk_A )
    | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( r2_relset_1 @ sk_D @ sk_B @ sk_E_1 @ ( k7_relat_1 @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,
    ( ( r2_relset_1 @ sk_D @ sk_B @ sk_E_1 @ ( k7_relat_1 @ sk_C @ sk_D ) )
    | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( zip_tseitin_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A )
    | ~ ( r2_relset_1 @ sk_D @ sk_B @ sk_E_1 @ ( k7_relat_1 @ sk_C @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['46','49'])).

thf('96',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A )
    | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_C @ sk_D ) @ sk_D @ sk_B ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A )
    | ( v1_funct_2 @ ( k7_relat_1 @ sk_C @ sk_D ) @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('98',plain,(
    zip_tseitin_1 @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X29: $i,X30: $i] :
      ( ( X29 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('100',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('101',plain,(
    ! [X29: $i,X30: $i] :
      ( ( X29 = o_0_0_xboole_0 )
      | ~ ( zip_tseitin_1 @ X29 @ X30 ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    sk_B = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['98','101'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('103',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('104',plain,(
    $false ),
    inference(demod,[status(thm)],['0','102','103'])).


%------------------------------------------------------------------------------
