%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1053+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9LmKSuA7xC

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 351 expanded)
%              Number of leaves         :   39 ( 129 expanded)
%              Depth                    :   20
%              Number of atoms          :  868 (4173 expanded)
%              Number of equality atoms :   49 ( 204 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(s3_relset_1__e2_192__funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k9_setfam_1 @ A ) ) ) )
        & ( v1_funct_2 @ B @ A @ ( k9_setfam_1 @ A ) )
        & ( v1_funct_1 @ B ) )
     => ( ! [C: $i] :
            ( ( m1_subset_1 @ C @ A )
           => ( ( r2_hidden @ C @ ( k2_subset_1 @ A ) )
             => ( r1_tarski @ ( k1_funct_1 @ B @ C ) @ ( k2_subset_1 @ A ) ) ) )
       => ? [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_subset_1 @ A ) @ ( k2_subset_1 @ A ) ) ) )
            & ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ ( k2_subset_1 @ A ) )
                 => ( ( k11_relat_1 @ C @ D )
                    = ( k1_funct_1 @ B @ D ) ) ) ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( ( r2_hidden @ C @ ( k2_subset_1 @ A ) )
       => ( r1_tarski @ ( k1_funct_1 @ B @ C ) @ ( k2_subset_1 @ A ) ) )
     => ( zip_tseitin_0 @ C @ B @ A ) ) )).

thf('0',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( zip_tseitin_0 @ X3 @ X4 @ X5 )
      | ( r2_hidden @ X3 @ ( k2_subset_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('2',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( zip_tseitin_0 @ X3 @ X4 @ X5 )
      | ( r2_hidden @ X3 @ X5 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t170_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ ( k9_setfam_1 @ A ) )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k9_setfam_1 @ A ) ) ) ) )
     => ? [C: $i] :
          ( ! [D: $i] :
              ( ( r2_hidden @ D @ A )
             => ( ( k11_relat_1 @ C @ D )
                = ( k1_funct_1 @ B @ D ) ) )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ ( k9_setfam_1 @ A ) )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k9_setfam_1 @ A ) ) ) ) )
       => ? [C: $i] :
            ( ! [D: $i] :
                ( ( r2_hidden @ D @ A )
               => ( ( k11_relat_1 @ C @ D )
                  = ( k1_funct_1 @ B @ D ) ) )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t170_funct_2])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k9_setfam_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X2: $i] :
      ( ( k9_setfam_1 @ X2 )
      = ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('6',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ( X23 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X24 @ X21 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_B @ sk_A @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k1_zfmisc_1 @ sk_A )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_2 @ sk_B @ sk_A @ ( k9_setfam_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('9',plain,(
    ! [X2: $i] :
      ( ( k9_setfam_1 @ X2 )
      = ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('10',plain,(
    v1_funct_2 @ sk_B @ sk_A @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) )
      | ( ( k1_zfmisc_1 @ sk_A )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 @ sk_A )
      | ( ( k1_zfmisc_1 @ sk_A )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','12'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ X15 @ X16 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_zfmisc_1 @ sk_A )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X1 @ sk_A )
      | ( m1_subset_1 @ ( k1_funct_1 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 @ sk_A )
      | ( ( k1_zfmisc_1 @ sk_A )
        = k1_xboole_0 )
      | ( r1_tarski @ ( k1_funct_1 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( zip_tseitin_0 @ X3 @ X4 @ X5 )
      | ~ ( r1_tarski @ ( k1_funct_1 @ X4 @ X3 ) @ ( k2_subset_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('20',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( zip_tseitin_0 @ X3 @ X4 @ X5 )
      | ~ ( r1_tarski @ ( k1_funct_1 @ X4 @ X3 ) @ X5 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_zfmisc_1 @ sk_A )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X1 @ sk_A )
      | ( zip_tseitin_0 @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k1_zfmisc_1 @ sk_A )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ sk_B @ sk_A ) ) ),
    inference(condensation,[status(thm)],['21'])).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( ( m1_subset_1 @ C @ A )
       => ( zip_tseitin_0 @ C @ B @ A ) )
     => ( zip_tseitin_1 @ C @ B @ A ) ) )).

thf('23',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( zip_tseitin_1 @ X6 @ X7 @ X8 )
      | ~ ( zip_tseitin_0 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k1_zfmisc_1 @ sk_A )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(zf_stmt_3,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ! [D: $i] :
            ( ( m1_subset_1 @ D @ A )
           => ( ( r2_hidden @ D @ ( k2_subset_1 @ A ) )
             => ( ( k11_relat_1 @ C @ D )
                = ( k1_funct_1 @ B @ D ) ) ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_subset_1 @ A ) @ ( k2_subset_1 @ A ) ) ) ) ) ) )).

thf(zf_stmt_5,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_6,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ ( k9_setfam_1 @ A ) )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k9_setfam_1 @ A ) ) ) ) )
     => ( ! [C: $i] :
            ( zip_tseitin_1 @ C @ B @ A )
       => ? [C: $i] :
            ( zip_tseitin_2 @ C @ B @ A ) ) ) )).

thf('26',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_C @ X13 @ X14 ) @ X13 @ X14 )
      | ( zip_tseitin_2 @ ( sk_C_1 @ X13 @ X14 ) @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ ( k9_setfam_1 @ X14 ) ) ) )
      | ~ ( v1_funct_2 @ X13 @ X14 @ ( k9_setfam_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('27',plain,(
    ! [X2: $i] :
      ( ( k9_setfam_1 @ X2 )
      = ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('28',plain,(
    ! [X2: $i] :
      ( ( k9_setfam_1 @ X2 )
      = ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('29',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_C @ X13 @ X14 ) @ X13 @ X14 )
      | ( zip_tseitin_2 @ ( sk_C_1 @ X13 @ X14 ) @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ ( k1_zfmisc_1 @ X14 ) ) ) )
      | ~ ( v1_funct_2 @ X13 @ X14 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ ( k1_zfmisc_1 @ sk_A ) )
    | ( zip_tseitin_2 @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_B @ sk_A )
    | ~ ( zip_tseitin_1 @ ( sk_C @ sk_B @ sk_A ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('32',plain,(
    v1_funct_2 @ sk_B @ sk_A @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('33',plain,
    ( ( zip_tseitin_2 @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_B @ sk_A )
    | ~ ( zip_tseitin_1 @ ( sk_C @ sk_B @ sk_A ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ( ( k1_zfmisc_1 @ sk_A )
      = k1_xboole_0 )
    | ( zip_tseitin_2 @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['24','33'])).

thf('35',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_subset_1 @ X10 ) @ ( k2_subset_1 @ X10 ) ) ) )
      | ~ ( zip_tseitin_2 @ X12 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('38',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X10 ) ) )
      | ~ ( zip_tseitin_2 @ X12 @ X11 @ X10 ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ( ( k1_zfmisc_1 @ sk_A )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,(
    ! [X25: $i] :
      ( ( r2_hidden @ ( sk_D @ X25 ) @ sk_A )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('41',plain,
    ( ( ( k1_zfmisc_1 @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_D @ ( sk_C_1 @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k1_zfmisc_1 @ sk_A )
      = k1_xboole_0 )
    | ( zip_tseitin_2 @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['24','33'])).

thf('43',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ X10 )
      | ( ( k11_relat_1 @ X12 @ X9 )
        = ( k1_funct_1 @ X11 @ X9 ) )
      | ~ ( r2_hidden @ X9 @ ( k2_subset_1 @ X10 ) )
      | ~ ( zip_tseitin_2 @ X12 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('45',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ X10 )
      | ( ( k11_relat_1 @ X12 @ X9 )
        = ( k1_funct_1 @ X11 @ X9 ) )
      | ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( zip_tseitin_2 @ X12 @ X11 @ X10 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k1_zfmisc_1 @ sk_A )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( k11_relat_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ X0 )
        = ( k1_funct_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,
    ( ( ( k1_zfmisc_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( m1_subset_1 @ ( sk_D @ ( sk_C_1 @ sk_B @ sk_A ) ) @ sk_A )
    | ( ( k11_relat_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( sk_D @ ( sk_C_1 @ sk_B @ sk_A ) ) )
      = ( k1_funct_1 @ sk_B @ ( sk_D @ ( sk_C_1 @ sk_B @ sk_A ) ) ) )
    | ( ( k1_zfmisc_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,
    ( ( ( k11_relat_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( sk_D @ ( sk_C_1 @ sk_B @ sk_A ) ) )
      = ( k1_funct_1 @ sk_B @ ( sk_D @ ( sk_C_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( m1_subset_1 @ ( sk_D @ ( sk_C_1 @ sk_B @ sk_A ) ) @ sk_A )
    | ( ( k1_zfmisc_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( ( k1_zfmisc_1 @ sk_A )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('50',plain,(
    ! [X25: $i] :
      ( ( ( k11_relat_1 @ X25 @ ( sk_D @ X25 ) )
       != ( k1_funct_1 @ sk_B @ ( sk_D @ X25 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('51',plain,
    ( ( ( k1_zfmisc_1 @ sk_A )
      = k1_xboole_0 )
    | ( ( k11_relat_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( sk_D @ ( sk_C_1 @ sk_B @ sk_A ) ) )
     != ( k1_funct_1 @ sk_B @ ( sk_D @ ( sk_C_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( k1_zfmisc_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( m1_subset_1 @ ( sk_D @ ( sk_C_1 @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference(clc,[status(thm)],['48','51'])).

thf('53',plain,
    ( ( ( k1_zfmisc_1 @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_D @ ( sk_C_1 @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('54',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ X15 @ X16 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('55',plain,
    ( ( ( k1_zfmisc_1 @ sk_A )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_D @ ( sk_C_1 @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k1_zfmisc_1 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['52','55'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('57',plain,(
    ! [X1: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('58',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('59',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('60',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('61',plain,(
    ! [X20: $i] :
      ( ( X20 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('62',plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['59','62'])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['58','63'])).


%------------------------------------------------------------------------------
