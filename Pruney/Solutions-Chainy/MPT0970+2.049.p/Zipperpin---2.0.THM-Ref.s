%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9NwbJAaaCP

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:23 EST 2020

% Result     : Theorem 5.21s
% Output     : Refutation 5.21s
% Verified   : 
% Statistics : Number of formulae       :  153 (3162 expanded)
%              Number of leaves         :   40 ( 947 expanded)
%              Depth                    :   29
%              Number of atoms          : 1042 (42051 expanded)
%              Number of equality atoms :  111 (2766 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(t16_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( ( r2_hidden @ E @ A )
                    & ( D
                      = ( k1_funct_1 @ C @ E ) ) ) )
       => ( ( k2_relset_1 @ A @ B @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ! [D: $i] :
              ~ ( ( r2_hidden @ D @ B )
                & ! [E: $i] :
                    ~ ( ( r2_hidden @ E @ A )
                      & ( D
                        = ( k1_funct_1 @ C @ E ) ) ) )
         => ( ( k2_relset_1 @ A @ B @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t16_funct_2])).

thf('0',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('1',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ( X24
        = ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('5',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v5_relat_1 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('9',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('13',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('16',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['11','16'])).

thf(t19_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ ( k1_relat_1 @ B ) )
                    & ( C
                      = ( k1_funct_1 @ B @ D ) ) ) )
       => ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) ) ) )).

thf('18',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ ( sk_C @ X10 @ X11 ) @ X11 )
      | ( r1_tarski @ X11 @ ( k2_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t19_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( ( k2_relat_1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = sk_B )
    | ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('24',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = sk_B )
    | ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('27',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('28',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != sk_B ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,(
    r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X30: $i] :
      ( ~ ( r2_hidden @ X30 @ sk_B )
      | ( X30
        = ( k1_funct_1 @ sk_C_1 @ ( sk_E @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_C @ sk_C_1 @ sk_B )
    = ( k1_funct_1 @ sk_C_1 @ ( sk_E @ ( sk_C @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('33',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('34',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('35',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('36',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('39',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( sk_C @ X10 @ X11 )
       != ( k1_funct_1 @ X10 @ X12 ) )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X10 ) )
      | ( r1_tarski @ X11 @ ( k2_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t19_funct_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( r1_tarski @ X1 @ ( k2_relat_1 @ sk_C_1 ) )
      | ( ( sk_C @ sk_C_1 @ X1 )
       != ( k1_funct_1 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('43',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k2_relat_1 @ sk_C_1 ) )
      | ( ( sk_C @ sk_C_1 @ X1 )
       != ( k1_funct_1 @ sk_C_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ sk_C_1 @ X0 )
       != ( sk_C @ sk_C_1 @ sk_B ) )
      | ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_E @ ( sk_C @ sk_C_1 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','44'])).

thf('46',plain,(
    r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['24','29'])).

thf('47',plain,(
    ! [X30: $i] :
      ( ~ ( r2_hidden @ X30 @ sk_B )
      | ( r2_hidden @ ( sk_E @ X30 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    r2_hidden @ ( sk_E @ ( sk_C @ sk_C_1 @ sk_B ) ) @ sk_A ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ sk_C_1 @ X0 )
       != ( sk_C @ sk_C_1 @ sk_B ) )
      | ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference(eq_res,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('52',plain,
    ( ( sk_B = k1_xboole_0 )
    | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B )
    | ( ( k2_relat_1 @ sk_C_1 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['11','16'])).

thf('54',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C_1 )
      = sk_B ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != sk_B ),
    inference(demod,[status(thm)],['25','28'])).

thf('56',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ k1_xboole_0 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['6','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['54','55'])).

thf('60',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( X27 != k1_xboole_0 )
      | ( X28 = k1_xboole_0 )
      | ( X29 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X29 @ X28 @ X27 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('62',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X28 @ k1_xboole_0 )
      | ( X29 = k1_xboole_0 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf('64',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['54','55'])).

thf('66',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','66'])).

thf('68',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != sk_B ),
    inference(demod,[status(thm)],['25','28'])).

thf('69',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['54','55'])).

thf('70',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('72',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('73',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['73'])).

thf('76',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['57','74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('78',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['73'])).

thf('79',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('81',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('83',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X23 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('84',plain,(
    ! [X22: $i] :
      ( zip_tseitin_0 @ X22 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['82','84'])).

thf('86',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('90',plain,(
    ! [X9: $i] :
      ( ( ( k1_relat_1 @ X9 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X9 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( sk_A != k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_A @ X0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( ( k2_relat_1 @ sk_C_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( sk_A != k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_A @ X0 )
      | ( ( k2_relat_1 @ sk_C_1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_C_1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_A @ X0 ) ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != sk_B ),
    inference(demod,[status(thm)],['25','28'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != sk_B )
      | ( zip_tseitin_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['54','55'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_A @ X0 ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['73'])).

thf('102',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    zip_tseitin_1 @ sk_C_1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['81','102'])).

thf('104',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['76','103'])).

thf('105',plain,(
    ! [X9: $i] :
      ( ( ( k1_relat_1 @ X9 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X9 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('106',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('108',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['68','69'])).

thf('111',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['109','110'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9NwbJAaaCP
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:06:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 5.21/5.41  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.21/5.41  % Solved by: fo/fo7.sh
% 5.21/5.41  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.21/5.41  % done 4218 iterations in 4.956s
% 5.21/5.41  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.21/5.41  % SZS output start Refutation
% 5.21/5.41  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.21/5.41  thf(sk_E_type, type, sk_E: $i > $i).
% 5.21/5.41  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 5.21/5.41  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.21/5.41  thf(sk_C_1_type, type, sk_C_1: $i).
% 5.21/5.41  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.21/5.41  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 5.21/5.41  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 5.21/5.41  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 5.21/5.41  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 5.21/5.41  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 5.21/5.41  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.21/5.41  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.21/5.41  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.21/5.41  thf(sk_A_type, type, sk_A: $i).
% 5.21/5.41  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 5.21/5.41  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.21/5.41  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 5.21/5.41  thf(sk_B_type, type, sk_B: $i).
% 5.21/5.41  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 5.21/5.41  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 5.21/5.41  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 5.21/5.41  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 5.21/5.41  thf(t16_funct_2, conjecture,
% 5.21/5.41    (![A:$i,B:$i,C:$i]:
% 5.21/5.41     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.21/5.41         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.21/5.41       ( ( ![D:$i]:
% 5.21/5.41           ( ~( ( r2_hidden @ D @ B ) & 
% 5.21/5.41                ( ![E:$i]:
% 5.21/5.41                  ( ~( ( r2_hidden @ E @ A ) & 
% 5.21/5.41                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 5.21/5.41         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 5.21/5.41  thf(zf_stmt_0, negated_conjecture,
% 5.21/5.41    (~( ![A:$i,B:$i,C:$i]:
% 5.21/5.41        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.21/5.41            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.21/5.41          ( ( ![D:$i]:
% 5.21/5.41              ( ~( ( r2_hidden @ D @ B ) & 
% 5.21/5.41                   ( ![E:$i]:
% 5.21/5.41                     ( ~( ( r2_hidden @ E @ A ) & 
% 5.21/5.41                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 5.21/5.41            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 5.21/5.41    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 5.21/5.41  thf('0', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 5.21/5.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.41  thf(d1_funct_2, axiom,
% 5.21/5.41    (![A:$i,B:$i,C:$i]:
% 5.21/5.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.21/5.41       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 5.21/5.41           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 5.21/5.41             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 5.21/5.41         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 5.21/5.41           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 5.21/5.41             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 5.21/5.41  thf(zf_stmt_1, axiom,
% 5.21/5.41    (![C:$i,B:$i,A:$i]:
% 5.21/5.41     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 5.21/5.41       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 5.21/5.41  thf('1', plain,
% 5.21/5.41      (![X24 : $i, X25 : $i, X26 : $i]:
% 5.21/5.41         (~ (v1_funct_2 @ X26 @ X24 @ X25)
% 5.21/5.41          | ((X24) = (k1_relset_1 @ X24 @ X25 @ X26))
% 5.21/5.41          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 5.21/5.41      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.21/5.41  thf('2', plain,
% 5.21/5.41      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 5.21/5.41        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 5.21/5.41      inference('sup-', [status(thm)], ['0', '1'])).
% 5.21/5.41  thf('3', plain,
% 5.21/5.41      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.21/5.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.41  thf(redefinition_k1_relset_1, axiom,
% 5.21/5.41    (![A:$i,B:$i,C:$i]:
% 5.21/5.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.21/5.41       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 5.21/5.41  thf('4', plain,
% 5.21/5.41      (![X16 : $i, X17 : $i, X18 : $i]:
% 5.21/5.41         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 5.21/5.41          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 5.21/5.41      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 5.21/5.41  thf('5', plain,
% 5.21/5.41      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 5.21/5.41      inference('sup-', [status(thm)], ['3', '4'])).
% 5.21/5.41  thf('6', plain,
% 5.21/5.41      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 5.21/5.41        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 5.21/5.41      inference('demod', [status(thm)], ['2', '5'])).
% 5.21/5.41  thf('7', plain,
% 5.21/5.41      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.21/5.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.41  thf(cc2_relset_1, axiom,
% 5.21/5.41    (![A:$i,B:$i,C:$i]:
% 5.21/5.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.21/5.41       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 5.21/5.41  thf('8', plain,
% 5.21/5.41      (![X13 : $i, X14 : $i, X15 : $i]:
% 5.21/5.41         ((v5_relat_1 @ X13 @ X15)
% 5.21/5.41          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 5.21/5.41      inference('cnf', [status(esa)], [cc2_relset_1])).
% 5.21/5.41  thf('9', plain, ((v5_relat_1 @ sk_C_1 @ sk_B)),
% 5.21/5.41      inference('sup-', [status(thm)], ['7', '8'])).
% 5.21/5.41  thf(d19_relat_1, axiom,
% 5.21/5.41    (![A:$i,B:$i]:
% 5.21/5.41     ( ( v1_relat_1 @ B ) =>
% 5.21/5.41       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 5.21/5.41  thf('10', plain,
% 5.21/5.41      (![X5 : $i, X6 : $i]:
% 5.21/5.41         (~ (v5_relat_1 @ X5 @ X6)
% 5.21/5.41          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 5.21/5.41          | ~ (v1_relat_1 @ X5))),
% 5.21/5.41      inference('cnf', [status(esa)], [d19_relat_1])).
% 5.21/5.41  thf('11', plain,
% 5.21/5.41      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B))),
% 5.21/5.41      inference('sup-', [status(thm)], ['9', '10'])).
% 5.21/5.41  thf('12', plain,
% 5.21/5.41      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.21/5.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.41  thf(cc2_relat_1, axiom,
% 5.21/5.41    (![A:$i]:
% 5.21/5.41     ( ( v1_relat_1 @ A ) =>
% 5.21/5.41       ( ![B:$i]:
% 5.21/5.41         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 5.21/5.41  thf('13', plain,
% 5.21/5.41      (![X3 : $i, X4 : $i]:
% 5.21/5.41         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 5.21/5.41          | (v1_relat_1 @ X3)
% 5.21/5.41          | ~ (v1_relat_1 @ X4))),
% 5.21/5.41      inference('cnf', [status(esa)], [cc2_relat_1])).
% 5.21/5.41  thf('14', plain,
% 5.21/5.41      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_1))),
% 5.21/5.41      inference('sup-', [status(thm)], ['12', '13'])).
% 5.21/5.41  thf(fc6_relat_1, axiom,
% 5.21/5.41    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 5.21/5.41  thf('15', plain,
% 5.21/5.41      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 5.21/5.41      inference('cnf', [status(esa)], [fc6_relat_1])).
% 5.21/5.41  thf('16', plain, ((v1_relat_1 @ sk_C_1)),
% 5.21/5.41      inference('demod', [status(thm)], ['14', '15'])).
% 5.21/5.41  thf('17', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B)),
% 5.21/5.41      inference('demod', [status(thm)], ['11', '16'])).
% 5.21/5.41  thf(t19_funct_1, axiom,
% 5.21/5.41    (![A:$i,B:$i]:
% 5.21/5.41     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 5.21/5.41       ( ( ![C:$i]:
% 5.21/5.41           ( ~( ( r2_hidden @ C @ A ) & 
% 5.21/5.41                ( ![D:$i]:
% 5.21/5.41                  ( ~( ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) & 
% 5.21/5.41                       ( ( C ) = ( k1_funct_1 @ B @ D ) ) ) ) ) ) ) ) =>
% 5.21/5.41         ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) ) ))).
% 5.21/5.41  thf('18', plain,
% 5.21/5.41      (![X10 : $i, X11 : $i]:
% 5.21/5.41         ((r2_hidden @ (sk_C @ X10 @ X11) @ X11)
% 5.21/5.41          | (r1_tarski @ X11 @ (k2_relat_1 @ X10))
% 5.21/5.41          | ~ (v1_funct_1 @ X10)
% 5.21/5.41          | ~ (v1_relat_1 @ X10))),
% 5.21/5.41      inference('cnf', [status(esa)], [t19_funct_1])).
% 5.21/5.41  thf(d10_xboole_0, axiom,
% 5.21/5.41    (![A:$i,B:$i]:
% 5.21/5.41     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.21/5.41  thf('19', plain,
% 5.21/5.41      (![X0 : $i, X2 : $i]:
% 5.21/5.41         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 5.21/5.41      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.21/5.41  thf('20', plain,
% 5.21/5.41      (![X0 : $i, X1 : $i]:
% 5.21/5.41         (~ (v1_relat_1 @ X0)
% 5.21/5.41          | ~ (v1_funct_1 @ X0)
% 5.21/5.41          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 5.21/5.41          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 5.21/5.41          | ((k2_relat_1 @ X0) = (X1)))),
% 5.21/5.41      inference('sup-', [status(thm)], ['18', '19'])).
% 5.21/5.41  thf('21', plain,
% 5.21/5.41      ((((k2_relat_1 @ sk_C_1) = (sk_B))
% 5.21/5.41        | (r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ sk_B)
% 5.21/5.41        | ~ (v1_funct_1 @ sk_C_1)
% 5.21/5.41        | ~ (v1_relat_1 @ sk_C_1))),
% 5.21/5.41      inference('sup-', [status(thm)], ['17', '20'])).
% 5.21/5.41  thf('22', plain, ((v1_funct_1 @ sk_C_1)),
% 5.21/5.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.41  thf('23', plain, ((v1_relat_1 @ sk_C_1)),
% 5.21/5.41      inference('demod', [status(thm)], ['14', '15'])).
% 5.21/5.41  thf('24', plain,
% 5.21/5.41      ((((k2_relat_1 @ sk_C_1) = (sk_B))
% 5.21/5.41        | (r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ sk_B))),
% 5.21/5.41      inference('demod', [status(thm)], ['21', '22', '23'])).
% 5.21/5.41  thf('25', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B))),
% 5.21/5.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.41  thf('26', plain,
% 5.21/5.41      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.21/5.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.41  thf(redefinition_k2_relset_1, axiom,
% 5.21/5.41    (![A:$i,B:$i,C:$i]:
% 5.21/5.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.21/5.41       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 5.21/5.41  thf('27', plain,
% 5.21/5.41      (![X19 : $i, X20 : $i, X21 : $i]:
% 5.21/5.41         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 5.21/5.41          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 5.21/5.41      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 5.21/5.41  thf('28', plain,
% 5.21/5.41      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 5.21/5.41      inference('sup-', [status(thm)], ['26', '27'])).
% 5.21/5.41  thf('29', plain, (((k2_relat_1 @ sk_C_1) != (sk_B))),
% 5.21/5.41      inference('demod', [status(thm)], ['25', '28'])).
% 5.21/5.41  thf('30', plain, ((r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ sk_B)),
% 5.21/5.41      inference('simplify_reflect-', [status(thm)], ['24', '29'])).
% 5.21/5.41  thf('31', plain,
% 5.21/5.41      (![X30 : $i]:
% 5.21/5.41         (~ (r2_hidden @ X30 @ sk_B)
% 5.21/5.41          | ((X30) = (k1_funct_1 @ sk_C_1 @ (sk_E @ X30))))),
% 5.21/5.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.41  thf('32', plain,
% 5.21/5.41      (((sk_C @ sk_C_1 @ sk_B)
% 5.21/5.41         = (k1_funct_1 @ sk_C_1 @ (sk_E @ (sk_C @ sk_C_1 @ sk_B))))),
% 5.21/5.41      inference('sup-', [status(thm)], ['30', '31'])).
% 5.21/5.41  thf(zf_stmt_2, axiom,
% 5.21/5.41    (![B:$i,A:$i]:
% 5.21/5.41     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 5.21/5.41       ( zip_tseitin_0 @ B @ A ) ))).
% 5.21/5.41  thf('33', plain,
% 5.21/5.41      (![X22 : $i, X23 : $i]:
% 5.21/5.41         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 5.21/5.41      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.21/5.41  thf('34', plain,
% 5.21/5.41      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.21/5.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.41  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 5.21/5.41  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 5.21/5.41  thf(zf_stmt_5, axiom,
% 5.21/5.41    (![A:$i,B:$i,C:$i]:
% 5.21/5.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.21/5.41       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 5.21/5.41         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 5.21/5.41           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 5.21/5.41             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 5.21/5.41  thf('35', plain,
% 5.21/5.41      (![X27 : $i, X28 : $i, X29 : $i]:
% 5.21/5.41         (~ (zip_tseitin_0 @ X27 @ X28)
% 5.21/5.41          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 5.21/5.41          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 5.21/5.41      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.21/5.41  thf('36', plain,
% 5.21/5.41      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 5.21/5.41        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 5.21/5.41      inference('sup-', [status(thm)], ['34', '35'])).
% 5.21/5.41  thf('37', plain,
% 5.21/5.41      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 5.21/5.41      inference('sup-', [status(thm)], ['33', '36'])).
% 5.21/5.41  thf('38', plain,
% 5.21/5.41      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 5.21/5.41        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 5.21/5.41      inference('demod', [status(thm)], ['2', '5'])).
% 5.21/5.41  thf('39', plain,
% 5.21/5.41      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 5.21/5.41      inference('sup-', [status(thm)], ['37', '38'])).
% 5.21/5.41  thf('40', plain,
% 5.21/5.41      (![X10 : $i, X11 : $i, X12 : $i]:
% 5.21/5.41         (((sk_C @ X10 @ X11) != (k1_funct_1 @ X10 @ X12))
% 5.21/5.41          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ X10))
% 5.21/5.41          | (r1_tarski @ X11 @ (k2_relat_1 @ X10))
% 5.21/5.41          | ~ (v1_funct_1 @ X10)
% 5.21/5.41          | ~ (v1_relat_1 @ X10))),
% 5.21/5.41      inference('cnf', [status(esa)], [t19_funct_1])).
% 5.21/5.41  thf('41', plain,
% 5.21/5.41      (![X0 : $i, X1 : $i]:
% 5.21/5.41         (~ (r2_hidden @ X0 @ sk_A)
% 5.21/5.41          | ((sk_B) = (k1_xboole_0))
% 5.21/5.41          | ~ (v1_relat_1 @ sk_C_1)
% 5.21/5.41          | ~ (v1_funct_1 @ sk_C_1)
% 5.21/5.41          | (r1_tarski @ X1 @ (k2_relat_1 @ sk_C_1))
% 5.21/5.41          | ((sk_C @ sk_C_1 @ X1) != (k1_funct_1 @ sk_C_1 @ X0)))),
% 5.21/5.41      inference('sup-', [status(thm)], ['39', '40'])).
% 5.21/5.41  thf('42', plain, ((v1_relat_1 @ sk_C_1)),
% 5.21/5.41      inference('demod', [status(thm)], ['14', '15'])).
% 5.21/5.41  thf('43', plain, ((v1_funct_1 @ sk_C_1)),
% 5.21/5.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.41  thf('44', plain,
% 5.21/5.41      (![X0 : $i, X1 : $i]:
% 5.21/5.41         (~ (r2_hidden @ X0 @ sk_A)
% 5.21/5.41          | ((sk_B) = (k1_xboole_0))
% 5.21/5.41          | (r1_tarski @ X1 @ (k2_relat_1 @ sk_C_1))
% 5.21/5.41          | ((sk_C @ sk_C_1 @ X1) != (k1_funct_1 @ sk_C_1 @ X0)))),
% 5.21/5.41      inference('demod', [status(thm)], ['41', '42', '43'])).
% 5.21/5.41  thf('45', plain,
% 5.21/5.41      (![X0 : $i]:
% 5.21/5.41         (((sk_C @ sk_C_1 @ X0) != (sk_C @ sk_C_1 @ sk_B))
% 5.21/5.41          | (r1_tarski @ X0 @ (k2_relat_1 @ sk_C_1))
% 5.21/5.41          | ((sk_B) = (k1_xboole_0))
% 5.21/5.41          | ~ (r2_hidden @ (sk_E @ (sk_C @ sk_C_1 @ sk_B)) @ sk_A))),
% 5.21/5.41      inference('sup-', [status(thm)], ['32', '44'])).
% 5.21/5.41  thf('46', plain, ((r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ sk_B)),
% 5.21/5.41      inference('simplify_reflect-', [status(thm)], ['24', '29'])).
% 5.21/5.41  thf('47', plain,
% 5.21/5.41      (![X30 : $i]:
% 5.21/5.41         (~ (r2_hidden @ X30 @ sk_B) | (r2_hidden @ (sk_E @ X30) @ sk_A))),
% 5.21/5.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.41  thf('48', plain, ((r2_hidden @ (sk_E @ (sk_C @ sk_C_1 @ sk_B)) @ sk_A)),
% 5.21/5.41      inference('sup-', [status(thm)], ['46', '47'])).
% 5.21/5.41  thf('49', plain,
% 5.21/5.41      (![X0 : $i]:
% 5.21/5.41         (((sk_C @ sk_C_1 @ X0) != (sk_C @ sk_C_1 @ sk_B))
% 5.21/5.41          | (r1_tarski @ X0 @ (k2_relat_1 @ sk_C_1))
% 5.21/5.41          | ((sk_B) = (k1_xboole_0)))),
% 5.21/5.41      inference('demod', [status(thm)], ['45', '48'])).
% 5.21/5.41  thf('50', plain,
% 5.21/5.41      ((((sk_B) = (k1_xboole_0)) | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1)))),
% 5.21/5.41      inference('eq_res', [status(thm)], ['49'])).
% 5.21/5.41  thf('51', plain,
% 5.21/5.41      (![X0 : $i, X2 : $i]:
% 5.21/5.41         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 5.21/5.41      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.21/5.41  thf('52', plain,
% 5.21/5.41      ((((sk_B) = (k1_xboole_0))
% 5.21/5.41        | ~ (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B)
% 5.21/5.41        | ((k2_relat_1 @ sk_C_1) = (sk_B)))),
% 5.21/5.41      inference('sup-', [status(thm)], ['50', '51'])).
% 5.21/5.41  thf('53', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B)),
% 5.21/5.41      inference('demod', [status(thm)], ['11', '16'])).
% 5.21/5.41  thf('54', plain,
% 5.21/5.41      ((((sk_B) = (k1_xboole_0)) | ((k2_relat_1 @ sk_C_1) = (sk_B)))),
% 5.21/5.41      inference('demod', [status(thm)], ['52', '53'])).
% 5.21/5.41  thf('55', plain, (((k2_relat_1 @ sk_C_1) != (sk_B))),
% 5.21/5.41      inference('demod', [status(thm)], ['25', '28'])).
% 5.21/5.41  thf('56', plain, (((sk_B) = (k1_xboole_0))),
% 5.21/5.41      inference('simplify_reflect-', [status(thm)], ['54', '55'])).
% 5.21/5.41  thf('57', plain,
% 5.21/5.41      ((~ (zip_tseitin_1 @ sk_C_1 @ k1_xboole_0 @ sk_A)
% 5.21/5.41        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 5.21/5.41      inference('demod', [status(thm)], ['6', '56'])).
% 5.21/5.41  thf('58', plain,
% 5.21/5.41      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.21/5.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.41  thf('59', plain, (((sk_B) = (k1_xboole_0))),
% 5.21/5.41      inference('simplify_reflect-', [status(thm)], ['54', '55'])).
% 5.21/5.41  thf('60', plain,
% 5.21/5.41      ((m1_subset_1 @ sk_C_1 @ 
% 5.21/5.41        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 5.21/5.41      inference('demod', [status(thm)], ['58', '59'])).
% 5.21/5.41  thf('61', plain,
% 5.21/5.41      (![X27 : $i, X28 : $i, X29 : $i]:
% 5.21/5.41         (((X27) != (k1_xboole_0))
% 5.21/5.41          | ((X28) = (k1_xboole_0))
% 5.21/5.41          | ((X29) = (k1_xboole_0))
% 5.21/5.41          | ~ (v1_funct_2 @ X29 @ X28 @ X27)
% 5.21/5.41          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 5.21/5.41      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.21/5.41  thf('62', plain,
% 5.21/5.41      (![X28 : $i, X29 : $i]:
% 5.21/5.41         (~ (m1_subset_1 @ X29 @ 
% 5.21/5.41             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ k1_xboole_0)))
% 5.21/5.41          | ~ (v1_funct_2 @ X29 @ X28 @ k1_xboole_0)
% 5.21/5.41          | ((X29) = (k1_xboole_0))
% 5.21/5.41          | ((X28) = (k1_xboole_0)))),
% 5.21/5.41      inference('simplify', [status(thm)], ['61'])).
% 5.21/5.41  thf('63', plain,
% 5.21/5.41      ((((sk_A) = (k1_xboole_0))
% 5.21/5.41        | ((sk_C_1) = (k1_xboole_0))
% 5.21/5.41        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ k1_xboole_0))),
% 5.21/5.41      inference('sup-', [status(thm)], ['60', '62'])).
% 5.21/5.41  thf('64', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 5.21/5.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.21/5.41  thf('65', plain, (((sk_B) = (k1_xboole_0))),
% 5.21/5.41      inference('simplify_reflect-', [status(thm)], ['54', '55'])).
% 5.21/5.41  thf('66', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ k1_xboole_0)),
% 5.21/5.41      inference('demod', [status(thm)], ['64', '65'])).
% 5.21/5.41  thf('67', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_C_1) = (k1_xboole_0)))),
% 5.21/5.41      inference('demod', [status(thm)], ['63', '66'])).
% 5.21/5.41  thf('68', plain, (((k2_relat_1 @ sk_C_1) != (sk_B))),
% 5.21/5.41      inference('demod', [status(thm)], ['25', '28'])).
% 5.21/5.41  thf('69', plain, (((sk_B) = (k1_xboole_0))),
% 5.21/5.41      inference('simplify_reflect-', [status(thm)], ['54', '55'])).
% 5.21/5.41  thf('70', plain, (((k2_relat_1 @ sk_C_1) != (k1_xboole_0))),
% 5.21/5.41      inference('demod', [status(thm)], ['68', '69'])).
% 5.21/5.41  thf('71', plain,
% 5.21/5.41      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 5.21/5.41        | ((sk_A) = (k1_xboole_0)))),
% 5.21/5.41      inference('sup-', [status(thm)], ['67', '70'])).
% 5.21/5.41  thf(t60_relat_1, axiom,
% 5.21/5.41    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 5.21/5.41     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 5.21/5.41  thf('72', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 5.21/5.41      inference('cnf', [status(esa)], [t60_relat_1])).
% 5.21/5.41  thf('73', plain,
% 5.21/5.41      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 5.21/5.41      inference('demod', [status(thm)], ['71', '72'])).
% 5.21/5.41  thf('74', plain, (((sk_A) = (k1_xboole_0))),
% 5.21/5.41      inference('simplify', [status(thm)], ['73'])).
% 5.21/5.41  thf('75', plain, (((sk_A) = (k1_xboole_0))),
% 5.21/5.41      inference('simplify', [status(thm)], ['73'])).
% 5.21/5.41  thf('76', plain,
% 5.21/5.41      ((~ (zip_tseitin_1 @ sk_C_1 @ k1_xboole_0 @ k1_xboole_0)
% 5.21/5.41        | ((k1_xboole_0) = (k1_relat_1 @ sk_C_1)))),
% 5.21/5.41      inference('demod', [status(thm)], ['57', '74', '75'])).
% 5.21/5.41  thf('77', plain,
% 5.21/5.41      ((m1_subset_1 @ sk_C_1 @ 
% 5.21/5.41        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 5.21/5.41      inference('demod', [status(thm)], ['58', '59'])).
% 5.21/5.41  thf('78', plain, (((sk_A) = (k1_xboole_0))),
% 5.21/5.41      inference('simplify', [status(thm)], ['73'])).
% 5.21/5.41  thf('79', plain,
% 5.21/5.41      ((m1_subset_1 @ sk_C_1 @ 
% 5.21/5.41        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 5.21/5.41      inference('demod', [status(thm)], ['77', '78'])).
% 5.21/5.41  thf('80', plain,
% 5.21/5.41      (![X27 : $i, X28 : $i, X29 : $i]:
% 5.21/5.41         (~ (zip_tseitin_0 @ X27 @ X28)
% 5.21/5.41          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 5.21/5.41          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 5.21/5.41      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.21/5.41  thf('81', plain,
% 5.21/5.41      (((zip_tseitin_1 @ sk_C_1 @ k1_xboole_0 @ k1_xboole_0)
% 5.21/5.41        | ~ (zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0))),
% 5.21/5.41      inference('sup-', [status(thm)], ['79', '80'])).
% 5.21/5.41  thf('82', plain,
% 5.21/5.41      (![X22 : $i, X23 : $i]:
% 5.21/5.41         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 5.21/5.41      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.21/5.41  thf('83', plain,
% 5.21/5.41      (![X22 : $i, X23 : $i]:
% 5.21/5.41         ((zip_tseitin_0 @ X22 @ X23) | ((X23) != (k1_xboole_0)))),
% 5.21/5.41      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.21/5.41  thf('84', plain, (![X22 : $i]: (zip_tseitin_0 @ X22 @ k1_xboole_0)),
% 5.21/5.41      inference('simplify', [status(thm)], ['83'])).
% 5.21/5.41  thf('85', plain,
% 5.21/5.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.21/5.41         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 5.21/5.41      inference('sup+', [status(thm)], ['82', '84'])).
% 5.21/5.41  thf('86', plain,
% 5.21/5.41      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 5.21/5.41        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 5.21/5.41      inference('sup-', [status(thm)], ['34', '35'])).
% 5.21/5.41  thf('87', plain,
% 5.21/5.41      (![X0 : $i]:
% 5.21/5.41         ((zip_tseitin_0 @ sk_A @ X0) | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 5.21/5.41      inference('sup-', [status(thm)], ['85', '86'])).
% 5.21/5.41  thf('88', plain,
% 5.21/5.41      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 5.21/5.41        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 5.21/5.41      inference('demod', [status(thm)], ['2', '5'])).
% 5.21/5.41  thf('89', plain,
% 5.21/5.41      (![X0 : $i]:
% 5.21/5.41         ((zip_tseitin_0 @ sk_A @ X0) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 5.21/5.41      inference('sup-', [status(thm)], ['87', '88'])).
% 5.21/5.41  thf(t65_relat_1, axiom,
% 5.21/5.41    (![A:$i]:
% 5.21/5.41     ( ( v1_relat_1 @ A ) =>
% 5.21/5.41       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 5.21/5.41         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 5.21/5.41  thf('90', plain,
% 5.21/5.41      (![X9 : $i]:
% 5.21/5.41         (((k1_relat_1 @ X9) != (k1_xboole_0))
% 5.21/5.41          | ((k2_relat_1 @ X9) = (k1_xboole_0))
% 5.21/5.41          | ~ (v1_relat_1 @ X9))),
% 5.21/5.41      inference('cnf', [status(esa)], [t65_relat_1])).
% 5.21/5.41  thf('91', plain,
% 5.21/5.41      (![X0 : $i]:
% 5.21/5.41         (((sk_A) != (k1_xboole_0))
% 5.21/5.41          | (zip_tseitin_0 @ sk_A @ X0)
% 5.21/5.41          | ~ (v1_relat_1 @ sk_C_1)
% 5.21/5.41          | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 5.21/5.41      inference('sup-', [status(thm)], ['89', '90'])).
% 5.21/5.41  thf('92', plain, ((v1_relat_1 @ sk_C_1)),
% 5.21/5.41      inference('demod', [status(thm)], ['14', '15'])).
% 5.21/5.41  thf('93', plain,
% 5.21/5.41      (![X0 : $i]:
% 5.21/5.41         (((sk_A) != (k1_xboole_0))
% 5.21/5.41          | (zip_tseitin_0 @ sk_A @ X0)
% 5.21/5.41          | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 5.21/5.41      inference('demod', [status(thm)], ['91', '92'])).
% 5.21/5.41  thf('94', plain,
% 5.21/5.41      (![X22 : $i, X23 : $i]:
% 5.21/5.41         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 5.21/5.41      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.21/5.41  thf('95', plain,
% 5.21/5.41      (![X0 : $i]:
% 5.21/5.41         (((k2_relat_1 @ sk_C_1) = (k1_xboole_0)) | (zip_tseitin_0 @ sk_A @ X0))),
% 5.21/5.41      inference('clc', [status(thm)], ['93', '94'])).
% 5.21/5.41  thf('96', plain, (((k2_relat_1 @ sk_C_1) != (sk_B))),
% 5.21/5.41      inference('demod', [status(thm)], ['25', '28'])).
% 5.21/5.41  thf('97', plain,
% 5.21/5.41      (![X0 : $i]: (((k1_xboole_0) != (sk_B)) | (zip_tseitin_0 @ sk_A @ X0))),
% 5.21/5.41      inference('sup-', [status(thm)], ['95', '96'])).
% 5.21/5.41  thf('98', plain, (((sk_B) = (k1_xboole_0))),
% 5.21/5.41      inference('simplify_reflect-', [status(thm)], ['54', '55'])).
% 5.21/5.41  thf('99', plain,
% 5.21/5.41      (![X0 : $i]:
% 5.21/5.41         (((k1_xboole_0) != (k1_xboole_0)) | (zip_tseitin_0 @ sk_A @ X0))),
% 5.21/5.41      inference('demod', [status(thm)], ['97', '98'])).
% 5.21/5.41  thf('100', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_A @ X0)),
% 5.21/5.41      inference('simplify', [status(thm)], ['99'])).
% 5.21/5.41  thf('101', plain, (((sk_A) = (k1_xboole_0))),
% 5.21/5.41      inference('simplify', [status(thm)], ['73'])).
% 5.21/5.41  thf('102', plain, (![X0 : $i]: (zip_tseitin_0 @ k1_xboole_0 @ X0)),
% 5.21/5.41      inference('demod', [status(thm)], ['100', '101'])).
% 5.21/5.41  thf('103', plain, ((zip_tseitin_1 @ sk_C_1 @ k1_xboole_0 @ k1_xboole_0)),
% 5.21/5.41      inference('demod', [status(thm)], ['81', '102'])).
% 5.21/5.41  thf('104', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_C_1))),
% 5.21/5.41      inference('demod', [status(thm)], ['76', '103'])).
% 5.21/5.41  thf('105', plain,
% 5.21/5.41      (![X9 : $i]:
% 5.21/5.41         (((k1_relat_1 @ X9) != (k1_xboole_0))
% 5.21/5.41          | ((k2_relat_1 @ X9) = (k1_xboole_0))
% 5.21/5.41          | ~ (v1_relat_1 @ X9))),
% 5.21/5.41      inference('cnf', [status(esa)], [t65_relat_1])).
% 5.21/5.41  thf('106', plain,
% 5.21/5.41      ((((k1_xboole_0) != (k1_xboole_0))
% 5.21/5.41        | ~ (v1_relat_1 @ sk_C_1)
% 5.21/5.41        | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 5.21/5.41      inference('sup-', [status(thm)], ['104', '105'])).
% 5.21/5.41  thf('107', plain, ((v1_relat_1 @ sk_C_1)),
% 5.21/5.41      inference('demod', [status(thm)], ['14', '15'])).
% 5.21/5.41  thf('108', plain,
% 5.21/5.41      ((((k1_xboole_0) != (k1_xboole_0))
% 5.21/5.41        | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 5.21/5.41      inference('demod', [status(thm)], ['106', '107'])).
% 5.21/5.41  thf('109', plain, (((k2_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 5.21/5.41      inference('simplify', [status(thm)], ['108'])).
% 5.21/5.41  thf('110', plain, (((k2_relat_1 @ sk_C_1) != (k1_xboole_0))),
% 5.21/5.41      inference('demod', [status(thm)], ['68', '69'])).
% 5.21/5.41  thf('111', plain, ($false),
% 5.21/5.41      inference('simplify_reflect-', [status(thm)], ['109', '110'])).
% 5.21/5.41  
% 5.21/5.41  % SZS output end Refutation
% 5.21/5.41  
% 5.21/5.42  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
