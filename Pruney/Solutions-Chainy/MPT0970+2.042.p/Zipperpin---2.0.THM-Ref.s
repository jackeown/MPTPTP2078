%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FJNtLU6UOY

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:22 EST 2020

% Result     : Theorem 1.14s
% Output     : Refutation 1.14s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 571 expanded)
%              Number of leaves         :   55 ( 193 expanded)
%              Depth                    :   18
%              Number of atoms          : 1137 (6252 expanded)
%              Number of equality atoms :   72 ( 379 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( v4_relat_1 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v4_relat_1 @ sk_C_3 @ sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X29: $i,X30: $i] :
      ( ( X29
        = ( k7_relat_1 @ X29 @ X30 ) )
      | ~ ( v4_relat_1 @ X29 @ X30 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_C_3 )
    | ( sk_C_3
      = ( k7_relat_1 @ sk_C_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( v1_relat_1 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('8',plain,(
    ! [X25: $i,X26: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('9',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( sk_C_3
    = ( k7_relat_1 @ sk_C_3 @ sk_A ) ),
    inference(demod,[status(thm)],['4','9'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X27 @ X28 ) )
        = ( k9_relat_1 @ X27 @ X28 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('12',plain,
    ( ( ( k2_relat_1 @ sk_C_3 )
      = ( k9_relat_1 @ sk_C_3 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C_3 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(demod,[status(thm)],['7','8'])).

thf('14',plain,
    ( ( k2_relat_1 @ sk_C_3 )
    = ( k9_relat_1 @ sk_C_3 @ sk_A ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('16',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X39 @ X40 @ X38 @ X41 ) @ ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C_3 @ X0 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('19',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ( ( k7_relset_1 @ X49 @ X50 @ X48 @ X51 )
        = ( k9_relat_1 @ X48 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_C_3 @ X0 )
      = ( k9_relat_1 @ sk_C_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_relat_1 @ sk_C_3 @ X0 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C_3 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['14','21'])).

thf(t49_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ! [C: $i] :
            ( ( m1_subset_1 @ C @ A )
           => ( r2_hidden @ C @ B ) )
       => ( A = B ) ) ) )).

thf('23',plain,(
    ! [X17: $i,X18: $i] :
      ( ( m1_subset_1 @ ( sk_C_2 @ X17 @ X18 ) @ X18 )
      | ( X18 = X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('24',plain,
    ( ( sk_B_1
      = ( k2_relat_1 @ sk_C_3 ) )
    | ( m1_subset_1 @ ( sk_C_2 @ ( k2_relat_1 @ sk_C_3 ) @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_3 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('27',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( ( k2_relset_1 @ X46 @ X47 @ X45 )
        = ( k2_relat_1 @ X45 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('28',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_3 )
    = ( k2_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ( k2_relat_1 @ sk_C_3 )
 != sk_B_1 ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,(
    m1_subset_1 @ ( sk_C_2 @ ( k2_relat_1 @ sk_C_3 ) @ sk_B_1 ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['24','29'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('31',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r2_hidden @ X19 @ X20 )
      | ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('32',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_C_2 @ ( k2_relat_1 @ sk_C_3 ) @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X60: $i] :
      ( ~ ( r2_hidden @ X60 @ sk_B_1 )
      | ( r2_hidden @ ( sk_E @ X60 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_E @ ( sk_C_2 @ ( k2_relat_1 @ sk_C_3 ) @ sk_B_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('35',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('36',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('37',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X33 @ X34 )
      | ~ ( r1_tarski @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','38'])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('40',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X4 = X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k2_relat_1 @ sk_C_3 )
    = ( k9_relat_1 @ sk_C_3 @ sk_A ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('49',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_relat_1 @ sk_C_3 @ X0 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('50',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r2_hidden @ X19 @ X20 )
      | ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( k9_relat_1 @ sk_C_3 @ X0 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('52',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( X5 != X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('53',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['52'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('54',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ( r2_hidden @ X12 @ X14 )
      | ( X14
       != ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('55',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('58',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k9_relat_1 @ sk_C_3 @ X0 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['51','58'])).

thf('60',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ( r1_tarski @ X15 @ X13 )
      | ( X14
       != ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('61',plain,(
    ! [X13: $i,X15: $i] :
      ( ( r1_tarski @ X15 @ X13 )
      | ~ ( r2_hidden @ X15 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_C_3 @ X0 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['59','61'])).

thf('63',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B_1 @ ( k9_relat_1 @ sk_C_3 @ X0 ) )
      | ( sk_B_1
        = ( k9_relat_1 @ sk_C_3 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k2_relat_1 @ sk_C_3 ) )
    | ( sk_B_1
      = ( k9_relat_1 @ sk_C_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','64'])).

thf('66',plain,
    ( ( k2_relat_1 @ sk_C_3 )
    = ( k9_relat_1 @ sk_C_3 @ sk_A ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('67',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k2_relat_1 @ sk_C_3 ) )
    | ( sk_B_1
      = ( k2_relat_1 @ sk_C_3 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ( k2_relat_1 @ sk_C_3 )
 != sk_B_1 ),
    inference(demod,[status(thm)],['25','28'])).

thf('69',plain,(
    ~ ( r1_tarski @ sk_B_1 @ ( k2_relat_1 @ sk_C_3 ) ) ),
    inference('simplify_reflect-',[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['47','69'])).

thf('71',plain,(
    r2_hidden @ ( sk_E @ ( sk_C_2 @ ( k2_relat_1 @ sk_C_3 ) @ sk_B_1 ) ) @ sk_A ),
    inference(clc,[status(thm)],['34','70'])).

thf('72',plain,(
    v1_funct_2 @ sk_C_3 @ sk_A @ sk_B_1 ),
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

thf('73',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ~ ( v1_funct_2 @ X56 @ X54 @ X55 )
      | ( X54
        = ( k1_relset_1 @ X54 @ X55 @ X56 ) )
      | ~ ( zip_tseitin_1 @ X56 @ X55 @ X54 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('74',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_3 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('76',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( ( k1_relset_1 @ X43 @ X44 @ X42 )
        = ( k1_relat_1 @ X42 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('77',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_3 )
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_3 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_3 ) ) ),
    inference(demod,[status(thm)],['74','77'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('79',plain,(
    ! [X52: $i,X53: $i] :
      ( ( zip_tseitin_0 @ X52 @ X53 )
      | ( X52 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('80',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( v5_relat_1 @ X35 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('84',plain,(
    v5_relat_1 @ sk_C_3 @ sk_B_1 ),
    inference('sup-',[status(thm)],['82','83'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('85',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v5_relat_1 @ X23 @ X24 )
      | ( r1_tarski @ ( k2_relat_1 @ X23 ) @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('86',plain,
    ( ~ ( v1_relat_1 @ sk_C_3 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_3 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(demod,[status(thm)],['7','8'])).

thf('88',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_3 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('90',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k2_relat_1 @ sk_C_3 ) )
    | ( sk_B_1
      = ( k2_relat_1 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( sk_B_1
        = ( k2_relat_1 @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['81','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('93',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ~ ( zip_tseitin_0 @ X57 @ X58 )
      | ( zip_tseitin_1 @ X59 @ X57 @ X58 )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X58 @ X57 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('94',plain,
    ( ( zip_tseitin_1 @ sk_C_3 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( sk_B_1
      = ( k2_relat_1 @ sk_C_3 ) )
    | ( zip_tseitin_1 @ sk_C_3 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['91','94'])).

thf('96',plain,(
    ( k2_relat_1 @ sk_C_3 )
 != sk_B_1 ),
    inference(demod,[status(thm)],['25','28'])).

thf('97',plain,(
    zip_tseitin_1 @ sk_C_3 @ sk_B_1 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['95','96'])).

thf('98',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['78','97'])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('99',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X31 @ ( k1_relat_1 @ X32 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X32 @ X31 ) @ ( k2_relat_1 @ X32 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C_3 )
      | ~ ( v1_funct_1 @ sk_C_3 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_3 @ X0 ) @ ( k2_relat_1 @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(demod,[status(thm)],['7','8'])).

thf('102',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_3 @ X0 ) @ ( k2_relat_1 @ sk_C_3 ) ) ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C_3 @ ( sk_E @ ( sk_C_2 @ ( k2_relat_1 @ sk_C_3 ) @ sk_B_1 ) ) ) @ ( k2_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['71','103'])).

thf('105',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_C_2 @ ( k2_relat_1 @ sk_C_3 ) @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('106',plain,(
    ! [X60: $i] :
      ( ~ ( r2_hidden @ X60 @ sk_B_1 )
      | ( X60
        = ( k1_funct_1 @ sk_C_3 @ ( sk_E @ X60 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( ( sk_C_2 @ ( k2_relat_1 @ sk_C_3 ) @ sk_B_1 )
      = ( k1_funct_1 @ sk_C_3 @ ( sk_E @ ( sk_C_2 @ ( k2_relat_1 @ sk_C_3 ) @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['47','69'])).

thf('109',plain,
    ( ( sk_C_2 @ ( k2_relat_1 @ sk_C_3 ) @ sk_B_1 )
    = ( k1_funct_1 @ sk_C_3 @ ( sk_E @ ( sk_C_2 @ ( k2_relat_1 @ sk_C_3 ) @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,(
    r2_hidden @ ( sk_C_2 @ ( k2_relat_1 @ sk_C_3 ) @ sk_B_1 ) @ ( k2_relat_1 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['104','109'])).

thf('111',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ ( sk_C_2 @ X17 @ X18 ) @ X17 )
      | ( X18 = X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('112',plain,
    ( ~ ( m1_subset_1 @ ( k2_relat_1 @ sk_C_3 ) @ ( k1_zfmisc_1 @ sk_B_1 ) )
    | ( sk_B_1
      = ( k2_relat_1 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C_3 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['14','21'])).

thf('114',plain,
    ( sk_B_1
    = ( k2_relat_1 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ( k2_relat_1 @ sk_C_3 )
 != sk_B_1 ),
    inference(demod,[status(thm)],['25','28'])).

thf('116',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['114','115'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FJNtLU6UOY
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:25:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.14/1.33  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.14/1.33  % Solved by: fo/fo7.sh
% 1.14/1.33  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.14/1.33  % done 1131 iterations in 0.879s
% 1.14/1.33  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.14/1.33  % SZS output start Refutation
% 1.14/1.33  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.14/1.33  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.14/1.33  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.14/1.33  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.14/1.33  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.14/1.33  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.14/1.33  thf(sk_E_type, type, sk_E: $i > $i).
% 1.14/1.33  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.14/1.33  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 1.14/1.33  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.14/1.33  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.14/1.33  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.14/1.33  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.14/1.33  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.14/1.33  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.14/1.33  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.14/1.33  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.14/1.33  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.14/1.33  thf(sk_C_3_type, type, sk_C_3: $i).
% 1.14/1.33  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.14/1.33  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.14/1.33  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 1.14/1.33  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.14/1.33  thf(sk_B_type, type, sk_B: $i > $i).
% 1.14/1.33  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.14/1.33  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.14/1.33  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.14/1.33  thf(sk_A_type, type, sk_A: $i).
% 1.14/1.33  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.14/1.33  thf(t16_funct_2, conjecture,
% 1.14/1.33    (![A:$i,B:$i,C:$i]:
% 1.14/1.33     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.14/1.33         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.14/1.33       ( ( ![D:$i]:
% 1.14/1.33           ( ~( ( r2_hidden @ D @ B ) & 
% 1.14/1.33                ( ![E:$i]:
% 1.14/1.33                  ( ~( ( r2_hidden @ E @ A ) & 
% 1.14/1.33                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 1.14/1.33         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 1.14/1.33  thf(zf_stmt_0, negated_conjecture,
% 1.14/1.33    (~( ![A:$i,B:$i,C:$i]:
% 1.14/1.33        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.14/1.33            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.14/1.33          ( ( ![D:$i]:
% 1.14/1.33              ( ~( ( r2_hidden @ D @ B ) & 
% 1.14/1.33                   ( ![E:$i]:
% 1.14/1.33                     ( ~( ( r2_hidden @ E @ A ) & 
% 1.14/1.33                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 1.14/1.33            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 1.14/1.33    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 1.14/1.33  thf('0', plain,
% 1.14/1.33      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf(cc2_relset_1, axiom,
% 1.14/1.33    (![A:$i,B:$i,C:$i]:
% 1.14/1.33     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.14/1.33       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.14/1.33  thf('1', plain,
% 1.14/1.33      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.14/1.33         ((v4_relat_1 @ X35 @ X36)
% 1.14/1.33          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 1.14/1.33      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.14/1.33  thf('2', plain, ((v4_relat_1 @ sk_C_3 @ sk_A)),
% 1.14/1.33      inference('sup-', [status(thm)], ['0', '1'])).
% 1.14/1.33  thf(t209_relat_1, axiom,
% 1.14/1.33    (![A:$i,B:$i]:
% 1.14/1.33     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.14/1.33       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 1.14/1.33  thf('3', plain,
% 1.14/1.33      (![X29 : $i, X30 : $i]:
% 1.14/1.33         (((X29) = (k7_relat_1 @ X29 @ X30))
% 1.14/1.33          | ~ (v4_relat_1 @ X29 @ X30)
% 1.14/1.33          | ~ (v1_relat_1 @ X29))),
% 1.14/1.33      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.14/1.33  thf('4', plain,
% 1.14/1.33      ((~ (v1_relat_1 @ sk_C_3) | ((sk_C_3) = (k7_relat_1 @ sk_C_3 @ sk_A)))),
% 1.14/1.33      inference('sup-', [status(thm)], ['2', '3'])).
% 1.14/1.33  thf('5', plain,
% 1.14/1.33      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf(cc2_relat_1, axiom,
% 1.14/1.33    (![A:$i]:
% 1.14/1.33     ( ( v1_relat_1 @ A ) =>
% 1.14/1.33       ( ![B:$i]:
% 1.14/1.33         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.14/1.33  thf('6', plain,
% 1.14/1.33      (![X21 : $i, X22 : $i]:
% 1.14/1.33         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 1.14/1.33          | (v1_relat_1 @ X21)
% 1.14/1.33          | ~ (v1_relat_1 @ X22))),
% 1.14/1.33      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.14/1.33  thf('7', plain,
% 1.14/1.33      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_C_3))),
% 1.14/1.33      inference('sup-', [status(thm)], ['5', '6'])).
% 1.14/1.33  thf(fc6_relat_1, axiom,
% 1.14/1.33    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.14/1.33  thf('8', plain,
% 1.14/1.33      (![X25 : $i, X26 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X25 @ X26))),
% 1.14/1.33      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.14/1.33  thf('9', plain, ((v1_relat_1 @ sk_C_3)),
% 1.14/1.33      inference('demod', [status(thm)], ['7', '8'])).
% 1.14/1.33  thf('10', plain, (((sk_C_3) = (k7_relat_1 @ sk_C_3 @ sk_A))),
% 1.14/1.33      inference('demod', [status(thm)], ['4', '9'])).
% 1.14/1.33  thf(t148_relat_1, axiom,
% 1.14/1.33    (![A:$i,B:$i]:
% 1.14/1.33     ( ( v1_relat_1 @ B ) =>
% 1.14/1.33       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 1.14/1.33  thf('11', plain,
% 1.14/1.33      (![X27 : $i, X28 : $i]:
% 1.14/1.33         (((k2_relat_1 @ (k7_relat_1 @ X27 @ X28)) = (k9_relat_1 @ X27 @ X28))
% 1.14/1.33          | ~ (v1_relat_1 @ X27))),
% 1.14/1.33      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.14/1.33  thf('12', plain,
% 1.14/1.33      ((((k2_relat_1 @ sk_C_3) = (k9_relat_1 @ sk_C_3 @ sk_A))
% 1.14/1.33        | ~ (v1_relat_1 @ sk_C_3))),
% 1.14/1.33      inference('sup+', [status(thm)], ['10', '11'])).
% 1.14/1.33  thf('13', plain, ((v1_relat_1 @ sk_C_3)),
% 1.14/1.33      inference('demod', [status(thm)], ['7', '8'])).
% 1.14/1.33  thf('14', plain, (((k2_relat_1 @ sk_C_3) = (k9_relat_1 @ sk_C_3 @ sk_A))),
% 1.14/1.33      inference('demod', [status(thm)], ['12', '13'])).
% 1.14/1.33  thf('15', plain,
% 1.14/1.33      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf(dt_k7_relset_1, axiom,
% 1.14/1.33    (![A:$i,B:$i,C:$i,D:$i]:
% 1.14/1.33     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.14/1.33       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 1.14/1.33  thf('16', plain,
% 1.14/1.33      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 1.14/1.33         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 1.14/1.33          | (m1_subset_1 @ (k7_relset_1 @ X39 @ X40 @ X38 @ X41) @ 
% 1.14/1.33             (k1_zfmisc_1 @ X40)))),
% 1.14/1.33      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 1.14/1.33  thf('17', plain,
% 1.14/1.33      (![X0 : $i]:
% 1.14/1.33         (m1_subset_1 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_C_3 @ X0) @ 
% 1.14/1.33          (k1_zfmisc_1 @ sk_B_1))),
% 1.14/1.33      inference('sup-', [status(thm)], ['15', '16'])).
% 1.14/1.33  thf('18', plain,
% 1.14/1.33      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf(redefinition_k7_relset_1, axiom,
% 1.14/1.33    (![A:$i,B:$i,C:$i,D:$i]:
% 1.14/1.33     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.14/1.33       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 1.14/1.33  thf('19', plain,
% 1.14/1.33      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 1.14/1.33         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 1.14/1.33          | ((k7_relset_1 @ X49 @ X50 @ X48 @ X51) = (k9_relat_1 @ X48 @ X51)))),
% 1.14/1.33      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 1.14/1.33  thf('20', plain,
% 1.14/1.33      (![X0 : $i]:
% 1.14/1.33         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_C_3 @ X0)
% 1.14/1.33           = (k9_relat_1 @ sk_C_3 @ X0))),
% 1.14/1.33      inference('sup-', [status(thm)], ['18', '19'])).
% 1.14/1.33  thf('21', plain,
% 1.14/1.33      (![X0 : $i]:
% 1.14/1.33         (m1_subset_1 @ (k9_relat_1 @ sk_C_3 @ X0) @ (k1_zfmisc_1 @ sk_B_1))),
% 1.14/1.33      inference('demod', [status(thm)], ['17', '20'])).
% 1.14/1.33  thf('22', plain,
% 1.14/1.33      ((m1_subset_1 @ (k2_relat_1 @ sk_C_3) @ (k1_zfmisc_1 @ sk_B_1))),
% 1.14/1.33      inference('sup+', [status(thm)], ['14', '21'])).
% 1.14/1.33  thf(t49_subset_1, axiom,
% 1.14/1.33    (![A:$i,B:$i]:
% 1.14/1.33     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.14/1.33       ( ( ![C:$i]: ( ( m1_subset_1 @ C @ A ) => ( r2_hidden @ C @ B ) ) ) =>
% 1.14/1.33         ( ( A ) = ( B ) ) ) ))).
% 1.14/1.33  thf('23', plain,
% 1.14/1.33      (![X17 : $i, X18 : $i]:
% 1.14/1.33         ((m1_subset_1 @ (sk_C_2 @ X17 @ X18) @ X18)
% 1.14/1.33          | ((X18) = (X17))
% 1.14/1.33          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 1.14/1.33      inference('cnf', [status(esa)], [t49_subset_1])).
% 1.14/1.33  thf('24', plain,
% 1.14/1.33      ((((sk_B_1) = (k2_relat_1 @ sk_C_3))
% 1.14/1.33        | (m1_subset_1 @ (sk_C_2 @ (k2_relat_1 @ sk_C_3) @ sk_B_1) @ sk_B_1))),
% 1.14/1.33      inference('sup-', [status(thm)], ['22', '23'])).
% 1.14/1.33  thf('25', plain, (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_3) != (sk_B_1))),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('26', plain,
% 1.14/1.33      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf(redefinition_k2_relset_1, axiom,
% 1.14/1.33    (![A:$i,B:$i,C:$i]:
% 1.14/1.33     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.14/1.33       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.14/1.33  thf('27', plain,
% 1.14/1.33      (![X45 : $i, X46 : $i, X47 : $i]:
% 1.14/1.33         (((k2_relset_1 @ X46 @ X47 @ X45) = (k2_relat_1 @ X45))
% 1.14/1.33          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47))))),
% 1.14/1.33      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.14/1.33  thf('28', plain,
% 1.14/1.33      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_3) = (k2_relat_1 @ sk_C_3))),
% 1.14/1.33      inference('sup-', [status(thm)], ['26', '27'])).
% 1.14/1.33  thf('29', plain, (((k2_relat_1 @ sk_C_3) != (sk_B_1))),
% 1.14/1.33      inference('demod', [status(thm)], ['25', '28'])).
% 1.14/1.33  thf('30', plain,
% 1.14/1.33      ((m1_subset_1 @ (sk_C_2 @ (k2_relat_1 @ sk_C_3) @ sk_B_1) @ sk_B_1)),
% 1.14/1.33      inference('simplify_reflect-', [status(thm)], ['24', '29'])).
% 1.14/1.33  thf(t2_subset, axiom,
% 1.14/1.33    (![A:$i,B:$i]:
% 1.14/1.33     ( ( m1_subset_1 @ A @ B ) =>
% 1.14/1.33       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 1.14/1.33  thf('31', plain,
% 1.14/1.33      (![X19 : $i, X20 : $i]:
% 1.14/1.33         ((r2_hidden @ X19 @ X20)
% 1.14/1.33          | (v1_xboole_0 @ X20)
% 1.14/1.33          | ~ (m1_subset_1 @ X19 @ X20))),
% 1.14/1.33      inference('cnf', [status(esa)], [t2_subset])).
% 1.14/1.33  thf('32', plain,
% 1.14/1.33      (((v1_xboole_0 @ sk_B_1)
% 1.14/1.33        | (r2_hidden @ (sk_C_2 @ (k2_relat_1 @ sk_C_3) @ sk_B_1) @ sk_B_1))),
% 1.14/1.33      inference('sup-', [status(thm)], ['30', '31'])).
% 1.14/1.33  thf('33', plain,
% 1.14/1.33      (![X60 : $i]:
% 1.14/1.33         (~ (r2_hidden @ X60 @ sk_B_1) | (r2_hidden @ (sk_E @ X60) @ sk_A))),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('34', plain,
% 1.14/1.33      (((v1_xboole_0 @ sk_B_1)
% 1.14/1.33        | (r2_hidden @ (sk_E @ (sk_C_2 @ (k2_relat_1 @ sk_C_3) @ sk_B_1)) @ 
% 1.14/1.33           sk_A))),
% 1.14/1.33      inference('sup-', [status(thm)], ['32', '33'])).
% 1.14/1.33  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.14/1.33  thf('35', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 1.14/1.33      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.14/1.33  thf(d1_xboole_0, axiom,
% 1.14/1.33    (![A:$i]:
% 1.14/1.33     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.14/1.33  thf('36', plain,
% 1.14/1.33      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.14/1.33      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.14/1.33  thf(t7_ordinal1, axiom,
% 1.14/1.33    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.14/1.33  thf('37', plain,
% 1.14/1.33      (![X33 : $i, X34 : $i]:
% 1.14/1.33         (~ (r2_hidden @ X33 @ X34) | ~ (r1_tarski @ X34 @ X33))),
% 1.14/1.33      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.14/1.33  thf('38', plain,
% 1.14/1.33      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 1.14/1.33      inference('sup-', [status(thm)], ['36', '37'])).
% 1.14/1.33  thf('39', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.14/1.33      inference('sup-', [status(thm)], ['35', '38'])).
% 1.14/1.33  thf(t2_tarski, axiom,
% 1.14/1.33    (![A:$i,B:$i]:
% 1.14/1.33     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 1.14/1.33       ( ( A ) = ( B ) ) ))).
% 1.14/1.33  thf('40', plain,
% 1.14/1.33      (![X3 : $i, X4 : $i]:
% 1.14/1.33         (((X4) = (X3))
% 1.14/1.33          | (r2_hidden @ (sk_C @ X3 @ X4) @ X3)
% 1.14/1.33          | (r2_hidden @ (sk_C @ X3 @ X4) @ X4))),
% 1.14/1.33      inference('cnf', [status(esa)], [t2_tarski])).
% 1.14/1.33  thf('41', plain,
% 1.14/1.33      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.14/1.33      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.14/1.33  thf('42', plain,
% 1.14/1.33      (![X0 : $i, X1 : $i]:
% 1.14/1.33         ((r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 1.14/1.33          | ((X1) = (X0))
% 1.14/1.33          | ~ (v1_xboole_0 @ X0))),
% 1.14/1.33      inference('sup-', [status(thm)], ['40', '41'])).
% 1.14/1.33  thf('43', plain,
% 1.14/1.33      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.14/1.33      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.14/1.33  thf('44', plain,
% 1.14/1.33      (![X0 : $i, X1 : $i]:
% 1.14/1.33         (~ (v1_xboole_0 @ X1) | ((X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 1.14/1.33      inference('sup-', [status(thm)], ['42', '43'])).
% 1.14/1.33  thf('45', plain,
% 1.14/1.33      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 1.14/1.33      inference('sup-', [status(thm)], ['39', '44'])).
% 1.14/1.33  thf('46', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 1.14/1.33      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.14/1.33  thf('47', plain,
% 1.14/1.33      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.14/1.33      inference('sup+', [status(thm)], ['45', '46'])).
% 1.14/1.33  thf('48', plain, (((k2_relat_1 @ sk_C_3) = (k9_relat_1 @ sk_C_3 @ sk_A))),
% 1.14/1.33      inference('demod', [status(thm)], ['12', '13'])).
% 1.14/1.33  thf('49', plain,
% 1.14/1.33      (![X0 : $i]:
% 1.14/1.33         (m1_subset_1 @ (k9_relat_1 @ sk_C_3 @ X0) @ (k1_zfmisc_1 @ sk_B_1))),
% 1.14/1.33      inference('demod', [status(thm)], ['17', '20'])).
% 1.14/1.33  thf('50', plain,
% 1.14/1.33      (![X19 : $i, X20 : $i]:
% 1.14/1.33         ((r2_hidden @ X19 @ X20)
% 1.14/1.33          | (v1_xboole_0 @ X20)
% 1.14/1.33          | ~ (m1_subset_1 @ X19 @ X20))),
% 1.14/1.33      inference('cnf', [status(esa)], [t2_subset])).
% 1.14/1.33  thf('51', plain,
% 1.14/1.33      (![X0 : $i]:
% 1.14/1.33         ((v1_xboole_0 @ (k1_zfmisc_1 @ sk_B_1))
% 1.14/1.33          | (r2_hidden @ (k9_relat_1 @ sk_C_3 @ X0) @ (k1_zfmisc_1 @ sk_B_1)))),
% 1.14/1.33      inference('sup-', [status(thm)], ['49', '50'])).
% 1.14/1.33  thf(d10_xboole_0, axiom,
% 1.14/1.33    (![A:$i,B:$i]:
% 1.14/1.33     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.14/1.33  thf('52', plain,
% 1.14/1.33      (![X5 : $i, X6 : $i]: ((r1_tarski @ X5 @ X6) | ((X5) != (X6)))),
% 1.14/1.33      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.14/1.33  thf('53', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 1.14/1.33      inference('simplify', [status(thm)], ['52'])).
% 1.14/1.33  thf(d1_zfmisc_1, axiom,
% 1.14/1.33    (![A:$i,B:$i]:
% 1.14/1.33     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 1.14/1.33       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 1.14/1.33  thf('54', plain,
% 1.14/1.33      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.14/1.33         (~ (r1_tarski @ X12 @ X13)
% 1.14/1.33          | (r2_hidden @ X12 @ X14)
% 1.14/1.33          | ((X14) != (k1_zfmisc_1 @ X13)))),
% 1.14/1.33      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.14/1.33  thf('55', plain,
% 1.14/1.33      (![X12 : $i, X13 : $i]:
% 1.14/1.33         ((r2_hidden @ X12 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X12 @ X13))),
% 1.14/1.33      inference('simplify', [status(thm)], ['54'])).
% 1.14/1.33  thf('56', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.14/1.33      inference('sup-', [status(thm)], ['53', '55'])).
% 1.14/1.33  thf('57', plain,
% 1.14/1.33      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.14/1.33      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.14/1.33  thf('58', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.14/1.33      inference('sup-', [status(thm)], ['56', '57'])).
% 1.14/1.33  thf('59', plain,
% 1.14/1.33      (![X0 : $i]:
% 1.14/1.33         (r2_hidden @ (k9_relat_1 @ sk_C_3 @ X0) @ (k1_zfmisc_1 @ sk_B_1))),
% 1.14/1.33      inference('clc', [status(thm)], ['51', '58'])).
% 1.14/1.33  thf('60', plain,
% 1.14/1.33      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.14/1.33         (~ (r2_hidden @ X15 @ X14)
% 1.14/1.33          | (r1_tarski @ X15 @ X13)
% 1.14/1.33          | ((X14) != (k1_zfmisc_1 @ X13)))),
% 1.14/1.33      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.14/1.33  thf('61', plain,
% 1.14/1.33      (![X13 : $i, X15 : $i]:
% 1.14/1.33         ((r1_tarski @ X15 @ X13) | ~ (r2_hidden @ X15 @ (k1_zfmisc_1 @ X13)))),
% 1.14/1.33      inference('simplify', [status(thm)], ['60'])).
% 1.14/1.33  thf('62', plain,
% 1.14/1.33      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ sk_C_3 @ X0) @ sk_B_1)),
% 1.14/1.33      inference('sup-', [status(thm)], ['59', '61'])).
% 1.14/1.33  thf('63', plain,
% 1.14/1.33      (![X5 : $i, X7 : $i]:
% 1.14/1.33         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 1.14/1.33      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.14/1.33  thf('64', plain,
% 1.14/1.33      (![X0 : $i]:
% 1.14/1.33         (~ (r1_tarski @ sk_B_1 @ (k9_relat_1 @ sk_C_3 @ X0))
% 1.14/1.33          | ((sk_B_1) = (k9_relat_1 @ sk_C_3 @ X0)))),
% 1.14/1.33      inference('sup-', [status(thm)], ['62', '63'])).
% 1.14/1.33  thf('65', plain,
% 1.14/1.33      ((~ (r1_tarski @ sk_B_1 @ (k2_relat_1 @ sk_C_3))
% 1.14/1.33        | ((sk_B_1) = (k9_relat_1 @ sk_C_3 @ sk_A)))),
% 1.14/1.33      inference('sup-', [status(thm)], ['48', '64'])).
% 1.14/1.33  thf('66', plain, (((k2_relat_1 @ sk_C_3) = (k9_relat_1 @ sk_C_3 @ sk_A))),
% 1.14/1.33      inference('demod', [status(thm)], ['12', '13'])).
% 1.14/1.33  thf('67', plain,
% 1.14/1.33      ((~ (r1_tarski @ sk_B_1 @ (k2_relat_1 @ sk_C_3))
% 1.14/1.33        | ((sk_B_1) = (k2_relat_1 @ sk_C_3)))),
% 1.14/1.33      inference('demod', [status(thm)], ['65', '66'])).
% 1.14/1.33  thf('68', plain, (((k2_relat_1 @ sk_C_3) != (sk_B_1))),
% 1.14/1.33      inference('demod', [status(thm)], ['25', '28'])).
% 1.14/1.33  thf('69', plain, (~ (r1_tarski @ sk_B_1 @ (k2_relat_1 @ sk_C_3))),
% 1.14/1.33      inference('simplify_reflect-', [status(thm)], ['67', '68'])).
% 1.14/1.33  thf('70', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.14/1.33      inference('sup-', [status(thm)], ['47', '69'])).
% 1.14/1.33  thf('71', plain,
% 1.14/1.33      ((r2_hidden @ (sk_E @ (sk_C_2 @ (k2_relat_1 @ sk_C_3) @ sk_B_1)) @ sk_A)),
% 1.14/1.33      inference('clc', [status(thm)], ['34', '70'])).
% 1.14/1.33  thf('72', plain, ((v1_funct_2 @ sk_C_3 @ sk_A @ sk_B_1)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf(d1_funct_2, axiom,
% 1.14/1.33    (![A:$i,B:$i,C:$i]:
% 1.14/1.33     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.14/1.33       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.14/1.33           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.14/1.33             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.14/1.33         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.14/1.33           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.14/1.33             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.14/1.33  thf(zf_stmt_1, axiom,
% 1.14/1.33    (![C:$i,B:$i,A:$i]:
% 1.14/1.33     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.14/1.33       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.14/1.33  thf('73', plain,
% 1.14/1.33      (![X54 : $i, X55 : $i, X56 : $i]:
% 1.14/1.33         (~ (v1_funct_2 @ X56 @ X54 @ X55)
% 1.14/1.33          | ((X54) = (k1_relset_1 @ X54 @ X55 @ X56))
% 1.14/1.33          | ~ (zip_tseitin_1 @ X56 @ X55 @ X54))),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.14/1.33  thf('74', plain,
% 1.14/1.33      ((~ (zip_tseitin_1 @ sk_C_3 @ sk_B_1 @ sk_A)
% 1.14/1.33        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_3)))),
% 1.14/1.33      inference('sup-', [status(thm)], ['72', '73'])).
% 1.14/1.33  thf('75', plain,
% 1.14/1.33      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf(redefinition_k1_relset_1, axiom,
% 1.14/1.33    (![A:$i,B:$i,C:$i]:
% 1.14/1.33     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.14/1.33       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.14/1.33  thf('76', plain,
% 1.14/1.33      (![X42 : $i, X43 : $i, X44 : $i]:
% 1.14/1.33         (((k1_relset_1 @ X43 @ X44 @ X42) = (k1_relat_1 @ X42))
% 1.14/1.33          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44))))),
% 1.14/1.33      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.14/1.33  thf('77', plain,
% 1.14/1.33      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_3) = (k1_relat_1 @ sk_C_3))),
% 1.14/1.33      inference('sup-', [status(thm)], ['75', '76'])).
% 1.14/1.33  thf('78', plain,
% 1.14/1.33      ((~ (zip_tseitin_1 @ sk_C_3 @ sk_B_1 @ sk_A)
% 1.14/1.33        | ((sk_A) = (k1_relat_1 @ sk_C_3)))),
% 1.14/1.33      inference('demod', [status(thm)], ['74', '77'])).
% 1.14/1.33  thf(zf_stmt_2, axiom,
% 1.14/1.33    (![B:$i,A:$i]:
% 1.14/1.33     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.14/1.33       ( zip_tseitin_0 @ B @ A ) ))).
% 1.14/1.33  thf('79', plain,
% 1.14/1.33      (![X52 : $i, X53 : $i]:
% 1.14/1.33         ((zip_tseitin_0 @ X52 @ X53) | ((X52) = (k1_xboole_0)))),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.14/1.33  thf('80', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 1.14/1.33      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.14/1.33  thf('81', plain,
% 1.14/1.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.14/1.33         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 1.14/1.33      inference('sup+', [status(thm)], ['79', '80'])).
% 1.14/1.33  thf('82', plain,
% 1.14/1.33      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('83', plain,
% 1.14/1.33      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.14/1.33         ((v5_relat_1 @ X35 @ X37)
% 1.14/1.33          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 1.14/1.33      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.14/1.33  thf('84', plain, ((v5_relat_1 @ sk_C_3 @ sk_B_1)),
% 1.14/1.33      inference('sup-', [status(thm)], ['82', '83'])).
% 1.14/1.33  thf(d19_relat_1, axiom,
% 1.14/1.33    (![A:$i,B:$i]:
% 1.14/1.33     ( ( v1_relat_1 @ B ) =>
% 1.14/1.33       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.14/1.33  thf('85', plain,
% 1.14/1.33      (![X23 : $i, X24 : $i]:
% 1.14/1.33         (~ (v5_relat_1 @ X23 @ X24)
% 1.14/1.33          | (r1_tarski @ (k2_relat_1 @ X23) @ X24)
% 1.14/1.33          | ~ (v1_relat_1 @ X23))),
% 1.14/1.33      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.14/1.33  thf('86', plain,
% 1.14/1.33      ((~ (v1_relat_1 @ sk_C_3) | (r1_tarski @ (k2_relat_1 @ sk_C_3) @ sk_B_1))),
% 1.14/1.33      inference('sup-', [status(thm)], ['84', '85'])).
% 1.14/1.33  thf('87', plain, ((v1_relat_1 @ sk_C_3)),
% 1.14/1.33      inference('demod', [status(thm)], ['7', '8'])).
% 1.14/1.33  thf('88', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_3) @ sk_B_1)),
% 1.14/1.33      inference('demod', [status(thm)], ['86', '87'])).
% 1.14/1.33  thf('89', plain,
% 1.14/1.33      (![X5 : $i, X7 : $i]:
% 1.14/1.33         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 1.14/1.33      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.14/1.33  thf('90', plain,
% 1.14/1.33      ((~ (r1_tarski @ sk_B_1 @ (k2_relat_1 @ sk_C_3))
% 1.14/1.33        | ((sk_B_1) = (k2_relat_1 @ sk_C_3)))),
% 1.14/1.33      inference('sup-', [status(thm)], ['88', '89'])).
% 1.14/1.33  thf('91', plain,
% 1.14/1.33      (![X0 : $i]:
% 1.14/1.33         ((zip_tseitin_0 @ sk_B_1 @ X0) | ((sk_B_1) = (k2_relat_1 @ sk_C_3)))),
% 1.14/1.33      inference('sup-', [status(thm)], ['81', '90'])).
% 1.14/1.33  thf('92', plain,
% 1.14/1.33      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.14/1.33  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.14/1.33  thf(zf_stmt_5, axiom,
% 1.14/1.33    (![A:$i,B:$i,C:$i]:
% 1.14/1.33     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.14/1.33       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.14/1.33         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.14/1.33           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.14/1.33             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.14/1.33  thf('93', plain,
% 1.14/1.33      (![X57 : $i, X58 : $i, X59 : $i]:
% 1.14/1.33         (~ (zip_tseitin_0 @ X57 @ X58)
% 1.14/1.33          | (zip_tseitin_1 @ X59 @ X57 @ X58)
% 1.14/1.33          | ~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X57))))),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.14/1.33  thf('94', plain,
% 1.14/1.33      (((zip_tseitin_1 @ sk_C_3 @ sk_B_1 @ sk_A)
% 1.14/1.33        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 1.14/1.33      inference('sup-', [status(thm)], ['92', '93'])).
% 1.14/1.33  thf('95', plain,
% 1.14/1.33      ((((sk_B_1) = (k2_relat_1 @ sk_C_3))
% 1.14/1.33        | (zip_tseitin_1 @ sk_C_3 @ sk_B_1 @ sk_A))),
% 1.14/1.33      inference('sup-', [status(thm)], ['91', '94'])).
% 1.14/1.33  thf('96', plain, (((k2_relat_1 @ sk_C_3) != (sk_B_1))),
% 1.14/1.33      inference('demod', [status(thm)], ['25', '28'])).
% 1.14/1.33  thf('97', plain, ((zip_tseitin_1 @ sk_C_3 @ sk_B_1 @ sk_A)),
% 1.14/1.33      inference('simplify_reflect-', [status(thm)], ['95', '96'])).
% 1.14/1.33  thf('98', plain, (((sk_A) = (k1_relat_1 @ sk_C_3))),
% 1.14/1.33      inference('demod', [status(thm)], ['78', '97'])).
% 1.14/1.33  thf(t12_funct_1, axiom,
% 1.14/1.33    (![A:$i,B:$i]:
% 1.14/1.33     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.14/1.33       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 1.14/1.33         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 1.14/1.33  thf('99', plain,
% 1.14/1.33      (![X31 : $i, X32 : $i]:
% 1.14/1.33         (~ (r2_hidden @ X31 @ (k1_relat_1 @ X32))
% 1.14/1.33          | (r2_hidden @ (k1_funct_1 @ X32 @ X31) @ (k2_relat_1 @ X32))
% 1.14/1.33          | ~ (v1_funct_1 @ X32)
% 1.14/1.33          | ~ (v1_relat_1 @ X32))),
% 1.14/1.33      inference('cnf', [status(esa)], [t12_funct_1])).
% 1.14/1.33  thf('100', plain,
% 1.14/1.33      (![X0 : $i]:
% 1.14/1.33         (~ (r2_hidden @ X0 @ sk_A)
% 1.14/1.33          | ~ (v1_relat_1 @ sk_C_3)
% 1.14/1.33          | ~ (v1_funct_1 @ sk_C_3)
% 1.14/1.33          | (r2_hidden @ (k1_funct_1 @ sk_C_3 @ X0) @ (k2_relat_1 @ sk_C_3)))),
% 1.14/1.33      inference('sup-', [status(thm)], ['98', '99'])).
% 1.14/1.33  thf('101', plain, ((v1_relat_1 @ sk_C_3)),
% 1.14/1.33      inference('demod', [status(thm)], ['7', '8'])).
% 1.14/1.33  thf('102', plain, ((v1_funct_1 @ sk_C_3)),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('103', plain,
% 1.14/1.33      (![X0 : $i]:
% 1.14/1.33         (~ (r2_hidden @ X0 @ sk_A)
% 1.14/1.33          | (r2_hidden @ (k1_funct_1 @ sk_C_3 @ X0) @ (k2_relat_1 @ sk_C_3)))),
% 1.14/1.33      inference('demod', [status(thm)], ['100', '101', '102'])).
% 1.14/1.33  thf('104', plain,
% 1.14/1.33      ((r2_hidden @ 
% 1.14/1.33        (k1_funct_1 @ sk_C_3 @ 
% 1.14/1.33         (sk_E @ (sk_C_2 @ (k2_relat_1 @ sk_C_3) @ sk_B_1))) @ 
% 1.14/1.33        (k2_relat_1 @ sk_C_3))),
% 1.14/1.33      inference('sup-', [status(thm)], ['71', '103'])).
% 1.14/1.33  thf('105', plain,
% 1.14/1.33      (((v1_xboole_0 @ sk_B_1)
% 1.14/1.33        | (r2_hidden @ (sk_C_2 @ (k2_relat_1 @ sk_C_3) @ sk_B_1) @ sk_B_1))),
% 1.14/1.33      inference('sup-', [status(thm)], ['30', '31'])).
% 1.14/1.33  thf('106', plain,
% 1.14/1.33      (![X60 : $i]:
% 1.14/1.33         (~ (r2_hidden @ X60 @ sk_B_1)
% 1.14/1.33          | ((X60) = (k1_funct_1 @ sk_C_3 @ (sk_E @ X60))))),
% 1.14/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.33  thf('107', plain,
% 1.14/1.33      (((v1_xboole_0 @ sk_B_1)
% 1.14/1.33        | ((sk_C_2 @ (k2_relat_1 @ sk_C_3) @ sk_B_1)
% 1.14/1.33            = (k1_funct_1 @ sk_C_3 @ 
% 1.14/1.33               (sk_E @ (sk_C_2 @ (k2_relat_1 @ sk_C_3) @ sk_B_1)))))),
% 1.14/1.33      inference('sup-', [status(thm)], ['105', '106'])).
% 1.14/1.33  thf('108', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.14/1.33      inference('sup-', [status(thm)], ['47', '69'])).
% 1.14/1.33  thf('109', plain,
% 1.14/1.33      (((sk_C_2 @ (k2_relat_1 @ sk_C_3) @ sk_B_1)
% 1.14/1.33         = (k1_funct_1 @ sk_C_3 @ 
% 1.14/1.33            (sk_E @ (sk_C_2 @ (k2_relat_1 @ sk_C_3) @ sk_B_1))))),
% 1.14/1.33      inference('clc', [status(thm)], ['107', '108'])).
% 1.14/1.33  thf('110', plain,
% 1.14/1.33      ((r2_hidden @ (sk_C_2 @ (k2_relat_1 @ sk_C_3) @ sk_B_1) @ 
% 1.14/1.33        (k2_relat_1 @ sk_C_3))),
% 1.14/1.33      inference('demod', [status(thm)], ['104', '109'])).
% 1.14/1.33  thf('111', plain,
% 1.14/1.33      (![X17 : $i, X18 : $i]:
% 1.14/1.33         (~ (r2_hidden @ (sk_C_2 @ X17 @ X18) @ X17)
% 1.14/1.33          | ((X18) = (X17))
% 1.14/1.33          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 1.14/1.33      inference('cnf', [status(esa)], [t49_subset_1])).
% 1.14/1.33  thf('112', plain,
% 1.14/1.33      ((~ (m1_subset_1 @ (k2_relat_1 @ sk_C_3) @ (k1_zfmisc_1 @ sk_B_1))
% 1.14/1.33        | ((sk_B_1) = (k2_relat_1 @ sk_C_3)))),
% 1.14/1.33      inference('sup-', [status(thm)], ['110', '111'])).
% 1.14/1.33  thf('113', plain,
% 1.14/1.33      ((m1_subset_1 @ (k2_relat_1 @ sk_C_3) @ (k1_zfmisc_1 @ sk_B_1))),
% 1.14/1.33      inference('sup+', [status(thm)], ['14', '21'])).
% 1.14/1.33  thf('114', plain, (((sk_B_1) = (k2_relat_1 @ sk_C_3))),
% 1.14/1.33      inference('demod', [status(thm)], ['112', '113'])).
% 1.14/1.33  thf('115', plain, (((k2_relat_1 @ sk_C_3) != (sk_B_1))),
% 1.14/1.33      inference('demod', [status(thm)], ['25', '28'])).
% 1.14/1.33  thf('116', plain, ($false),
% 1.14/1.33      inference('simplify_reflect-', [status(thm)], ['114', '115'])).
% 1.14/1.33  
% 1.14/1.33  % SZS output end Refutation
% 1.14/1.33  
% 1.14/1.34  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
