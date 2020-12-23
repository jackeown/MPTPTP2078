%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZxlZQZP6rC

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:17 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 248 expanded)
%              Number of leaves         :   43 (  94 expanded)
%              Depth                    :   18
%              Number of atoms          :  790 (2906 expanded)
%              Number of equality atoms :   51 ( 175 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v5_relat_1 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_C_2 @ sk_B_1 ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v5_relat_1 @ X10 @ X11 )
      | ( r1_tarski @ ( k2_relat_1 @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('7',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['4','7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k2_relat_1 @ sk_C_2 ) )
    | ( sk_B_1
      = ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['4','7'])).

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

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X12 @ X13 ) @ X13 )
      | ( r1_tarski @ X13 @ ( k2_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t19_funct_1])).

thf('13',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X1 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( ( k2_relat_1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
      = sk_B_1 )
    | ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_B_1 ) @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('18',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
      = sk_B_1 )
    | ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_B_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('22',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B_1 ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,(
    r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_B_1 ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X35: $i] :
      ( ~ ( r2_hidden @ X35 @ sk_B_1 )
      | ( X35
        = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( sk_C_1 @ sk_C_2 @ sk_B_1 )
    = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C_1 @ sk_C_2 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 ),
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

thf('28',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('29',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('30',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('31',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('34',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('35',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('37',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('41',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_B_1 )
      | ~ ( v1_xboole_0 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('48',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('50',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['4','7'])).

thf('51',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) )
    | ( r2_hidden @ ( sk_B @ ( k2_relat_1 @ sk_C_2 ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('55',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['48','55'])).

thf('57',plain,(
    zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['36','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('59',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('60',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['29','57','60'])).

thf('62',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( sk_C_1 @ X12 @ X13 )
       != ( k1_funct_1 @ X12 @ X14 ) )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X12 ) )
      | ( r1_tarski @ X13 @ ( k2_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t19_funct_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r1_tarski @ X1 @ ( k2_relat_1 @ sk_C_2 ) )
      | ( ( sk_C_1 @ sk_C_2 @ X1 )
       != ( k1_funct_1 @ sk_C_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('65',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r1_tarski @ X1 @ ( k2_relat_1 @ sk_C_2 ) )
      | ( ( sk_C_1 @ sk_C_2 @ X1 )
       != ( k1_funct_1 @ sk_C_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ sk_C_2 @ X0 )
       != ( sk_C_1 @ sk_C_2 @ sk_B_1 ) )
      | ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ ( sk_E @ ( sk_C_1 @ sk_C_2 @ sk_B_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','66'])).

thf('68',plain,(
    r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_B_1 ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['18','23'])).

thf('69',plain,(
    ! [X35: $i] :
      ( ~ ( r2_hidden @ X35 @ sk_B_1 )
      | ( r2_hidden @ ( sk_E @ X35 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    r2_hidden @ ( sk_E @ ( sk_C_1 @ sk_C_2 @ sk_B_1 ) ) @ sk_A ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ sk_C_2 @ X0 )
       != ( sk_C_1 @ sk_C_2 @ sk_B_1 ) )
      | ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['67','70'])).

thf('72',plain,(
    r1_tarski @ sk_B_1 @ ( k2_relat_1 @ sk_C_2 ) ),
    inference(eq_res,[status(thm)],['71'])).

thf('73',plain,
    ( sk_B_1
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['10','72'])).

thf('74',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B_1 ),
    inference(demod,[status(thm)],['19','22'])).

thf('75',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['73','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZxlZQZP6rC
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:15:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.51/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.51/0.70  % Solved by: fo/fo7.sh
% 0.51/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.70  % done 175 iterations in 0.236s
% 0.51/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.51/0.70  % SZS output start Refutation
% 0.51/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.51/0.70  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.51/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.51/0.70  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.51/0.70  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.51/0.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.51/0.70  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.51/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.51/0.70  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.51/0.70  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.51/0.70  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.51/0.70  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.51/0.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.51/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.51/0.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.51/0.70  thf(sk_E_type, type, sk_E: $i > $i).
% 0.51/0.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.51/0.70  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.51/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.51/0.70  thf(sk_B_type, type, sk_B: $i > $i).
% 0.51/0.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.51/0.70  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.51/0.70  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.51/0.70  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.51/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.51/0.70  thf(t16_funct_2, conjecture,
% 0.51/0.70    (![A:$i,B:$i,C:$i]:
% 0.51/0.70     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.51/0.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.51/0.70       ( ( ![D:$i]:
% 0.51/0.70           ( ~( ( r2_hidden @ D @ B ) & 
% 0.51/0.70                ( ![E:$i]:
% 0.51/0.70                  ( ~( ( r2_hidden @ E @ A ) & 
% 0.51/0.70                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.51/0.70         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.51/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.70    (~( ![A:$i,B:$i,C:$i]:
% 0.51/0.70        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.51/0.70            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.51/0.70          ( ( ![D:$i]:
% 0.51/0.70              ( ~( ( r2_hidden @ D @ B ) & 
% 0.51/0.70                   ( ![E:$i]:
% 0.51/0.70                     ( ~( ( r2_hidden @ E @ A ) & 
% 0.51/0.70                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.51/0.70            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 0.51/0.70    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 0.51/0.70  thf('0', plain,
% 0.51/0.70      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf(cc2_relset_1, axiom,
% 0.51/0.70    (![A:$i,B:$i,C:$i]:
% 0.51/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.70       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.51/0.70  thf('1', plain,
% 0.51/0.70      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.51/0.70         ((v5_relat_1 @ X18 @ X20)
% 0.51/0.70          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.51/0.70      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.51/0.70  thf('2', plain, ((v5_relat_1 @ sk_C_2 @ sk_B_1)),
% 0.51/0.70      inference('sup-', [status(thm)], ['0', '1'])).
% 0.51/0.70  thf(d19_relat_1, axiom,
% 0.51/0.70    (![A:$i,B:$i]:
% 0.51/0.70     ( ( v1_relat_1 @ B ) =>
% 0.51/0.70       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.51/0.70  thf('3', plain,
% 0.51/0.70      (![X10 : $i, X11 : $i]:
% 0.51/0.70         (~ (v5_relat_1 @ X10 @ X11)
% 0.51/0.70          | (r1_tarski @ (k2_relat_1 @ X10) @ X11)
% 0.51/0.70          | ~ (v1_relat_1 @ X10))),
% 0.51/0.70      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.51/0.70  thf('4', plain,
% 0.51/0.70      ((~ (v1_relat_1 @ sk_C_2) | (r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B_1))),
% 0.51/0.70      inference('sup-', [status(thm)], ['2', '3'])).
% 0.51/0.70  thf('5', plain,
% 0.51/0.70      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf(cc1_relset_1, axiom,
% 0.51/0.70    (![A:$i,B:$i,C:$i]:
% 0.51/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.70       ( v1_relat_1 @ C ) ))).
% 0.51/0.70  thf('6', plain,
% 0.51/0.70      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.51/0.70         ((v1_relat_1 @ X15)
% 0.51/0.70          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.51/0.70      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.51/0.70  thf('7', plain, ((v1_relat_1 @ sk_C_2)),
% 0.51/0.70      inference('sup-', [status(thm)], ['5', '6'])).
% 0.51/0.70  thf('8', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B_1)),
% 0.51/0.70      inference('demod', [status(thm)], ['4', '7'])).
% 0.51/0.70  thf(d10_xboole_0, axiom,
% 0.51/0.70    (![A:$i,B:$i]:
% 0.51/0.70     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.51/0.70  thf('9', plain,
% 0.51/0.70      (![X7 : $i, X9 : $i]:
% 0.51/0.70         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.51/0.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.51/0.70  thf('10', plain,
% 0.51/0.70      ((~ (r1_tarski @ sk_B_1 @ (k2_relat_1 @ sk_C_2))
% 0.51/0.70        | ((sk_B_1) = (k2_relat_1 @ sk_C_2)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['8', '9'])).
% 0.51/0.70  thf('11', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B_1)),
% 0.51/0.70      inference('demod', [status(thm)], ['4', '7'])).
% 0.51/0.70  thf(t19_funct_1, axiom,
% 0.51/0.70    (![A:$i,B:$i]:
% 0.51/0.70     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.51/0.70       ( ( ![C:$i]:
% 0.51/0.70           ( ~( ( r2_hidden @ C @ A ) & 
% 0.51/0.70                ( ![D:$i]:
% 0.51/0.70                  ( ~( ( r2_hidden @ D @ ( k1_relat_1 @ B ) ) & 
% 0.51/0.70                       ( ( C ) = ( k1_funct_1 @ B @ D ) ) ) ) ) ) ) ) =>
% 0.51/0.70         ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) ) ))).
% 0.51/0.70  thf('12', plain,
% 0.51/0.70      (![X12 : $i, X13 : $i]:
% 0.51/0.70         ((r2_hidden @ (sk_C_1 @ X12 @ X13) @ X13)
% 0.51/0.70          | (r1_tarski @ X13 @ (k2_relat_1 @ X12))
% 0.51/0.70          | ~ (v1_funct_1 @ X12)
% 0.51/0.70          | ~ (v1_relat_1 @ X12))),
% 0.51/0.70      inference('cnf', [status(esa)], [t19_funct_1])).
% 0.51/0.70  thf('13', plain,
% 0.51/0.70      (![X7 : $i, X9 : $i]:
% 0.51/0.70         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.51/0.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.51/0.70  thf('14', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]:
% 0.51/0.70         (~ (v1_relat_1 @ X0)
% 0.51/0.70          | ~ (v1_funct_1 @ X0)
% 0.51/0.70          | (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X1)
% 0.51/0.70          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.51/0.70          | ((k2_relat_1 @ X0) = (X1)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['12', '13'])).
% 0.51/0.70  thf('15', plain,
% 0.51/0.70      ((((k2_relat_1 @ sk_C_2) = (sk_B_1))
% 0.51/0.70        | (r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_B_1) @ sk_B_1)
% 0.51/0.70        | ~ (v1_funct_1 @ sk_C_2)
% 0.51/0.70        | ~ (v1_relat_1 @ sk_C_2))),
% 0.51/0.70      inference('sup-', [status(thm)], ['11', '14'])).
% 0.51/0.70  thf('16', plain, ((v1_funct_1 @ sk_C_2)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('17', plain, ((v1_relat_1 @ sk_C_2)),
% 0.51/0.70      inference('sup-', [status(thm)], ['5', '6'])).
% 0.51/0.70  thf('18', plain,
% 0.51/0.70      ((((k2_relat_1 @ sk_C_2) = (sk_B_1))
% 0.51/0.70        | (r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_B_1) @ sk_B_1))),
% 0.51/0.70      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.51/0.70  thf('19', plain, (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) != (sk_B_1))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('20', plain,
% 0.51/0.70      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf(redefinition_k2_relset_1, axiom,
% 0.51/0.70    (![A:$i,B:$i,C:$i]:
% 0.51/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.70       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.51/0.70  thf('21', plain,
% 0.51/0.70      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.51/0.70         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 0.51/0.70          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.51/0.70      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.51/0.70  thf('22', plain,
% 0.51/0.70      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.51/0.70      inference('sup-', [status(thm)], ['20', '21'])).
% 0.51/0.70  thf('23', plain, (((k2_relat_1 @ sk_C_2) != (sk_B_1))),
% 0.51/0.70      inference('demod', [status(thm)], ['19', '22'])).
% 0.51/0.70  thf('24', plain, ((r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_B_1) @ sk_B_1)),
% 0.51/0.70      inference('simplify_reflect-', [status(thm)], ['18', '23'])).
% 0.51/0.70  thf('25', plain,
% 0.51/0.70      (![X35 : $i]:
% 0.51/0.70         (~ (r2_hidden @ X35 @ sk_B_1)
% 0.51/0.70          | ((X35) = (k1_funct_1 @ sk_C_2 @ (sk_E @ X35))))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('26', plain,
% 0.51/0.70      (((sk_C_1 @ sk_C_2 @ sk_B_1)
% 0.51/0.70         = (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C_1 @ sk_C_2 @ sk_B_1))))),
% 0.51/0.70      inference('sup-', [status(thm)], ['24', '25'])).
% 0.51/0.70  thf('27', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf(d1_funct_2, axiom,
% 0.51/0.70    (![A:$i,B:$i,C:$i]:
% 0.51/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.70       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.51/0.70           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.51/0.70             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.51/0.70         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.51/0.70           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.51/0.70             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.51/0.70  thf(zf_stmt_1, axiom,
% 0.51/0.70    (![C:$i,B:$i,A:$i]:
% 0.51/0.70     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.51/0.70       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.51/0.70  thf('28', plain,
% 0.51/0.70      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.51/0.70         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 0.51/0.70          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 0.51/0.70          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.51/0.70  thf('29', plain,
% 0.51/0.70      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 0.51/0.70        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['27', '28'])).
% 0.51/0.70  thf(zf_stmt_2, axiom,
% 0.51/0.70    (![B:$i,A:$i]:
% 0.51/0.70     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.51/0.70       ( zip_tseitin_0 @ B @ A ) ))).
% 0.51/0.70  thf('30', plain,
% 0.51/0.70      (![X27 : $i, X28 : $i]:
% 0.51/0.70         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.51/0.70  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.51/0.70  thf('31', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.51/0.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.51/0.70  thf('32', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.51/0.70      inference('sup+', [status(thm)], ['30', '31'])).
% 0.51/0.70  thf('33', plain,
% 0.51/0.70      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.51/0.70  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.51/0.70  thf(zf_stmt_5, axiom,
% 0.51/0.70    (![A:$i,B:$i,C:$i]:
% 0.51/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.70       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.51/0.70         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.51/0.70           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.51/0.70             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.51/0.70  thf('34', plain,
% 0.51/0.70      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.51/0.70         (~ (zip_tseitin_0 @ X32 @ X33)
% 0.51/0.70          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 0.51/0.70          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.51/0.70  thf('35', plain,
% 0.51/0.70      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 0.51/0.70        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.51/0.70      inference('sup-', [status(thm)], ['33', '34'])).
% 0.51/0.70  thf('36', plain,
% 0.51/0.70      (((v1_xboole_0 @ sk_B_1) | (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A))),
% 0.51/0.70      inference('sup-', [status(thm)], ['32', '35'])).
% 0.51/0.70  thf(d3_tarski, axiom,
% 0.51/0.70    (![A:$i,B:$i]:
% 0.51/0.70     ( ( r1_tarski @ A @ B ) <=>
% 0.51/0.70       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.51/0.70  thf('37', plain,
% 0.51/0.70      (![X4 : $i, X6 : $i]:
% 0.51/0.70         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.51/0.70      inference('cnf', [status(esa)], [d3_tarski])).
% 0.51/0.70  thf(d1_xboole_0, axiom,
% 0.51/0.70    (![A:$i]:
% 0.51/0.70     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.51/0.70  thf('38', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.51/0.70      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.51/0.70  thf('39', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.51/0.70      inference('sup-', [status(thm)], ['37', '38'])).
% 0.51/0.70  thf('40', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.51/0.70      inference('sup-', [status(thm)], ['37', '38'])).
% 0.51/0.70  thf('41', plain,
% 0.51/0.70      (![X7 : $i, X9 : $i]:
% 0.51/0.70         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.51/0.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.51/0.70  thf('42', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]:
% 0.51/0.70         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['40', '41'])).
% 0.51/0.70  thf('43', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]:
% 0.51/0.70         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.51/0.70      inference('sup-', [status(thm)], ['39', '42'])).
% 0.51/0.70  thf('44', plain, (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) != (sk_B_1))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('45', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (((X0) != (sk_B_1))
% 0.51/0.70          | ~ (v1_xboole_0 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2))
% 0.51/0.70          | ~ (v1_xboole_0 @ X0))),
% 0.51/0.70      inference('sup-', [status(thm)], ['43', '44'])).
% 0.51/0.70  thf('46', plain,
% 0.51/0.70      ((~ (v1_xboole_0 @ sk_B_1)
% 0.51/0.70        | ~ (v1_xboole_0 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2)))),
% 0.51/0.70      inference('simplify', [status(thm)], ['45'])).
% 0.51/0.70  thf('47', plain,
% 0.51/0.70      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.51/0.70      inference('sup-', [status(thm)], ['20', '21'])).
% 0.51/0.70  thf('48', plain,
% 0.51/0.70      ((~ (v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_2)))),
% 0.51/0.70      inference('demod', [status(thm)], ['46', '47'])).
% 0.51/0.70  thf('49', plain,
% 0.51/0.70      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.51/0.70      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.51/0.70  thf('50', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B_1)),
% 0.51/0.70      inference('demod', [status(thm)], ['4', '7'])).
% 0.51/0.70  thf('51', plain,
% 0.51/0.70      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.51/0.70         (~ (r2_hidden @ X3 @ X4)
% 0.51/0.70          | (r2_hidden @ X3 @ X5)
% 0.51/0.70          | ~ (r1_tarski @ X4 @ X5))),
% 0.51/0.70      inference('cnf', [status(esa)], [d3_tarski])).
% 0.51/0.70  thf('52', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         ((r2_hidden @ X0 @ sk_B_1)
% 0.51/0.70          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_2)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['50', '51'])).
% 0.51/0.70  thf('53', plain,
% 0.51/0.70      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_2))
% 0.51/0.70        | (r2_hidden @ (sk_B @ (k2_relat_1 @ sk_C_2)) @ sk_B_1))),
% 0.51/0.70      inference('sup-', [status(thm)], ['49', '52'])).
% 0.51/0.70  thf('54', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.51/0.70      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.51/0.70  thf('55', plain,
% 0.51/0.70      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_2)) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.51/0.70      inference('sup-', [status(thm)], ['53', '54'])).
% 0.51/0.70  thf('56', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.51/0.70      inference('clc', [status(thm)], ['48', '55'])).
% 0.51/0.70  thf('57', plain, ((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)),
% 0.51/0.70      inference('clc', [status(thm)], ['36', '56'])).
% 0.51/0.70  thf('58', plain,
% 0.51/0.70      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf(redefinition_k1_relset_1, axiom,
% 0.51/0.70    (![A:$i,B:$i,C:$i]:
% 0.51/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.70       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.51/0.70  thf('59', plain,
% 0.51/0.70      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.51/0.70         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 0.51/0.70          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.51/0.70      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.51/0.70  thf('60', plain,
% 0.51/0.70      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 0.51/0.70      inference('sup-', [status(thm)], ['58', '59'])).
% 0.51/0.70  thf('61', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 0.51/0.70      inference('demod', [status(thm)], ['29', '57', '60'])).
% 0.51/0.70  thf('62', plain,
% 0.51/0.70      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.51/0.70         (((sk_C_1 @ X12 @ X13) != (k1_funct_1 @ X12 @ X14))
% 0.51/0.70          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X12))
% 0.51/0.70          | (r1_tarski @ X13 @ (k2_relat_1 @ X12))
% 0.51/0.70          | ~ (v1_funct_1 @ X12)
% 0.51/0.70          | ~ (v1_relat_1 @ X12))),
% 0.51/0.70      inference('cnf', [status(esa)], [t19_funct_1])).
% 0.51/0.70  thf('63', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]:
% 0.51/0.70         (~ (r2_hidden @ X0 @ sk_A)
% 0.51/0.70          | ~ (v1_relat_1 @ sk_C_2)
% 0.51/0.70          | ~ (v1_funct_1 @ sk_C_2)
% 0.51/0.70          | (r1_tarski @ X1 @ (k2_relat_1 @ sk_C_2))
% 0.51/0.70          | ((sk_C_1 @ sk_C_2 @ X1) != (k1_funct_1 @ sk_C_2 @ X0)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['61', '62'])).
% 0.51/0.70  thf('64', plain, ((v1_relat_1 @ sk_C_2)),
% 0.51/0.70      inference('sup-', [status(thm)], ['5', '6'])).
% 0.51/0.70  thf('65', plain, ((v1_funct_1 @ sk_C_2)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('66', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]:
% 0.51/0.70         (~ (r2_hidden @ X0 @ sk_A)
% 0.51/0.70          | (r1_tarski @ X1 @ (k2_relat_1 @ sk_C_2))
% 0.51/0.70          | ((sk_C_1 @ sk_C_2 @ X1) != (k1_funct_1 @ sk_C_2 @ X0)))),
% 0.51/0.70      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.51/0.70  thf('67', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (((sk_C_1 @ sk_C_2 @ X0) != (sk_C_1 @ sk_C_2 @ sk_B_1))
% 0.51/0.70          | (r1_tarski @ X0 @ (k2_relat_1 @ sk_C_2))
% 0.51/0.70          | ~ (r2_hidden @ (sk_E @ (sk_C_1 @ sk_C_2 @ sk_B_1)) @ sk_A))),
% 0.51/0.70      inference('sup-', [status(thm)], ['26', '66'])).
% 0.51/0.70  thf('68', plain, ((r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_B_1) @ sk_B_1)),
% 0.51/0.70      inference('simplify_reflect-', [status(thm)], ['18', '23'])).
% 0.51/0.70  thf('69', plain,
% 0.51/0.70      (![X35 : $i]:
% 0.51/0.70         (~ (r2_hidden @ X35 @ sk_B_1) | (r2_hidden @ (sk_E @ X35) @ sk_A))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('70', plain, ((r2_hidden @ (sk_E @ (sk_C_1 @ sk_C_2 @ sk_B_1)) @ sk_A)),
% 0.51/0.70      inference('sup-', [status(thm)], ['68', '69'])).
% 0.51/0.70  thf('71', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (((sk_C_1 @ sk_C_2 @ X0) != (sk_C_1 @ sk_C_2 @ sk_B_1))
% 0.51/0.70          | (r1_tarski @ X0 @ (k2_relat_1 @ sk_C_2)))),
% 0.51/0.70      inference('demod', [status(thm)], ['67', '70'])).
% 0.51/0.70  thf('72', plain, ((r1_tarski @ sk_B_1 @ (k2_relat_1 @ sk_C_2))),
% 0.51/0.70      inference('eq_res', [status(thm)], ['71'])).
% 0.51/0.70  thf('73', plain, (((sk_B_1) = (k2_relat_1 @ sk_C_2))),
% 0.51/0.70      inference('demod', [status(thm)], ['10', '72'])).
% 0.51/0.70  thf('74', plain, (((k2_relat_1 @ sk_C_2) != (sk_B_1))),
% 0.51/0.70      inference('demod', [status(thm)], ['19', '22'])).
% 0.51/0.70  thf('75', plain, ($false),
% 0.51/0.70      inference('simplify_reflect-', [status(thm)], ['73', '74'])).
% 0.51/0.70  
% 0.51/0.70  % SZS output end Refutation
% 0.51/0.70  
% 0.51/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
