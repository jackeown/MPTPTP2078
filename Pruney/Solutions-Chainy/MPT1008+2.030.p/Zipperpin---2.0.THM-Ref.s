%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qZRYQnvSDT

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:35 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 179 expanded)
%              Number of leaves         :   42 (  73 expanded)
%              Depth                    :   12
%              Number of atoms          :  644 (2091 expanded)
%              Number of equality atoms :   60 ( 165 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t62_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
          = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
            = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_funct_2])).

thf('0',plain,(
    v1_funct_2 @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ( X30
        = ( k1_relset_1 @ X30 @ X31 @ X32 ) )
      | ~ ( zip_tseitin_1 @ X32 @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
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

thf('5',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X34 )
      | ( zip_tseitin_1 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('15',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['13','15'])).

thf(t117_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('17',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X15 ) )
      | ( ( k11_relat_1 @ X15 @ X14 )
        = ( k1_tarski @ ( k1_funct_1 @ X15 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k11_relat_1 @ sk_C_1 @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('20',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('21',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k11_relat_1 @ sk_C_1 @ sk_A )
    = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','21','22'])).

thf('24',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('25',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('26',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('27',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('28',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k11_relat_1 @ X8 @ X9 )
        = ( k9_relat_1 @ X8 @ ( k1_tarski @ X9 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
        = ( k9_relat_1 @ X1 @ ( k2_tarski @ X0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k11_relat_1 @ sk_C_1 @ X0 )
      = ( k9_relat_1 @ sk_C_1 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k11_relat_1 @ sk_C_1 @ X0 )
      = ( k9_relat_1 @ sk_C_1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','30'])).

thf('32',plain,
    ( ( k11_relat_1 @ sk_C_1 @ sk_A )
    = ( k9_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['24','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('34',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v4_relat_1 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('35',plain,(
    v4_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12
        = ( k7_relat_1 @ X12 @ X13 ) )
      | ~ ( v4_relat_1 @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1
      = ( k7_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('39',plain,
    ( sk_C_1
    = ( k7_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('41',plain,
    ( sk_C_1
    = ( k7_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('42',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) )
        = ( k9_relat_1 @ X10 @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('43',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k9_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('45',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k9_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k11_relat_1 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['32','45'])).

thf('47',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','46'])).

thf('48',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('50',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X27 @ X25 )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('51',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','51'])).

thf('53',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['47','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qZRYQnvSDT
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:23:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.53  % Solved by: fo/fo7.sh
% 0.35/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.53  % done 95 iterations in 0.084s
% 0.35/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.53  % SZS output start Refutation
% 0.35/0.53  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.35/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.35/0.53  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.35/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.35/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.35/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.35/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.53  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.35/0.53  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.35/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.35/0.53  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.35/0.53  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.35/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.35/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.53  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.35/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.53  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.35/0.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.35/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.53  thf(t62_funct_2, conjecture,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.35/0.53         ( m1_subset_1 @
% 0.35/0.53           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.35/0.53       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.35/0.53         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.35/0.53           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.35/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.35/0.53        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.35/0.53            ( m1_subset_1 @
% 0.35/0.53              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.35/0.53          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.35/0.53            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.35/0.53              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.35/0.53    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.35/0.53  thf('0', plain, ((v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(d1_funct_2, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.53       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.35/0.53           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.35/0.53             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.35/0.53         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.35/0.53           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.35/0.53             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.35/0.53  thf(zf_stmt_1, axiom,
% 0.35/0.53    (![C:$i,B:$i,A:$i]:
% 0.35/0.53     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.35/0.53       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.35/0.53  thf('1', plain,
% 0.35/0.53      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.35/0.53         (~ (v1_funct_2 @ X32 @ X30 @ X31)
% 0.35/0.53          | ((X30) = (k1_relset_1 @ X30 @ X31 @ X32))
% 0.35/0.53          | ~ (zip_tseitin_1 @ X32 @ X31 @ X30))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.35/0.53  thf('2', plain,
% 0.35/0.53      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.35/0.53        | ((k1_tarski @ sk_A)
% 0.35/0.53            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.35/0.53  thf(zf_stmt_2, axiom,
% 0.35/0.53    (![B:$i,A:$i]:
% 0.35/0.53     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.35/0.53       ( zip_tseitin_0 @ B @ A ) ))).
% 0.35/0.53  thf('3', plain,
% 0.35/0.53      (![X28 : $i, X29 : $i]:
% 0.35/0.53         ((zip_tseitin_0 @ X28 @ X29) | ((X28) = (k1_xboole_0)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.35/0.53  thf('4', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_C_1 @ 
% 0.35/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.35/0.53  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.35/0.53  thf(zf_stmt_5, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.53       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.35/0.53         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.35/0.53           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.35/0.53             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.35/0.53  thf('5', plain,
% 0.35/0.53      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.35/0.53         (~ (zip_tseitin_0 @ X33 @ X34)
% 0.35/0.53          | (zip_tseitin_1 @ X35 @ X33 @ X34)
% 0.35/0.53          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.35/0.53  thf('6', plain,
% 0.35/0.53      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.35/0.53        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.35/0.53  thf('7', plain,
% 0.35/0.53      ((((sk_B) = (k1_xboole_0))
% 0.35/0.53        | (zip_tseitin_1 @ sk_C_1 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['3', '6'])).
% 0.35/0.53  thf('8', plain, (((sk_B) != (k1_xboole_0))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('9', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B @ (k1_tarski @ sk_A))),
% 0.35/0.53      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.35/0.53  thf('10', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_C_1 @ 
% 0.35/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(redefinition_k1_relset_1, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.53       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.35/0.53  thf('11', plain,
% 0.35/0.53      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.35/0.53         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 0.35/0.53          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.35/0.53      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.35/0.53  thf('12', plain,
% 0.35/0.53      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 0.35/0.53         = (k1_relat_1 @ sk_C_1))),
% 0.35/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.35/0.53  thf('13', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.35/0.53      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.35/0.53  thf(d1_tarski, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.35/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.35/0.53  thf('14', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.53         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.35/0.53      inference('cnf', [status(esa)], [d1_tarski])).
% 0.35/0.53  thf('15', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.35/0.53      inference('simplify', [status(thm)], ['14'])).
% 0.35/0.53  thf('16', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))),
% 0.35/0.53      inference('sup+', [status(thm)], ['13', '15'])).
% 0.35/0.53  thf(t117_funct_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.35/0.53       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.35/0.53         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.35/0.53  thf('17', plain,
% 0.35/0.53      (![X14 : $i, X15 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X14 @ (k1_relat_1 @ X15))
% 0.35/0.53          | ((k11_relat_1 @ X15 @ X14) = (k1_tarski @ (k1_funct_1 @ X15 @ X14)))
% 0.35/0.53          | ~ (v1_funct_1 @ X15)
% 0.35/0.53          | ~ (v1_relat_1 @ X15))),
% 0.35/0.53      inference('cnf', [status(esa)], [t117_funct_1])).
% 0.35/0.53  thf('18', plain,
% 0.35/0.53      ((~ (v1_relat_1 @ sk_C_1)
% 0.35/0.53        | ~ (v1_funct_1 @ sk_C_1)
% 0.35/0.53        | ((k11_relat_1 @ sk_C_1 @ sk_A)
% 0.35/0.53            = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.35/0.53  thf('19', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_C_1 @ 
% 0.35/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(cc1_relset_1, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.53       ( v1_relat_1 @ C ) ))).
% 0.35/0.53  thf('20', plain,
% 0.35/0.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.35/0.53         ((v1_relat_1 @ X16)
% 0.35/0.53          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.35/0.53      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.35/0.53  thf('21', plain, ((v1_relat_1 @ sk_C_1)),
% 0.35/0.53      inference('sup-', [status(thm)], ['19', '20'])).
% 0.35/0.53  thf('22', plain, ((v1_funct_1 @ sk_C_1)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('23', plain,
% 0.35/0.53      (((k11_relat_1 @ sk_C_1 @ sk_A)
% 0.35/0.53         = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.35/0.53      inference('demod', [status(thm)], ['18', '21', '22'])).
% 0.35/0.53  thf('24', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.35/0.53      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.35/0.53  thf(t69_enumset1, axiom,
% 0.35/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.35/0.53  thf('25', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.35/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.35/0.53  thf('26', plain, ((v1_relat_1 @ sk_C_1)),
% 0.35/0.53      inference('sup-', [status(thm)], ['19', '20'])).
% 0.35/0.53  thf('27', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.35/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.35/0.53  thf(d16_relat_1, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( v1_relat_1 @ A ) =>
% 0.35/0.53       ( ![B:$i]:
% 0.35/0.53         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.35/0.53  thf('28', plain,
% 0.35/0.53      (![X8 : $i, X9 : $i]:
% 0.35/0.53         (((k11_relat_1 @ X8 @ X9) = (k9_relat_1 @ X8 @ (k1_tarski @ X9)))
% 0.35/0.53          | ~ (v1_relat_1 @ X8))),
% 0.35/0.53      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.35/0.53  thf('29', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         (((k11_relat_1 @ X1 @ X0) = (k9_relat_1 @ X1 @ (k2_tarski @ X0 @ X0)))
% 0.35/0.53          | ~ (v1_relat_1 @ X1))),
% 0.35/0.53      inference('sup+', [status(thm)], ['27', '28'])).
% 0.35/0.53  thf('30', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((k11_relat_1 @ sk_C_1 @ X0)
% 0.35/0.53           = (k9_relat_1 @ sk_C_1 @ (k2_tarski @ X0 @ X0)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['26', '29'])).
% 0.35/0.53  thf('31', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((k11_relat_1 @ sk_C_1 @ X0)
% 0.35/0.53           = (k9_relat_1 @ sk_C_1 @ (k1_tarski @ X0)))),
% 0.35/0.53      inference('sup+', [status(thm)], ['25', '30'])).
% 0.35/0.53  thf('32', plain,
% 0.35/0.53      (((k11_relat_1 @ sk_C_1 @ sk_A)
% 0.35/0.53         = (k9_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1)))),
% 0.35/0.53      inference('sup+', [status(thm)], ['24', '31'])).
% 0.35/0.53  thf('33', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_C_1 @ 
% 0.35/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(cc2_relset_1, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.53       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.35/0.53  thf('34', plain,
% 0.35/0.53      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.35/0.53         ((v4_relat_1 @ X19 @ X20)
% 0.35/0.53          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.35/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.35/0.53  thf('35', plain, ((v4_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A))),
% 0.35/0.53      inference('sup-', [status(thm)], ['33', '34'])).
% 0.35/0.53  thf(t209_relat_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.35/0.53       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.35/0.53  thf('36', plain,
% 0.35/0.53      (![X12 : $i, X13 : $i]:
% 0.35/0.53         (((X12) = (k7_relat_1 @ X12 @ X13))
% 0.35/0.53          | ~ (v4_relat_1 @ X12 @ X13)
% 0.35/0.53          | ~ (v1_relat_1 @ X12))),
% 0.35/0.53      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.35/0.53  thf('37', plain,
% 0.35/0.53      ((~ (v1_relat_1 @ sk_C_1)
% 0.35/0.53        | ((sk_C_1) = (k7_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['35', '36'])).
% 0.35/0.53  thf('38', plain, ((v1_relat_1 @ sk_C_1)),
% 0.35/0.53      inference('sup-', [status(thm)], ['19', '20'])).
% 0.35/0.53  thf('39', plain, (((sk_C_1) = (k7_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A)))),
% 0.35/0.53      inference('demod', [status(thm)], ['37', '38'])).
% 0.35/0.53  thf('40', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.35/0.53      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.35/0.53  thf('41', plain,
% 0.35/0.53      (((sk_C_1) = (k7_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1)))),
% 0.35/0.53      inference('demod', [status(thm)], ['39', '40'])).
% 0.35/0.53  thf(t148_relat_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( v1_relat_1 @ B ) =>
% 0.35/0.53       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.35/0.53  thf('42', plain,
% 0.35/0.53      (![X10 : $i, X11 : $i]:
% 0.35/0.53         (((k2_relat_1 @ (k7_relat_1 @ X10 @ X11)) = (k9_relat_1 @ X10 @ X11))
% 0.35/0.53          | ~ (v1_relat_1 @ X10))),
% 0.35/0.53      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.35/0.53  thf('43', plain,
% 0.35/0.53      ((((k2_relat_1 @ sk_C_1) = (k9_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1)))
% 0.35/0.53        | ~ (v1_relat_1 @ sk_C_1))),
% 0.35/0.53      inference('sup+', [status(thm)], ['41', '42'])).
% 0.35/0.53  thf('44', plain, ((v1_relat_1 @ sk_C_1)),
% 0.35/0.53      inference('sup-', [status(thm)], ['19', '20'])).
% 0.35/0.53  thf('45', plain,
% 0.35/0.53      (((k2_relat_1 @ sk_C_1) = (k9_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1)))),
% 0.35/0.53      inference('demod', [status(thm)], ['43', '44'])).
% 0.35/0.53  thf('46', plain, (((k2_relat_1 @ sk_C_1) = (k11_relat_1 @ sk_C_1 @ sk_A))),
% 0.35/0.53      inference('sup+', [status(thm)], ['32', '45'])).
% 0.35/0.53  thf('47', plain,
% 0.35/0.53      (((k2_relat_1 @ sk_C_1) = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.35/0.53      inference('demod', [status(thm)], ['23', '46'])).
% 0.35/0.53  thf('48', plain,
% 0.35/0.53      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 0.35/0.53         != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('49', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_C_1 @ 
% 0.35/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(redefinition_k2_relset_1, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.53       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.35/0.53  thf('50', plain,
% 0.35/0.53      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.35/0.53         (((k2_relset_1 @ X26 @ X27 @ X25) = (k2_relat_1 @ X25))
% 0.35/0.53          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.35/0.53      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.35/0.53  thf('51', plain,
% 0.35/0.53      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 0.35/0.53         = (k2_relat_1 @ sk_C_1))),
% 0.35/0.53      inference('sup-', [status(thm)], ['49', '50'])).
% 0.35/0.53  thf('52', plain,
% 0.35/0.53      (((k2_relat_1 @ sk_C_1) != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.35/0.53      inference('demod', [status(thm)], ['48', '51'])).
% 0.35/0.53  thf('53', plain, ($false),
% 0.35/0.53      inference('simplify_reflect-', [status(thm)], ['47', '52'])).
% 0.35/0.53  
% 0.35/0.53  % SZS output end Refutation
% 0.35/0.53  
% 0.35/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
