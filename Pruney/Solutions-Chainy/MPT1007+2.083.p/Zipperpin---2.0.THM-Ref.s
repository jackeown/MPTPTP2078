%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fMSfDoTnBG

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:27 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 377 expanded)
%              Number of leaves         :   49 ( 133 expanded)
%              Depth                    :   15
%              Number of atoms          :  809 (4413 expanded)
%              Number of equality atoms :   80 ( 297 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('2',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( r1_tarski @ X40 @ X41 )
      | ( r2_hidden @ X40 @ X42 )
      | ( X42
       != ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('3',plain,(
    ! [X40: $i,X41: $i] :
      ( ( r2_hidden @ X40 @ ( k1_zfmisc_1 @ X41 ) )
      | ~ ( r1_tarski @ X40 @ X41 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf(t61_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_funct_2])).

thf('5',plain,(
    v1_funct_2 @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
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

thf('6',plain,(
    ! [X68: $i,X69: $i,X70: $i] :
      ( ~ ( v1_funct_2 @ X70 @ X68 @ X69 )
      | ( X68
        = ( k1_relset_1 @ X68 @ X69 @ X70 ) )
      | ~ ( zip_tseitin_1 @ X70 @ X69 @ X68 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X66: $i,X67: $i] :
      ( ( zip_tseitin_0 @ X66 @ X67 )
      | ( X66 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('9',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
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

thf('10',plain,(
    ! [X71: $i,X72: $i,X73: $i] :
      ( ~ ( zip_tseitin_0 @ X71 @ X72 )
      | ( zip_tseitin_1 @ X73 @ X71 @ X72 )
      | ~ ( m1_subset_1 @ X73 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X72 @ X71 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('11',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('16',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( ( k1_relset_1 @ X58 @ X59 @ X57 )
        = ( k1_relat_1 @ X57 ) )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X58 @ X59 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('17',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['7','14','17'])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('19',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( r2_hidden @ X45 @ X46 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X45 ) @ X46 )
       != ( k1_tarski @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) @ X0 )
       != ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['7','14','17'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) @ X0 )
       != ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('23',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('24',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('25',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( r2_hidden @ X48 @ X49 )
      | ( r2_hidden @ X48 @ X50 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf(t12_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('28',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ( ( k1_mcart_1 @ X64 )
        = X63 )
      | ~ ( r2_hidden @ X64 @ ( k2_zfmisc_1 @ ( k1_tarski @ X63 ) @ X65 ) ) ) ),
    inference(cnf,[status(esa)],[t12_mcart_1])).

thf('29',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k1_mcart_1 @ ( sk_B @ sk_C_1 ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('31',plain,(
    ! [X60: $i,X61: $i,X62: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X60 ) @ X61 )
      | ~ ( r2_hidden @ X60 @ ( k2_zfmisc_1 @ X61 @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('32',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k1_mcart_1 @ ( sk_B @ sk_C_1 ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['7','14','17'])).

thf('36',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['7','14','17'])).

thf('39',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('40',plain,(
    ! [X74: $i,X75: $i,X76: $i,X77: $i] :
      ( ~ ( r2_hidden @ X74 @ X75 )
      | ( X76 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X77 )
      | ~ ( v1_funct_2 @ X77 @ X75 @ X76 )
      | ~ ( m1_subset_1 @ X77 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X75 @ X76 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X77 @ X74 ) @ X76 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ sk_B_1 )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_funct_2 @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['7','14','17'])).

thf('44',plain,(
    v1_funct_2 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['41','44','45'])).

thf('47',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['36','48'])).

thf('50',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['49','50'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('52',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('53',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X11 @ X10 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('54',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X52 @ X53 ) )
      = ( k3_xboole_0 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X52 @ X53 ) )
      = ( k3_xboole_0 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('58',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('60',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('62',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['59','64'])).

thf('66',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['49','50'])).

thf('67',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['22','51','52','65','66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_A @ X0 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    $false ),
    inference('sup-',[status(thm)],['4','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fMSfDoTnBG
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:40:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.59  % Solved by: fo/fo7.sh
% 0.36/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.59  % done 272 iterations in 0.127s
% 0.36/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.59  % SZS output start Refutation
% 0.36/0.59  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.36/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.59  thf(sk_B_type, type, sk_B: $i > $i).
% 0.36/0.59  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.36/0.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.36/0.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.36/0.59  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.36/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.59  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.36/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.59  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.36/0.59  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.36/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.59  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.36/0.59  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.36/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.59  thf(d10_xboole_0, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.59  thf('0', plain,
% 0.36/0.59      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 0.36/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.59  thf('1', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.36/0.59      inference('simplify', [status(thm)], ['0'])).
% 0.36/0.59  thf(d1_zfmisc_1, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.36/0.59       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.36/0.59  thf('2', plain,
% 0.36/0.59      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.36/0.59         (~ (r1_tarski @ X40 @ X41)
% 0.36/0.59          | (r2_hidden @ X40 @ X42)
% 0.36/0.59          | ((X42) != (k1_zfmisc_1 @ X41)))),
% 0.36/0.59      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.36/0.59  thf('3', plain,
% 0.36/0.59      (![X40 : $i, X41 : $i]:
% 0.36/0.59         ((r2_hidden @ X40 @ (k1_zfmisc_1 @ X41)) | ~ (r1_tarski @ X40 @ X41))),
% 0.36/0.59      inference('simplify', [status(thm)], ['2'])).
% 0.36/0.59  thf('4', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['1', '3'])).
% 0.36/0.59  thf(t61_funct_2, conjecture,
% 0.36/0.59    (![A:$i,B:$i,C:$i]:
% 0.36/0.59     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.36/0.59         ( m1_subset_1 @
% 0.36/0.59           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.36/0.59       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.36/0.59         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.36/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.59    (~( ![A:$i,B:$i,C:$i]:
% 0.36/0.59        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.36/0.59            ( m1_subset_1 @
% 0.36/0.59              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.36/0.59          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.36/0.59            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.36/0.59    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.36/0.59  thf('5', plain, ((v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf(d1_funct_2, axiom,
% 0.36/0.59    (![A:$i,B:$i,C:$i]:
% 0.36/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.59       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.36/0.59           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.36/0.59             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.36/0.59         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.36/0.59           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.36/0.59             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.36/0.59  thf(zf_stmt_1, axiom,
% 0.36/0.59    (![C:$i,B:$i,A:$i]:
% 0.36/0.59     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.36/0.59       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.36/0.59  thf('6', plain,
% 0.36/0.59      (![X68 : $i, X69 : $i, X70 : $i]:
% 0.36/0.59         (~ (v1_funct_2 @ X70 @ X68 @ X69)
% 0.36/0.59          | ((X68) = (k1_relset_1 @ X68 @ X69 @ X70))
% 0.36/0.59          | ~ (zip_tseitin_1 @ X70 @ X69 @ X68))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.36/0.59  thf('7', plain,
% 0.36/0.59      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.36/0.59        | ((k1_tarski @ sk_A)
% 0.36/0.59            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C_1)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['5', '6'])).
% 0.36/0.59  thf(zf_stmt_2, axiom,
% 0.36/0.59    (![B:$i,A:$i]:
% 0.36/0.59     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.36/0.59       ( zip_tseitin_0 @ B @ A ) ))).
% 0.36/0.59  thf('8', plain,
% 0.36/0.59      (![X66 : $i, X67 : $i]:
% 0.36/0.59         ((zip_tseitin_0 @ X66 @ X67) | ((X66) = (k1_xboole_0)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.36/0.59  thf('9', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_C_1 @ 
% 0.36/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.36/0.59  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.36/0.59  thf(zf_stmt_5, axiom,
% 0.36/0.59    (![A:$i,B:$i,C:$i]:
% 0.36/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.59       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.36/0.59         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.36/0.59           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.36/0.59             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.36/0.59  thf('10', plain,
% 0.36/0.59      (![X71 : $i, X72 : $i, X73 : $i]:
% 0.36/0.59         (~ (zip_tseitin_0 @ X71 @ X72)
% 0.36/0.59          | (zip_tseitin_1 @ X73 @ X71 @ X72)
% 0.36/0.59          | ~ (m1_subset_1 @ X73 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X72 @ X71))))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.36/0.59  thf('11', plain,
% 0.36/0.59      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.36/0.59        | ~ (zip_tseitin_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['9', '10'])).
% 0.36/0.59  thf('12', plain,
% 0.36/0.59      ((((sk_B_1) = (k1_xboole_0))
% 0.36/0.59        | (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['8', '11'])).
% 0.36/0.59  thf('13', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('14', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.36/0.59      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.36/0.59  thf('15', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_C_1 @ 
% 0.36/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf(redefinition_k1_relset_1, axiom,
% 0.36/0.59    (![A:$i,B:$i,C:$i]:
% 0.36/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.59       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.36/0.59  thf('16', plain,
% 0.36/0.59      (![X57 : $i, X58 : $i, X59 : $i]:
% 0.36/0.59         (((k1_relset_1 @ X58 @ X59 @ X57) = (k1_relat_1 @ X57))
% 0.36/0.59          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X59))))),
% 0.36/0.59      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.36/0.59  thf('17', plain,
% 0.36/0.59      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C_1)
% 0.36/0.59         = (k1_relat_1 @ sk_C_1))),
% 0.36/0.59      inference('sup-', [status(thm)], ['15', '16'])).
% 0.36/0.59  thf('18', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.36/0.59      inference('demod', [status(thm)], ['7', '14', '17'])).
% 0.36/0.59  thf(l33_zfmisc_1, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.36/0.59       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.36/0.59  thf('19', plain,
% 0.36/0.59      (![X45 : $i, X46 : $i]:
% 0.36/0.59         (~ (r2_hidden @ X45 @ X46)
% 0.36/0.59          | ((k4_xboole_0 @ (k1_tarski @ X45) @ X46) != (k1_tarski @ X45)))),
% 0.36/0.59      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.36/0.59  thf('20', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         (((k4_xboole_0 @ (k1_relat_1 @ sk_C_1) @ X0) != (k1_tarski @ sk_A))
% 0.36/0.59          | ~ (r2_hidden @ sk_A @ X0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['18', '19'])).
% 0.36/0.59  thf('21', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.36/0.59      inference('demod', [status(thm)], ['7', '14', '17'])).
% 0.36/0.59  thf('22', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         (((k4_xboole_0 @ (k1_relat_1 @ sk_C_1) @ X0) != (k1_relat_1 @ sk_C_1))
% 0.36/0.59          | ~ (r2_hidden @ sk_A @ X0))),
% 0.36/0.59      inference('demod', [status(thm)], ['20', '21'])).
% 0.36/0.59  thf(t7_xboole_0, axiom,
% 0.36/0.59    (![A:$i]:
% 0.36/0.59     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.36/0.59          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.36/0.59  thf('23', plain,
% 0.36/0.59      (![X2 : $i]: (((X2) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.36/0.59      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.36/0.59  thf('24', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_C_1 @ 
% 0.36/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf(l3_subset_1, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.59       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.36/0.59  thf('25', plain,
% 0.36/0.59      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.36/0.59         (~ (r2_hidden @ X48 @ X49)
% 0.36/0.59          | (r2_hidden @ X48 @ X50)
% 0.36/0.59          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X50)))),
% 0.36/0.59      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.36/0.59  thf('26', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1))
% 0.36/0.59          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.36/0.59      inference('sup-', [status(thm)], ['24', '25'])).
% 0.36/0.59  thf('27', plain,
% 0.36/0.59      ((((sk_C_1) = (k1_xboole_0))
% 0.36/0.59        | (r2_hidden @ (sk_B @ sk_C_1) @ 
% 0.36/0.59           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['23', '26'])).
% 0.36/0.59  thf(t12_mcart_1, axiom,
% 0.36/0.59    (![A:$i,B:$i,C:$i]:
% 0.36/0.59     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) =>
% 0.36/0.59       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.36/0.59         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.36/0.59  thf('28', plain,
% 0.36/0.59      (![X63 : $i, X64 : $i, X65 : $i]:
% 0.36/0.59         (((k1_mcart_1 @ X64) = (X63))
% 0.36/0.59          | ~ (r2_hidden @ X64 @ (k2_zfmisc_1 @ (k1_tarski @ X63) @ X65)))),
% 0.36/0.59      inference('cnf', [status(esa)], [t12_mcart_1])).
% 0.36/0.59  thf('29', plain,
% 0.36/0.59      ((((sk_C_1) = (k1_xboole_0)) | ((k1_mcart_1 @ (sk_B @ sk_C_1)) = (sk_A)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['27', '28'])).
% 0.36/0.59  thf('30', plain,
% 0.36/0.59      ((((sk_C_1) = (k1_xboole_0))
% 0.36/0.59        | (r2_hidden @ (sk_B @ sk_C_1) @ 
% 0.36/0.59           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['23', '26'])).
% 0.36/0.59  thf(t10_mcart_1, axiom,
% 0.36/0.59    (![A:$i,B:$i,C:$i]:
% 0.36/0.59     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.36/0.59       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.36/0.59         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.36/0.59  thf('31', plain,
% 0.36/0.59      (![X60 : $i, X61 : $i, X62 : $i]:
% 0.36/0.59         ((r2_hidden @ (k1_mcart_1 @ X60) @ X61)
% 0.36/0.59          | ~ (r2_hidden @ X60 @ (k2_zfmisc_1 @ X61 @ X62)))),
% 0.36/0.59      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.36/0.59  thf('32', plain,
% 0.36/0.59      ((((sk_C_1) = (k1_xboole_0))
% 0.36/0.59        | (r2_hidden @ (k1_mcart_1 @ (sk_B @ sk_C_1)) @ (k1_tarski @ sk_A)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['30', '31'])).
% 0.36/0.59  thf('33', plain,
% 0.36/0.59      (((r2_hidden @ sk_A @ (k1_tarski @ sk_A))
% 0.36/0.59        | ((sk_C_1) = (k1_xboole_0))
% 0.36/0.59        | ((sk_C_1) = (k1_xboole_0)))),
% 0.36/0.59      inference('sup+', [status(thm)], ['29', '32'])).
% 0.36/0.59  thf('34', plain,
% 0.36/0.59      ((((sk_C_1) = (k1_xboole_0)) | (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))),
% 0.36/0.59      inference('simplify', [status(thm)], ['33'])).
% 0.36/0.59  thf('35', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.36/0.59      inference('demod', [status(thm)], ['7', '14', '17'])).
% 0.36/0.59  thf('36', plain,
% 0.36/0.59      ((((sk_C_1) = (k1_xboole_0)) | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1)))),
% 0.36/0.59      inference('demod', [status(thm)], ['34', '35'])).
% 0.36/0.59  thf('37', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_C_1 @ 
% 0.36/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('38', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.36/0.59      inference('demod', [status(thm)], ['7', '14', '17'])).
% 0.36/0.59  thf('39', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_C_1 @ 
% 0.36/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ sk_B_1)))),
% 0.36/0.59      inference('demod', [status(thm)], ['37', '38'])).
% 0.36/0.59  thf(t7_funct_2, axiom,
% 0.36/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.59     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.36/0.59         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.59       ( ( r2_hidden @ C @ A ) =>
% 0.36/0.59         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.36/0.59           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.36/0.59  thf('40', plain,
% 0.36/0.59      (![X74 : $i, X75 : $i, X76 : $i, X77 : $i]:
% 0.36/0.59         (~ (r2_hidden @ X74 @ X75)
% 0.36/0.59          | ((X76) = (k1_xboole_0))
% 0.36/0.59          | ~ (v1_funct_1 @ X77)
% 0.36/0.59          | ~ (v1_funct_2 @ X77 @ X75 @ X76)
% 0.36/0.59          | ~ (m1_subset_1 @ X77 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X75 @ X76)))
% 0.36/0.59          | (r2_hidden @ (k1_funct_1 @ X77 @ X74) @ X76))),
% 0.36/0.59      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.36/0.59  thf('41', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ sk_B_1)
% 0.36/0.59          | ~ (v1_funct_2 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ sk_B_1)
% 0.36/0.59          | ~ (v1_funct_1 @ sk_C_1)
% 0.36/0.59          | ((sk_B_1) = (k1_xboole_0))
% 0.36/0.59          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['39', '40'])).
% 0.36/0.59  thf('42', plain, ((v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('43', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.36/0.59      inference('demod', [status(thm)], ['7', '14', '17'])).
% 0.36/0.59  thf('44', plain, ((v1_funct_2 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ sk_B_1)),
% 0.36/0.59      inference('demod', [status(thm)], ['42', '43'])).
% 0.36/0.59  thf('45', plain, ((v1_funct_1 @ sk_C_1)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('46', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ sk_B_1)
% 0.36/0.59          | ((sk_B_1) = (k1_xboole_0))
% 0.36/0.59          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1)))),
% 0.36/0.59      inference('demod', [status(thm)], ['41', '44', '45'])).
% 0.36/0.59  thf('47', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('48', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ sk_B_1)
% 0.36/0.59          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1)))),
% 0.36/0.59      inference('simplify_reflect-', [status(thm)], ['46', '47'])).
% 0.36/0.59  thf('49', plain,
% 0.36/0.59      ((((sk_C_1) = (k1_xboole_0))
% 0.36/0.59        | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B_1))),
% 0.36/0.59      inference('sup-', [status(thm)], ['36', '48'])).
% 0.36/0.59  thf('50', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B_1)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('51', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.36/0.59      inference('clc', [status(thm)], ['49', '50'])).
% 0.36/0.59  thf(t60_relat_1, axiom,
% 0.36/0.59    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.36/0.59     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.36/0.59  thf('52', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.59      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.36/0.59  thf(commutativity_k2_tarski, axiom,
% 0.36/0.59    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.36/0.59  thf('53', plain,
% 0.36/0.59      (![X10 : $i, X11 : $i]:
% 0.36/0.59         ((k2_tarski @ X11 @ X10) = (k2_tarski @ X10 @ X11))),
% 0.36/0.59      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.36/0.59  thf(t12_setfam_1, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.36/0.59  thf('54', plain,
% 0.36/0.59      (![X52 : $i, X53 : $i]:
% 0.36/0.59         ((k1_setfam_1 @ (k2_tarski @ X52 @ X53)) = (k3_xboole_0 @ X52 @ X53))),
% 0.36/0.59      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.36/0.59  thf('55', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.59      inference('sup+', [status(thm)], ['53', '54'])).
% 0.36/0.59  thf('56', plain,
% 0.36/0.59      (![X52 : $i, X53 : $i]:
% 0.36/0.59         ((k1_setfam_1 @ (k2_tarski @ X52 @ X53)) = (k3_xboole_0 @ X52 @ X53))),
% 0.36/0.59      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.36/0.59  thf('57', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.59      inference('sup+', [status(thm)], ['55', '56'])).
% 0.36/0.59  thf(t2_boole, axiom,
% 0.36/0.59    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.36/0.59  thf('58', plain,
% 0.36/0.59      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.59      inference('cnf', [status(esa)], [t2_boole])).
% 0.36/0.59  thf('59', plain,
% 0.36/0.59      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['57', '58'])).
% 0.36/0.59  thf(t100_xboole_1, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.36/0.59  thf('60', plain,
% 0.36/0.59      (![X6 : $i, X7 : $i]:
% 0.36/0.59         ((k4_xboole_0 @ X6 @ X7)
% 0.36/0.59           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.36/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.59  thf(commutativity_k5_xboole_0, axiom,
% 0.36/0.59    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.36/0.59  thf('61', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.36/0.59      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.36/0.59  thf(t5_boole, axiom,
% 0.36/0.59    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.36/0.59  thf('62', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.36/0.59      inference('cnf', [status(esa)], [t5_boole])).
% 0.36/0.59  thf('63', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['61', '62'])).
% 0.36/0.59  thf('64', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['60', '63'])).
% 0.36/0.59  thf('65', plain,
% 0.36/0.59      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['59', '64'])).
% 0.36/0.59  thf('66', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.36/0.59      inference('clc', [status(thm)], ['49', '50'])).
% 0.36/0.59  thf('67', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.59      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.36/0.59  thf('68', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         (((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ sk_A @ X0))),
% 0.36/0.59      inference('demod', [status(thm)], ['22', '51', '52', '65', '66', '67'])).
% 0.36/0.59  thf('69', plain, (![X0 : $i]: ~ (r2_hidden @ sk_A @ X0)),
% 0.36/0.59      inference('simplify', [status(thm)], ['68'])).
% 0.36/0.59  thf('70', plain, ($false), inference('sup-', [status(thm)], ['4', '69'])).
% 0.36/0.59  
% 0.36/0.59  % SZS output end Refutation
% 0.36/0.59  
% 0.36/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
