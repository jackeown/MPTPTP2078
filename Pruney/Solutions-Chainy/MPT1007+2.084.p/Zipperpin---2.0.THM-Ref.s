%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NJFYBorbpZ

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 198 expanded)
%              Number of leaves         :   41 (  77 expanded)
%              Depth                    :   15
%              Number of atoms          :  679 (2227 expanded)
%              Number of equality atoms :   60 ( 149 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('2',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( r1_tarski @ X39 @ X40 )
      | ( r2_hidden @ X39 @ X41 )
      | ( X41
       != ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('3',plain,(
    ! [X39: $i,X40: $i] :
      ( ( r2_hidden @ X39 @ ( k1_zfmisc_1 @ X40 ) )
      | ~ ( r1_tarski @ X39 @ X40 ) ) ),
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
    ! [X65: $i,X66: $i,X67: $i] :
      ( ~ ( v1_funct_2 @ X67 @ X65 @ X66 )
      | ( X65
        = ( k1_relset_1 @ X65 @ X66 @ X67 ) )
      | ~ ( zip_tseitin_1 @ X67 @ X66 @ X65 ) ) ),
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
    ! [X63: $i,X64: $i] :
      ( ( zip_tseitin_0 @ X63 @ X64 )
      | ( X63 = k1_xboole_0 ) ) ),
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
    ! [X68: $i,X69: $i,X70: $i] :
      ( ~ ( zip_tseitin_0 @ X68 @ X69 )
      | ( zip_tseitin_1 @ X70 @ X68 @ X69 )
      | ~ ( m1_subset_1 @ X70 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X69 @ X68 ) ) ) ) ),
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
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( ( k1_relset_1 @ X51 @ X52 @ X50 )
        = ( k1_relat_1 @ X50 ) )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('17',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['7','14','17'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('19',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( r2_hidden @ X44 @ X45 )
      | ( ( k4_xboole_0 @ X45 @ ( k1_tarski @ X44 ) )
       != X45 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_relat_1 @ sk_C_1 ) )
       != X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t29_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) )).

thf('21',plain,(
    ! [X59: $i] :
      ( ( X59 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X59 ) @ X59 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('22',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('23',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( r2_hidden @ X47 @ X48 )
      | ( r2_hidden @ X47 @ X49 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf(t12_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('26',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ( ( k1_mcart_1 @ X57 )
        = X56 )
      | ~ ( r2_hidden @ X57 @ ( k2_zfmisc_1 @ ( k1_tarski @ X56 ) @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[t12_mcart_1])).

thf('27',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k1_mcart_1 @ ( sk_B @ sk_C_1 ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('29',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X53 ) @ X54 )
      | ~ ( r2_hidden @ X53 @ ( k2_zfmisc_1 @ X54 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('30',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k1_mcart_1 @ ( sk_B @ sk_C_1 ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['7','14','17'])).

thf('34',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['7','14','17'])).

thf('37',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('38',plain,(
    ! [X71: $i,X72: $i,X73: $i,X74: $i] :
      ( ~ ( r2_hidden @ X71 @ X72 )
      | ( X73 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X74 )
      | ~ ( v1_funct_2 @ X74 @ X72 @ X73 )
      | ~ ( m1_subset_1 @ X74 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X72 @ X73 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X74 @ X71 ) @ X73 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ sk_B_1 )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_2 @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['7','14','17'])).

thf('42',plain,(
    v1_funct_2 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['39','42','43'])).

thf('45',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['34','46'])).

thf('48',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['47','48'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('50',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('51',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( X0 != X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['20','49','50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_A @ X0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    $false ),
    inference('sup-',[status(thm)],['4','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NJFYBorbpZ
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:15:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.58  % Solved by: fo/fo7.sh
% 0.22/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.58  % done 231 iterations in 0.114s
% 0.22/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.58  % SZS output start Refutation
% 0.22/0.58  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.22/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.58  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.22/0.58  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.22/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.58  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.22/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.58  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.58  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.58  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.58  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.22/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.58  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.22/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.58  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.58  thf(d10_xboole_0, axiom,
% 0.22/0.58    (![A:$i,B:$i]:
% 0.22/0.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.58  thf('0', plain,
% 0.22/0.58      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.22/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.58  thf('1', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.22/0.58      inference('simplify', [status(thm)], ['0'])).
% 0.22/0.58  thf(d1_zfmisc_1, axiom,
% 0.22/0.58    (![A:$i,B:$i]:
% 0.22/0.58     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.22/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.22/0.58  thf('2', plain,
% 0.22/0.58      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.22/0.58         (~ (r1_tarski @ X39 @ X40)
% 0.22/0.58          | (r2_hidden @ X39 @ X41)
% 0.22/0.58          | ((X41) != (k1_zfmisc_1 @ X40)))),
% 0.22/0.58      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.22/0.58  thf('3', plain,
% 0.22/0.58      (![X39 : $i, X40 : $i]:
% 0.22/0.58         ((r2_hidden @ X39 @ (k1_zfmisc_1 @ X40)) | ~ (r1_tarski @ X39 @ X40))),
% 0.22/0.58      inference('simplify', [status(thm)], ['2'])).
% 0.22/0.58  thf('4', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.58      inference('sup-', [status(thm)], ['1', '3'])).
% 0.22/0.58  thf(t61_funct_2, conjecture,
% 0.22/0.58    (![A:$i,B:$i,C:$i]:
% 0.22/0.58     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.22/0.58         ( m1_subset_1 @
% 0.22/0.58           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.22/0.58       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.22/0.58         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.22/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.58    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.58        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.22/0.58            ( m1_subset_1 @
% 0.22/0.58              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.22/0.58          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.22/0.58            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.22/0.58    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.22/0.58  thf('5', plain, ((v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf(d1_funct_2, axiom,
% 0.22/0.58    (![A:$i,B:$i,C:$i]:
% 0.22/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.58       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.22/0.58           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.22/0.58             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.22/0.58         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.22/0.58           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.22/0.58             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.22/0.58  thf(zf_stmt_1, axiom,
% 0.22/0.58    (![C:$i,B:$i,A:$i]:
% 0.22/0.58     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.22/0.58       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.22/0.58  thf('6', plain,
% 0.22/0.58      (![X65 : $i, X66 : $i, X67 : $i]:
% 0.22/0.58         (~ (v1_funct_2 @ X67 @ X65 @ X66)
% 0.22/0.58          | ((X65) = (k1_relset_1 @ X65 @ X66 @ X67))
% 0.22/0.58          | ~ (zip_tseitin_1 @ X67 @ X66 @ X65))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.58  thf('7', plain,
% 0.22/0.58      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.22/0.58        | ((k1_tarski @ sk_A)
% 0.22/0.58            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C_1)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.58  thf(zf_stmt_2, axiom,
% 0.22/0.58    (![B:$i,A:$i]:
% 0.22/0.58     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.22/0.58       ( zip_tseitin_0 @ B @ A ) ))).
% 0.22/0.58  thf('8', plain,
% 0.22/0.58      (![X63 : $i, X64 : $i]:
% 0.22/0.58         ((zip_tseitin_0 @ X63 @ X64) | ((X63) = (k1_xboole_0)))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.22/0.58  thf('9', plain,
% 0.22/0.58      ((m1_subset_1 @ sk_C_1 @ 
% 0.22/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.22/0.58  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.22/0.58  thf(zf_stmt_5, axiom,
% 0.22/0.58    (![A:$i,B:$i,C:$i]:
% 0.22/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.58       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.22/0.58         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.22/0.58           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.22/0.58             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.22/0.58  thf('10', plain,
% 0.22/0.58      (![X68 : $i, X69 : $i, X70 : $i]:
% 0.22/0.58         (~ (zip_tseitin_0 @ X68 @ X69)
% 0.22/0.58          | (zip_tseitin_1 @ X70 @ X68 @ X69)
% 0.22/0.58          | ~ (m1_subset_1 @ X70 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X69 @ X68))))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.58  thf('11', plain,
% 0.22/0.58      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.22/0.58        | ~ (zip_tseitin_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.58  thf('12', plain,
% 0.22/0.58      ((((sk_B_1) = (k1_xboole_0))
% 0.22/0.58        | (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['8', '11'])).
% 0.22/0.58  thf('13', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('14', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.22/0.58      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.22/0.58  thf('15', plain,
% 0.22/0.58      ((m1_subset_1 @ sk_C_1 @ 
% 0.22/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf(redefinition_k1_relset_1, axiom,
% 0.22/0.58    (![A:$i,B:$i,C:$i]:
% 0.22/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.58       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.22/0.58  thf('16', plain,
% 0.22/0.58      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.22/0.58         (((k1_relset_1 @ X51 @ X52 @ X50) = (k1_relat_1 @ X50))
% 0.22/0.58          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52))))),
% 0.22/0.58      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.22/0.58  thf('17', plain,
% 0.22/0.58      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C_1)
% 0.22/0.58         = (k1_relat_1 @ sk_C_1))),
% 0.22/0.58      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.58  thf('18', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.22/0.58      inference('demod', [status(thm)], ['7', '14', '17'])).
% 0.22/0.58  thf(t65_zfmisc_1, axiom,
% 0.22/0.58    (![A:$i,B:$i]:
% 0.22/0.58     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.22/0.58       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.22/0.58  thf('19', plain,
% 0.22/0.58      (![X44 : $i, X45 : $i]:
% 0.22/0.58         (~ (r2_hidden @ X44 @ X45)
% 0.22/0.58          | ((k4_xboole_0 @ X45 @ (k1_tarski @ X44)) != (X45)))),
% 0.22/0.58      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.22/0.58  thf('20', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         (((k4_xboole_0 @ X0 @ (k1_relat_1 @ sk_C_1)) != (X0))
% 0.22/0.58          | ~ (r2_hidden @ sk_A @ X0))),
% 0.22/0.58      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.58  thf(t29_mcart_1, axiom,
% 0.22/0.58    (![A:$i]:
% 0.22/0.58     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.58          ( ![B:$i]:
% 0.22/0.58            ( ~( ( r2_hidden @ B @ A ) & 
% 0.22/0.58                 ( ![C:$i,D:$i,E:$i]:
% 0.22/0.58                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.22/0.58                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.58  thf('21', plain,
% 0.22/0.58      (![X59 : $i]:
% 0.22/0.58         (((X59) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X59) @ X59))),
% 0.22/0.58      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.22/0.58  thf('22', plain,
% 0.22/0.58      ((m1_subset_1 @ sk_C_1 @ 
% 0.22/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf(l3_subset_1, axiom,
% 0.22/0.58    (![A:$i,B:$i]:
% 0.22/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.22/0.58  thf('23', plain,
% 0.22/0.58      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.22/0.58         (~ (r2_hidden @ X47 @ X48)
% 0.22/0.58          | (r2_hidden @ X47 @ X49)
% 0.22/0.58          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X49)))),
% 0.22/0.58      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.22/0.58  thf('24', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1))
% 0.22/0.58          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.22/0.58      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.58  thf('25', plain,
% 0.22/0.58      ((((sk_C_1) = (k1_xboole_0))
% 0.22/0.58        | (r2_hidden @ (sk_B @ sk_C_1) @ 
% 0.22/0.58           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['21', '24'])).
% 0.22/0.58  thf(t12_mcart_1, axiom,
% 0.22/0.58    (![A:$i,B:$i,C:$i]:
% 0.22/0.58     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) =>
% 0.22/0.58       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.22/0.58         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.22/0.58  thf('26', plain,
% 0.22/0.58      (![X56 : $i, X57 : $i, X58 : $i]:
% 0.22/0.58         (((k1_mcart_1 @ X57) = (X56))
% 0.22/0.58          | ~ (r2_hidden @ X57 @ (k2_zfmisc_1 @ (k1_tarski @ X56) @ X58)))),
% 0.22/0.58      inference('cnf', [status(esa)], [t12_mcart_1])).
% 0.22/0.58  thf('27', plain,
% 0.22/0.58      ((((sk_C_1) = (k1_xboole_0)) | ((k1_mcart_1 @ (sk_B @ sk_C_1)) = (sk_A)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.58  thf('28', plain,
% 0.22/0.58      ((((sk_C_1) = (k1_xboole_0))
% 0.22/0.58        | (r2_hidden @ (sk_B @ sk_C_1) @ 
% 0.22/0.58           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['21', '24'])).
% 0.22/0.58  thf(t10_mcart_1, axiom,
% 0.22/0.58    (![A:$i,B:$i,C:$i]:
% 0.22/0.58     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.22/0.58       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.22/0.58         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.22/0.58  thf('29', plain,
% 0.22/0.58      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.22/0.58         ((r2_hidden @ (k1_mcart_1 @ X53) @ X54)
% 0.22/0.58          | ~ (r2_hidden @ X53 @ (k2_zfmisc_1 @ X54 @ X55)))),
% 0.22/0.58      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.22/0.58  thf('30', plain,
% 0.22/0.58      ((((sk_C_1) = (k1_xboole_0))
% 0.22/0.58        | (r2_hidden @ (k1_mcart_1 @ (sk_B @ sk_C_1)) @ (k1_tarski @ sk_A)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.58  thf('31', plain,
% 0.22/0.58      (((r2_hidden @ sk_A @ (k1_tarski @ sk_A))
% 0.22/0.58        | ((sk_C_1) = (k1_xboole_0))
% 0.22/0.58        | ((sk_C_1) = (k1_xboole_0)))),
% 0.22/0.58      inference('sup+', [status(thm)], ['27', '30'])).
% 0.22/0.58  thf('32', plain,
% 0.22/0.58      ((((sk_C_1) = (k1_xboole_0)) | (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))),
% 0.22/0.58      inference('simplify', [status(thm)], ['31'])).
% 0.22/0.58  thf('33', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.22/0.58      inference('demod', [status(thm)], ['7', '14', '17'])).
% 0.22/0.58  thf('34', plain,
% 0.22/0.58      ((((sk_C_1) = (k1_xboole_0)) | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1)))),
% 0.22/0.58      inference('demod', [status(thm)], ['32', '33'])).
% 0.22/0.58  thf('35', plain,
% 0.22/0.58      ((m1_subset_1 @ sk_C_1 @ 
% 0.22/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('36', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.22/0.58      inference('demod', [status(thm)], ['7', '14', '17'])).
% 0.22/0.58  thf('37', plain,
% 0.22/0.58      ((m1_subset_1 @ sk_C_1 @ 
% 0.22/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ sk_B_1)))),
% 0.22/0.58      inference('demod', [status(thm)], ['35', '36'])).
% 0.22/0.58  thf(t7_funct_2, axiom,
% 0.22/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.58     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.22/0.58         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.58       ( ( r2_hidden @ C @ A ) =>
% 0.22/0.58         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.22/0.58           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.22/0.58  thf('38', plain,
% 0.22/0.58      (![X71 : $i, X72 : $i, X73 : $i, X74 : $i]:
% 0.22/0.58         (~ (r2_hidden @ X71 @ X72)
% 0.22/0.58          | ((X73) = (k1_xboole_0))
% 0.22/0.58          | ~ (v1_funct_1 @ X74)
% 0.22/0.58          | ~ (v1_funct_2 @ X74 @ X72 @ X73)
% 0.22/0.58          | ~ (m1_subset_1 @ X74 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X72 @ X73)))
% 0.22/0.58          | (r2_hidden @ (k1_funct_1 @ X74 @ X71) @ X73))),
% 0.22/0.58      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.22/0.58  thf('39', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ sk_B_1)
% 0.22/0.58          | ~ (v1_funct_2 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ sk_B_1)
% 0.22/0.58          | ~ (v1_funct_1 @ sk_C_1)
% 0.22/0.58          | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.58          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.58  thf('40', plain, ((v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('41', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.22/0.58      inference('demod', [status(thm)], ['7', '14', '17'])).
% 0.22/0.58  thf('42', plain, ((v1_funct_2 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ sk_B_1)),
% 0.22/0.58      inference('demod', [status(thm)], ['40', '41'])).
% 0.22/0.58  thf('43', plain, ((v1_funct_1 @ sk_C_1)),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('44', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ sk_B_1)
% 0.22/0.58          | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.58          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1)))),
% 0.22/0.58      inference('demod', [status(thm)], ['39', '42', '43'])).
% 0.22/0.58  thf('45', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('46', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ sk_B_1)
% 0.22/0.58          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1)))),
% 0.22/0.58      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 0.22/0.58  thf('47', plain,
% 0.22/0.58      ((((sk_C_1) = (k1_xboole_0))
% 0.22/0.58        | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B_1))),
% 0.22/0.58      inference('sup-', [status(thm)], ['34', '46'])).
% 0.22/0.58  thf('48', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B_1)),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('49', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.22/0.58      inference('clc', [status(thm)], ['47', '48'])).
% 0.22/0.58  thf(t60_relat_1, axiom,
% 0.22/0.58    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.22/0.58     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.58  thf('50', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.58      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.58  thf(t3_boole, axiom,
% 0.22/0.58    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.58  thf('51', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.22/0.58      inference('cnf', [status(esa)], [t3_boole])).
% 0.22/0.58  thf('52', plain, (![X0 : $i]: (((X0) != (X0)) | ~ (r2_hidden @ sk_A @ X0))),
% 0.22/0.58      inference('demod', [status(thm)], ['20', '49', '50', '51'])).
% 0.22/0.58  thf('53', plain, (![X0 : $i]: ~ (r2_hidden @ sk_A @ X0)),
% 0.22/0.58      inference('simplify', [status(thm)], ['52'])).
% 0.22/0.58  thf('54', plain, ($false), inference('sup-', [status(thm)], ['4', '53'])).
% 0.22/0.58  
% 0.22/0.58  % SZS output end Refutation
% 0.22/0.58  
% 0.22/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
