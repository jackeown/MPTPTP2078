%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vy7hmzbYwJ

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:18 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 425 expanded)
%              Number of leaves         :   64 ( 157 expanded)
%              Depth                    :   21
%              Number of atoms          : 1010 (4080 expanded)
%              Number of equality atoms :   79 ( 228 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X48: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X51: $i,X52: $i] :
      ( ( r2_hidden @ X51 @ X52 )
      | ( v1_xboole_0 @ X52 )
      | ~ ( m1_subset_1 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X44: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['2','3'])).

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
    ! [X82: $i,X83: $i,X84: $i] :
      ( ~ ( v1_funct_2 @ X84 @ X82 @ X83 )
      | ( X82
        = ( k1_relset_1 @ X82 @ X83 @ X84 ) )
      | ~ ( zip_tseitin_1 @ X84 @ X83 @ X82 ) ) ),
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
    ! [X80: $i,X81: $i] :
      ( ( zip_tseitin_0 @ X80 @ X81 )
      | ( X80 = k1_xboole_0 ) ) ),
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
    ! [X85: $i,X86: $i,X87: $i] :
      ( ~ ( zip_tseitin_0 @ X85 @ X86 )
      | ( zip_tseitin_1 @ X87 @ X85 @ X86 )
      | ~ ( m1_subset_1 @ X87 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X86 @ X85 ) ) ) ) ),
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
    ! [X66: $i,X67: $i,X68: $i] :
      ( ( ( k1_relset_1 @ X67 @ X68 @ X66 )
        = ( k1_relat_1 @ X66 ) )
      | ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X67 @ X68 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('17',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['7','14','17'])).

thf(t6_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i,G: $i] :
                  ( ( ( r2_hidden @ C @ D )
                    & ( r2_hidden @ D @ E )
                    & ( r2_hidden @ E @ F )
                    & ( r2_hidden @ F @ G )
                    & ( r2_hidden @ G @ B ) )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('19',plain,(
    ! [X72: $i] :
      ( ( X72 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X72 ) @ X72 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('22',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( r2_hidden @ X45 @ X46 )
      | ( r2_hidden @ X45 @ X47 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf(t12_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('25',plain,(
    ! [X69: $i,X70: $i,X71: $i] :
      ( ( ( k1_mcart_1 @ X70 )
        = X69 )
      | ~ ( r2_hidden @ X70 @ ( k2_zfmisc_1 @ ( k1_tarski @ X69 ) @ X71 ) ) ) ),
    inference(cnf,[status(esa)],[t12_mcart_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( ( k1_mcart_1 @ ( sk_C @ X0 @ sk_C_1 ) )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t91_mcart_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( ( r2_hidden @ ( k1_mcart_1 @ B ) @ ( k1_relat_1 @ A ) )
            & ( r2_hidden @ ( k2_mcart_1 @ B ) @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('28',plain,(
    ! [X78: $i,X79: $i] :
      ( ~ ( r2_hidden @ X78 @ X79 )
      | ( r2_hidden @ ( k1_mcart_1 @ X78 ) @ ( k1_relat_1 @ X79 ) )
      | ~ ( v1_relat_1 @ X79 ) ) ),
    inference(cnf,[status(esa)],[t91_mcart_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( sk_C @ X1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
      | ( r1_tarski @ sk_C_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('32',plain,(
    ! [X60: $i,X61: $i,X62: $i] :
      ( ( v1_relat_1 @ X60 )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X61 @ X62 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('33',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
      | ( r1_tarski @ sk_C_1 @ X0 )
      | ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('36',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( r2_hidden @ X58 @ ( k1_relat_1 @ X59 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X59 @ X58 ) @ ( k2_relat_1 @ X59 ) )
      | ~ ( v1_funct_1 @ X59 )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('39',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('42',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ( v5_relat_1 @ X63 @ X65 )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X64 @ X65 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('43',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['41','42'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('44',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( v5_relat_1 @ X56 @ X57 )
      | ( r1_tarski @ ( k2_relat_1 @ X56 ) @ X57 )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('47',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['40','49'])).

thf('51',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_C_1 @ X0 ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','54'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('56',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('57',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('59',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('61',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('62',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( r2_hidden @ X40 @ X41 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X40 ) @ X41 )
       != ( k1_tarski @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 )
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ X0 @ X0 )
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('66',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['64','65'])).

thf('67',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['55','66'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('68',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('69',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['18','67','68'])).

thf('70',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( r2_hidden @ X40 @ X41 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X40 ) @ X41 )
       != ( k1_tarski @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
       != ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('72',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X11 @ X10 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('73',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X49 @ X50 ) )
      = ( k3_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X49 @ X50 ) )
      = ( k3_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('81',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['79','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['78','83'])).

thf('85',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['18','67','68'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['71','84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_A @ X0 ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['7','14','17'])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('89',plain,(
    ! [X43: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('90',plain,
    ( ( k3_tarski @ ( k1_relat_1 @ sk_C_1 ) )
    = sk_A ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['55','66'])).

thf('92',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('93',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = sk_A ),
    inference(demod,[status(thm)],['90','91','92'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('94',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('95',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['87','95'])).

thf('97',plain,(
    $false ),
    inference('sup-',[status(thm)],['4','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vy7hmzbYwJ
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:16:24 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.76/0.97  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.76/0.97  % Solved by: fo/fo7.sh
% 0.76/0.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.97  % done 734 iterations in 0.511s
% 0.76/0.97  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.76/0.97  % SZS output start Refutation
% 0.76/0.97  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.97  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.97  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.76/0.97  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.76/0.97  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.76/0.97  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.76/0.97  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.76/0.97  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.76/0.97  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.76/0.97  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.76/0.97  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.76/0.97  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.76/0.97  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.76/0.97  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.76/0.97  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.76/0.97  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.76/0.97  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.97  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.76/0.97  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.76/0.97  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.76/0.97  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.76/0.97  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.76/0.97  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.76/0.97  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.76/0.97  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.76/0.97  thf(sk_B_type, type, sk_B: $i > $i).
% 0.76/0.97  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.76/0.97  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.76/0.97  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.97  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.76/0.97  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.76/0.97  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.76/0.97  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.76/0.97  thf(t4_subset_1, axiom,
% 0.76/0.97    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.76/0.97  thf('0', plain,
% 0.76/0.97      (![X48 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X48))),
% 0.76/0.97      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.76/0.97  thf(t2_subset, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ A @ B ) =>
% 0.76/0.97       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.76/0.97  thf('1', plain,
% 0.76/0.97      (![X51 : $i, X52 : $i]:
% 0.76/0.97         ((r2_hidden @ X51 @ X52)
% 0.76/0.97          | (v1_xboole_0 @ X52)
% 0.76/0.97          | ~ (m1_subset_1 @ X51 @ X52))),
% 0.76/0.97      inference('cnf', [status(esa)], [t2_subset])).
% 0.76/0.97  thf('2', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.76/0.97          | (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['0', '1'])).
% 0.76/0.97  thf(fc1_subset_1, axiom,
% 0.76/0.97    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.76/0.97  thf('3', plain, (![X44 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X44))),
% 0.76/0.97      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.76/0.97  thf('4', plain, (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.76/0.97      inference('clc', [status(thm)], ['2', '3'])).
% 0.76/0.97  thf(t61_funct_2, conjecture,
% 0.76/0.97    (![A:$i,B:$i,C:$i]:
% 0.76/0.97     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.76/0.97         ( m1_subset_1 @
% 0.76/0.97           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.76/0.97       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.76/0.97         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.76/0.97  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.97    (~( ![A:$i,B:$i,C:$i]:
% 0.76/0.97        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.76/0.97            ( m1_subset_1 @
% 0.76/0.97              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.76/0.97          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.76/0.97            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.76/0.97    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.76/0.97  thf('5', plain, ((v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(d1_funct_2, axiom,
% 0.76/0.97    (![A:$i,B:$i,C:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.97       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.76/0.97           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.76/0.97             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.76/0.97         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.76/0.97           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.76/0.97             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.76/0.97  thf(zf_stmt_1, axiom,
% 0.76/0.97    (![C:$i,B:$i,A:$i]:
% 0.76/0.97     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.76/0.97       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.76/0.97  thf('6', plain,
% 0.76/0.97      (![X82 : $i, X83 : $i, X84 : $i]:
% 0.76/0.97         (~ (v1_funct_2 @ X84 @ X82 @ X83)
% 0.76/0.97          | ((X82) = (k1_relset_1 @ X82 @ X83 @ X84))
% 0.76/0.97          | ~ (zip_tseitin_1 @ X84 @ X83 @ X82))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.76/0.97  thf('7', plain,
% 0.76/0.97      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.76/0.97        | ((k1_tarski @ sk_A)
% 0.76/0.97            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C_1)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['5', '6'])).
% 0.76/0.97  thf(zf_stmt_2, axiom,
% 0.76/0.97    (![B:$i,A:$i]:
% 0.76/0.97     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.76/0.97       ( zip_tseitin_0 @ B @ A ) ))).
% 0.76/0.97  thf('8', plain,
% 0.76/0.97      (![X80 : $i, X81 : $i]:
% 0.76/0.97         ((zip_tseitin_0 @ X80 @ X81) | ((X80) = (k1_xboole_0)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.76/0.97  thf('9', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_C_1 @ 
% 0.76/0.97        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.76/0.97  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.76/0.97  thf(zf_stmt_5, axiom,
% 0.76/0.97    (![A:$i,B:$i,C:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.97       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.76/0.97         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.76/0.97           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.76/0.97             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.76/0.97  thf('10', plain,
% 0.76/0.97      (![X85 : $i, X86 : $i, X87 : $i]:
% 0.76/0.97         (~ (zip_tseitin_0 @ X85 @ X86)
% 0.76/0.97          | (zip_tseitin_1 @ X87 @ X85 @ X86)
% 0.76/0.97          | ~ (m1_subset_1 @ X87 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X86 @ X85))))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.76/0.97  thf('11', plain,
% 0.76/0.97      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.76/0.97        | ~ (zip_tseitin_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['9', '10'])).
% 0.76/0.97  thf('12', plain,
% 0.76/0.97      ((((sk_B_1) = (k1_xboole_0))
% 0.76/0.97        | (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['8', '11'])).
% 0.76/0.97  thf('13', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('14', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.76/0.97      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.76/0.97  thf('15', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_C_1 @ 
% 0.76/0.97        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(redefinition_k1_relset_1, axiom,
% 0.76/0.97    (![A:$i,B:$i,C:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.97       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.76/0.97  thf('16', plain,
% 0.76/0.97      (![X66 : $i, X67 : $i, X68 : $i]:
% 0.76/0.97         (((k1_relset_1 @ X67 @ X68 @ X66) = (k1_relat_1 @ X66))
% 0.76/0.97          | ~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X67 @ X68))))),
% 0.76/0.97      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.76/0.97  thf('17', plain,
% 0.76/0.97      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C_1)
% 0.76/0.97         = (k1_relat_1 @ sk_C_1))),
% 0.76/0.97      inference('sup-', [status(thm)], ['15', '16'])).
% 0.76/0.97  thf('18', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.76/0.97      inference('demod', [status(thm)], ['7', '14', '17'])).
% 0.76/0.97  thf(t6_mcart_1, axiom,
% 0.76/0.97    (![A:$i]:
% 0.76/0.97     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.76/0.97          ( ![B:$i]:
% 0.76/0.97            ( ~( ( r2_hidden @ B @ A ) & 
% 0.76/0.97                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.76/0.97                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.76/0.97                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.76/0.97                       ( r2_hidden @ G @ B ) ) =>
% 0.76/0.97                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.76/0.97  thf('19', plain,
% 0.76/0.97      (![X72 : $i]:
% 0.76/0.97         (((X72) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X72) @ X72))),
% 0.76/0.97      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.76/0.97  thf(d3_tarski, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( r1_tarski @ A @ B ) <=>
% 0.76/0.97       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.76/0.97  thf('20', plain,
% 0.76/0.97      (![X3 : $i, X5 : $i]:
% 0.76/0.97         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.76/0.97      inference('cnf', [status(esa)], [d3_tarski])).
% 0.76/0.97  thf('21', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_C_1 @ 
% 0.76/0.97        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(l3_subset_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.97       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.76/0.97  thf('22', plain,
% 0.76/0.97      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.76/0.97         (~ (r2_hidden @ X45 @ X46)
% 0.76/0.97          | (r2_hidden @ X45 @ X47)
% 0.76/0.97          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47)))),
% 0.76/0.97      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.76/0.97  thf('23', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1))
% 0.76/0.97          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.76/0.97      inference('sup-', [status(thm)], ['21', '22'])).
% 0.76/0.97  thf('24', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((r1_tarski @ sk_C_1 @ X0)
% 0.76/0.97          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ 
% 0.76/0.97             (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['20', '23'])).
% 0.76/0.97  thf(t12_mcart_1, axiom,
% 0.76/0.97    (![A:$i,B:$i,C:$i]:
% 0.76/0.97     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) =>
% 0.76/0.97       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.76/0.97         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.76/0.97  thf('25', plain,
% 0.76/0.97      (![X69 : $i, X70 : $i, X71 : $i]:
% 0.76/0.97         (((k1_mcart_1 @ X70) = (X69))
% 0.76/0.97          | ~ (r2_hidden @ X70 @ (k2_zfmisc_1 @ (k1_tarski @ X69) @ X71)))),
% 0.76/0.97      inference('cnf', [status(esa)], [t12_mcart_1])).
% 0.76/0.97  thf('26', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((r1_tarski @ sk_C_1 @ X0)
% 0.76/0.97          | ((k1_mcart_1 @ (sk_C @ X0 @ sk_C_1)) = (sk_A)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['24', '25'])).
% 0.76/0.97  thf('27', plain,
% 0.76/0.97      (![X3 : $i, X5 : $i]:
% 0.76/0.97         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.76/0.97      inference('cnf', [status(esa)], [d3_tarski])).
% 0.76/0.97  thf(t91_mcart_1, axiom,
% 0.76/0.97    (![A:$i]:
% 0.76/0.97     ( ( v1_relat_1 @ A ) =>
% 0.76/0.97       ( ![B:$i]:
% 0.76/0.97         ( ( r2_hidden @ B @ A ) =>
% 0.76/0.97           ( ( r2_hidden @ ( k1_mcart_1 @ B ) @ ( k1_relat_1 @ A ) ) & 
% 0.76/0.97             ( r2_hidden @ ( k2_mcart_1 @ B ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.76/0.97  thf('28', plain,
% 0.76/0.97      (![X78 : $i, X79 : $i]:
% 0.76/0.97         (~ (r2_hidden @ X78 @ X79)
% 0.76/0.97          | (r2_hidden @ (k1_mcart_1 @ X78) @ (k1_relat_1 @ X79))
% 0.76/0.97          | ~ (v1_relat_1 @ X79))),
% 0.76/0.97      inference('cnf', [status(esa)], [t91_mcart_1])).
% 0.76/0.97  thf('29', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         ((r1_tarski @ X0 @ X1)
% 0.76/0.97          | ~ (v1_relat_1 @ X0)
% 0.76/0.97          | (r2_hidden @ (k1_mcart_1 @ (sk_C @ X1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['27', '28'])).
% 0.76/0.97  thf('30', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))
% 0.76/0.97          | (r1_tarski @ sk_C_1 @ X0)
% 0.76/0.97          | ~ (v1_relat_1 @ sk_C_1)
% 0.76/0.97          | (r1_tarski @ sk_C_1 @ X0))),
% 0.76/0.97      inference('sup+', [status(thm)], ['26', '29'])).
% 0.76/0.97  thf('31', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_C_1 @ 
% 0.76/0.97        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(cc1_relset_1, axiom,
% 0.76/0.97    (![A:$i,B:$i,C:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.97       ( v1_relat_1 @ C ) ))).
% 0.76/0.97  thf('32', plain,
% 0.76/0.97      (![X60 : $i, X61 : $i, X62 : $i]:
% 0.76/0.97         ((v1_relat_1 @ X60)
% 0.76/0.97          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X61 @ X62))))),
% 0.76/0.97      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.76/0.97  thf('33', plain, ((v1_relat_1 @ sk_C_1)),
% 0.76/0.97      inference('sup-', [status(thm)], ['31', '32'])).
% 0.76/0.97  thf('34', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))
% 0.76/0.97          | (r1_tarski @ sk_C_1 @ X0)
% 0.76/0.97          | (r1_tarski @ sk_C_1 @ X0))),
% 0.76/0.97      inference('demod', [status(thm)], ['30', '33'])).
% 0.76/0.97  thf('35', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((r1_tarski @ sk_C_1 @ X0)
% 0.76/0.97          | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1)))),
% 0.76/0.97      inference('simplify', [status(thm)], ['34'])).
% 0.76/0.97  thf(t12_funct_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.76/0.97       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.76/0.97         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.76/0.97  thf('36', plain,
% 0.76/0.97      (![X58 : $i, X59 : $i]:
% 0.76/0.97         (~ (r2_hidden @ X58 @ (k1_relat_1 @ X59))
% 0.76/0.97          | (r2_hidden @ (k1_funct_1 @ X59 @ X58) @ (k2_relat_1 @ X59))
% 0.76/0.97          | ~ (v1_funct_1 @ X59)
% 0.76/0.97          | ~ (v1_relat_1 @ X59))),
% 0.76/0.97      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.76/0.97  thf('37', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((r1_tarski @ sk_C_1 @ X0)
% 0.76/0.97          | ~ (v1_relat_1 @ sk_C_1)
% 0.76/0.97          | ~ (v1_funct_1 @ sk_C_1)
% 0.76/0.97          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ (k2_relat_1 @ sk_C_1)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['35', '36'])).
% 0.76/0.97  thf('38', plain, ((v1_relat_1 @ sk_C_1)),
% 0.76/0.97      inference('sup-', [status(thm)], ['31', '32'])).
% 0.76/0.97  thf('39', plain, ((v1_funct_1 @ sk_C_1)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('40', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((r1_tarski @ sk_C_1 @ X0)
% 0.76/0.97          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ (k2_relat_1 @ sk_C_1)))),
% 0.76/0.97      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.76/0.97  thf('41', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_C_1 @ 
% 0.76/0.97        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(cc2_relset_1, axiom,
% 0.76/0.97    (![A:$i,B:$i,C:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.97       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.76/0.97  thf('42', plain,
% 0.76/0.97      (![X63 : $i, X64 : $i, X65 : $i]:
% 0.76/0.97         ((v5_relat_1 @ X63 @ X65)
% 0.76/0.97          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X64 @ X65))))),
% 0.76/0.97      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.76/0.97  thf('43', plain, ((v5_relat_1 @ sk_C_1 @ sk_B_1)),
% 0.76/0.97      inference('sup-', [status(thm)], ['41', '42'])).
% 0.76/0.97  thf(d19_relat_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( v1_relat_1 @ B ) =>
% 0.76/0.97       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.76/0.97  thf('44', plain,
% 0.76/0.97      (![X56 : $i, X57 : $i]:
% 0.76/0.97         (~ (v5_relat_1 @ X56 @ X57)
% 0.76/0.97          | (r1_tarski @ (k2_relat_1 @ X56) @ X57)
% 0.76/0.97          | ~ (v1_relat_1 @ X56))),
% 0.76/0.97      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.76/0.97  thf('45', plain,
% 0.76/0.97      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))),
% 0.76/0.97      inference('sup-', [status(thm)], ['43', '44'])).
% 0.76/0.97  thf('46', plain, ((v1_relat_1 @ sk_C_1)),
% 0.76/0.97      inference('sup-', [status(thm)], ['31', '32'])).
% 0.76/0.97  thf('47', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)),
% 0.76/0.97      inference('demod', [status(thm)], ['45', '46'])).
% 0.76/0.97  thf('48', plain,
% 0.76/0.97      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.76/0.97         (~ (r2_hidden @ X2 @ X3)
% 0.76/0.97          | (r2_hidden @ X2 @ X4)
% 0.76/0.97          | ~ (r1_tarski @ X3 @ X4))),
% 0.76/0.97      inference('cnf', [status(esa)], [d3_tarski])).
% 0.76/0.97  thf('49', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((r2_hidden @ X0 @ sk_B_1)
% 0.76/0.97          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['47', '48'])).
% 0.76/0.97  thf('50', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((r1_tarski @ sk_C_1 @ X0)
% 0.76/0.97          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B_1))),
% 0.76/0.97      inference('sup-', [status(thm)], ['40', '49'])).
% 0.76/0.97  thf('51', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B_1)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('52', plain, (![X0 : $i]: (r1_tarski @ sk_C_1 @ X0)),
% 0.76/0.97      inference('clc', [status(thm)], ['50', '51'])).
% 0.76/0.97  thf('53', plain,
% 0.76/0.97      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.76/0.97         (~ (r2_hidden @ X2 @ X3)
% 0.76/0.97          | (r2_hidden @ X2 @ X4)
% 0.76/0.97          | ~ (r1_tarski @ X3 @ X4))),
% 0.76/0.97      inference('cnf', [status(esa)], [d3_tarski])).
% 0.76/0.97  thf('54', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ sk_C_1))),
% 0.76/0.97      inference('sup-', [status(thm)], ['52', '53'])).
% 0.76/0.97  thf('55', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (((sk_C_1) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ sk_C_1) @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['19', '54'])).
% 0.76/0.97  thf(t2_boole, axiom,
% 0.76/0.97    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.76/0.97  thf('56', plain,
% 0.76/0.97      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.97      inference('cnf', [status(esa)], [t2_boole])).
% 0.76/0.97  thf(t100_xboole_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.76/0.97  thf('57', plain,
% 0.76/0.97      (![X6 : $i, X7 : $i]:
% 0.76/0.97         ((k4_xboole_0 @ X6 @ X7)
% 0.76/0.97           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.76/0.97      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.76/0.97  thf('58', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.76/0.97      inference('sup+', [status(thm)], ['56', '57'])).
% 0.76/0.97  thf(t5_boole, axiom,
% 0.76/0.97    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.76/0.97  thf('59', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.76/0.97      inference('cnf', [status(esa)], [t5_boole])).
% 0.76/0.97  thf('60', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.76/0.97      inference('sup+', [status(thm)], ['58', '59'])).
% 0.76/0.97  thf(t69_enumset1, axiom,
% 0.76/0.97    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.76/0.97  thf('61', plain,
% 0.76/0.97      (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.76/0.97      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.76/0.97  thf(l33_zfmisc_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.76/0.97       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.76/0.97  thf('62', plain,
% 0.76/0.97      (![X40 : $i, X41 : $i]:
% 0.76/0.97         (~ (r2_hidden @ X40 @ X41)
% 0.76/0.97          | ((k4_xboole_0 @ (k1_tarski @ X40) @ X41) != (k1_tarski @ X40)))),
% 0.76/0.97      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.76/0.97  thf('63', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (((k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1) != (k1_tarski @ X0))
% 0.76/0.97          | ~ (r2_hidden @ X0 @ X1))),
% 0.76/0.97      inference('sup-', [status(thm)], ['61', '62'])).
% 0.76/0.97  thf('64', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (((k2_tarski @ X0 @ X0) != (k1_tarski @ X0))
% 0.76/0.97          | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['60', '63'])).
% 0.76/0.97  thf('65', plain,
% 0.76/0.97      (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.76/0.97      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.76/0.97  thf('66', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.76/0.97      inference('simplify_reflect+', [status(thm)], ['64', '65'])).
% 0.76/0.97  thf('67', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['55', '66'])).
% 0.76/0.97  thf(t60_relat_1, axiom,
% 0.76/0.97    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.76/0.97     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.76/0.97  thf('68', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.97      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.76/0.97  thf('69', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.76/0.97      inference('demod', [status(thm)], ['18', '67', '68'])).
% 0.76/0.97  thf('70', plain,
% 0.76/0.97      (![X40 : $i, X41 : $i]:
% 0.76/0.97         (~ (r2_hidden @ X40 @ X41)
% 0.76/0.97          | ((k4_xboole_0 @ (k1_tarski @ X40) @ X41) != (k1_tarski @ X40)))),
% 0.76/0.97      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.76/0.97  thf('71', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (((k4_xboole_0 @ k1_xboole_0 @ X0) != (k1_tarski @ sk_A))
% 0.76/0.97          | ~ (r2_hidden @ sk_A @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['69', '70'])).
% 0.76/0.97  thf(commutativity_k2_tarski, axiom,
% 0.76/0.97    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.76/0.97  thf('72', plain,
% 0.76/0.97      (![X10 : $i, X11 : $i]:
% 0.76/0.97         ((k2_tarski @ X11 @ X10) = (k2_tarski @ X10 @ X11))),
% 0.76/0.97      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.76/0.97  thf(t12_setfam_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.76/0.97  thf('73', plain,
% 0.76/0.97      (![X49 : $i, X50 : $i]:
% 0.76/0.97         ((k1_setfam_1 @ (k2_tarski @ X49 @ X50)) = (k3_xboole_0 @ X49 @ X50))),
% 0.76/0.97      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.76/0.97  thf('74', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.76/0.97      inference('sup+', [status(thm)], ['72', '73'])).
% 0.76/0.97  thf('75', plain,
% 0.76/0.97      (![X49 : $i, X50 : $i]:
% 0.76/0.97         ((k1_setfam_1 @ (k2_tarski @ X49 @ X50)) = (k3_xboole_0 @ X49 @ X50))),
% 0.76/0.97      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.76/0.97  thf('76', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.76/0.97      inference('sup+', [status(thm)], ['74', '75'])).
% 0.76/0.97  thf('77', plain,
% 0.76/0.97      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.97      inference('cnf', [status(esa)], [t2_boole])).
% 0.76/0.97  thf('78', plain,
% 0.76/0.97      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.76/0.97      inference('sup+', [status(thm)], ['76', '77'])).
% 0.76/0.97  thf('79', plain,
% 0.76/0.97      (![X6 : $i, X7 : $i]:
% 0.76/0.97         ((k4_xboole_0 @ X6 @ X7)
% 0.76/0.97           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.76/0.97      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.76/0.97  thf(commutativity_k5_xboole_0, axiom,
% 0.76/0.97    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.76/0.97  thf('80', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.76/0.97      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.76/0.97  thf('81', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.76/0.97      inference('cnf', [status(esa)], [t5_boole])).
% 0.76/0.97  thf('82', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.76/0.97      inference('sup+', [status(thm)], ['80', '81'])).
% 0.76/0.97  thf('83', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.76/0.97      inference('sup+', [status(thm)], ['79', '82'])).
% 0.76/0.97  thf('84', plain,
% 0.76/0.97      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.76/0.97      inference('sup+', [status(thm)], ['78', '83'])).
% 0.76/0.97  thf('85', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.76/0.97      inference('demod', [status(thm)], ['18', '67', '68'])).
% 0.76/0.97  thf('86', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ sk_A @ X0))),
% 0.76/0.97      inference('demod', [status(thm)], ['71', '84', '85'])).
% 0.76/0.97  thf('87', plain, (![X0 : $i]: ~ (r2_hidden @ sk_A @ X0)),
% 0.76/0.97      inference('simplify', [status(thm)], ['86'])).
% 0.76/0.97  thf('88', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.76/0.97      inference('demod', [status(thm)], ['7', '14', '17'])).
% 0.76/0.97  thf(t31_zfmisc_1, axiom,
% 0.76/0.97    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.76/0.97  thf('89', plain, (![X43 : $i]: ((k3_tarski @ (k1_tarski @ X43)) = (X43))),
% 0.76/0.97      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.76/0.97  thf('90', plain, (((k3_tarski @ (k1_relat_1 @ sk_C_1)) = (sk_A))),
% 0.76/0.97      inference('sup+', [status(thm)], ['88', '89'])).
% 0.76/0.97  thf('91', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['55', '66'])).
% 0.76/0.97  thf('92', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.97      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.76/0.97  thf('93', plain, (((k3_tarski @ k1_xboole_0) = (sk_A))),
% 0.76/0.97      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.76/0.97  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.76/0.97  thf('94', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.97      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.76/0.97  thf('95', plain, (((sk_A) = (k1_xboole_0))),
% 0.76/0.97      inference('sup+', [status(thm)], ['93', '94'])).
% 0.76/0.97  thf('96', plain, (![X0 : $i]: ~ (r2_hidden @ k1_xboole_0 @ X0)),
% 0.76/0.97      inference('demod', [status(thm)], ['87', '95'])).
% 0.76/0.97  thf('97', plain, ($false), inference('sup-', [status(thm)], ['4', '96'])).
% 0.76/0.97  
% 0.76/0.97  % SZS output end Refutation
% 0.76/0.97  
% 0.76/0.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
