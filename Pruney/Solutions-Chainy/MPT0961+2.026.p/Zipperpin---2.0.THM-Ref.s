%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3kHTJNmdxn

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:42 EST 2020

% Result     : Theorem 0.64s
% Output     : Refutation 0.64s
% Verified   : 
% Statistics : Number of formulae       :  129 (1948 expanded)
%              Number of leaves         :   35 ( 605 expanded)
%              Depth                    :   21
%              Number of atoms          :  922 (17870 expanded)
%              Number of equality atoms :   54 ( 539 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X4 ) @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('1',plain,(
    ! [X3: $i] :
      ( ( k2_subset_1 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('2',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X8 ) ) )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('5',plain,(
    ! [X17: $i] :
      ( ( X17 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X17 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('10',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      = ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
        = ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

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

thf(zf_stmt_0,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('16',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( X22
       != ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
       != ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_4,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X25 != k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( v1_funct_2 @ X27 @ X26 @ X25 )
      | ( X27 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('21',plain,(
    ! [X26: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X26 @ k1_xboole_0 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('24',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf(t3_funct_2,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf(zf_stmt_5,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v1_funct_1 @ A )
          & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
          & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t3_funct_2])).

thf('26',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('27',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
   <= ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('29',plain,
    ( ~ ( v1_funct_1 @ sk_A )
   <= ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['26'])).

thf('30',plain,(
    v1_funct_1 @ sk_A ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('32',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('35',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X16 )
      | ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,
    ( ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['26'])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ sk_A )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('41',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['26'])).

thf('43',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['30','41','42'])).

thf('44',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['27','43'])).

thf('45',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('47',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('51',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( X22
       != ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['27','43'])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('61',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','61'])).

thf('63',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['59','60'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('65',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X8 ) ) )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('69',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('70',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('72',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['70','71'])).

thf('74',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','72','73'])).

thf('75',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['25','74'])).

thf('76',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['25','74'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('79',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X21 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('80',plain,(
    ! [X20: $i] :
      ( zip_tseitin_0 @ X20 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('82',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['77','85'])).

thf('87',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','72','73'])).

thf('88',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['25','74'])).

thf('89',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('92',plain,(
    $false ),
    inference(demod,[status(thm)],['90','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3kHTJNmdxn
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:54:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.64/0.85  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.64/0.85  % Solved by: fo/fo7.sh
% 0.64/0.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.64/0.85  % done 302 iterations in 0.401s
% 0.64/0.85  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.64/0.85  % SZS output start Refutation
% 0.64/0.85  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.64/0.85  thf(sk_A_type, type, sk_A: $i).
% 0.64/0.85  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.64/0.85  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.64/0.85  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.64/0.85  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.64/0.85  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.64/0.85  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.64/0.85  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.64/0.85  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.64/0.85  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.64/0.85  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.64/0.85  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.64/0.85  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.64/0.85  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.64/0.85  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.64/0.85  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.64/0.85  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.64/0.85  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.64/0.85  thf(dt_k2_subset_1, axiom,
% 0.64/0.85    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.64/0.85  thf('0', plain,
% 0.64/0.85      (![X4 : $i]: (m1_subset_1 @ (k2_subset_1 @ X4) @ (k1_zfmisc_1 @ X4))),
% 0.64/0.85      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.64/0.85  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.64/0.85  thf('1', plain, (![X3 : $i]: ((k2_subset_1 @ X3) = (X3))),
% 0.64/0.85      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.64/0.85  thf('2', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.64/0.85      inference('demod', [status(thm)], ['0', '1'])).
% 0.64/0.85  thf(cc4_relset_1, axiom,
% 0.64/0.85    (![A:$i,B:$i]:
% 0.64/0.85     ( ( v1_xboole_0 @ A ) =>
% 0.64/0.85       ( ![C:$i]:
% 0.64/0.85         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.64/0.85           ( v1_xboole_0 @ C ) ) ) ))).
% 0.64/0.85  thf('3', plain,
% 0.64/0.85      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.64/0.85         (~ (v1_xboole_0 @ X8)
% 0.64/0.85          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X8)))
% 0.64/0.85          | (v1_xboole_0 @ X9))),
% 0.64/0.85      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.64/0.85  thf('4', plain,
% 0.64/0.85      (![X0 : $i, X1 : $i]:
% 0.64/0.85         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.64/0.85      inference('sup-', [status(thm)], ['2', '3'])).
% 0.64/0.85  thf(t9_mcart_1, axiom,
% 0.64/0.85    (![A:$i]:
% 0.64/0.85     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.64/0.85          ( ![B:$i]:
% 0.64/0.85            ( ~( ( r2_hidden @ B @ A ) & 
% 0.64/0.85                 ( ![C:$i,D:$i]:
% 0.64/0.85                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.64/0.85                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.64/0.85  thf('5', plain,
% 0.64/0.85      (![X17 : $i]:
% 0.64/0.85         (((X17) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X17) @ X17))),
% 0.64/0.85      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.64/0.85  thf(d1_xboole_0, axiom,
% 0.64/0.85    (![A:$i]:
% 0.64/0.85     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.64/0.85  thf('6', plain,
% 0.64/0.85      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.64/0.85      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.64/0.85  thf('7', plain,
% 0.64/0.85      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.64/0.85      inference('sup-', [status(thm)], ['5', '6'])).
% 0.64/0.85  thf('8', plain,
% 0.64/0.85      (![X0 : $i, X1 : $i]:
% 0.64/0.85         (~ (v1_xboole_0 @ X0) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.64/0.85      inference('sup-', [status(thm)], ['4', '7'])).
% 0.64/0.85  thf('9', plain,
% 0.64/0.85      (![X0 : $i, X1 : $i]:
% 0.64/0.85         (~ (v1_xboole_0 @ X0) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.64/0.85      inference('sup-', [status(thm)], ['4', '7'])).
% 0.64/0.85  thf('10', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.64/0.85      inference('demod', [status(thm)], ['0', '1'])).
% 0.64/0.85  thf(redefinition_k1_relset_1, axiom,
% 0.64/0.85    (![A:$i,B:$i,C:$i]:
% 0.64/0.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.64/0.85       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.64/0.85  thf('11', plain,
% 0.64/0.85      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.64/0.85         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 0.64/0.85          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.64/0.85      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.64/0.85  thf('12', plain,
% 0.64/0.85      (![X0 : $i, X1 : $i]:
% 0.64/0.85         ((k1_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.64/0.85           = (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.64/0.85      inference('sup-', [status(thm)], ['10', '11'])).
% 0.64/0.85  thf('13', plain,
% 0.64/0.85      (![X0 : $i, X1 : $i]:
% 0.64/0.85         (((k1_relset_1 @ X1 @ X0 @ k1_xboole_0)
% 0.64/0.85            = (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.64/0.85          | ~ (v1_xboole_0 @ X0))),
% 0.64/0.85      inference('sup+', [status(thm)], ['9', '12'])).
% 0.64/0.85  thf('14', plain,
% 0.64/0.85      (![X0 : $i, X1 : $i]:
% 0.64/0.85         (((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))
% 0.64/0.85          | ~ (v1_xboole_0 @ X0)
% 0.64/0.85          | ~ (v1_xboole_0 @ X0))),
% 0.64/0.85      inference('sup+', [status(thm)], ['8', '13'])).
% 0.64/0.85  thf('15', plain,
% 0.64/0.85      (![X0 : $i, X1 : $i]:
% 0.64/0.85         (~ (v1_xboole_0 @ X0)
% 0.64/0.85          | ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.64/0.85      inference('simplify', [status(thm)], ['14'])).
% 0.64/0.85  thf(d1_funct_2, axiom,
% 0.64/0.85    (![A:$i,B:$i,C:$i]:
% 0.64/0.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.64/0.85       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.64/0.85           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.64/0.85             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.64/0.85         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.64/0.85           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.64/0.85             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.64/0.85  thf(zf_stmt_0, axiom,
% 0.64/0.85    (![C:$i,B:$i,A:$i]:
% 0.64/0.85     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.64/0.85       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.64/0.85  thf('16', plain,
% 0.64/0.85      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.64/0.85         (((X22) != (k1_relset_1 @ X22 @ X23 @ X24))
% 0.64/0.85          | (v1_funct_2 @ X24 @ X22 @ X23)
% 0.64/0.85          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 0.64/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.85  thf('17', plain,
% 0.64/0.85      (![X0 : $i, X1 : $i]:
% 0.64/0.85         (((X1) != (k1_relat_1 @ k1_xboole_0))
% 0.64/0.85          | ~ (v1_xboole_0 @ X0)
% 0.64/0.85          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 0.64/0.85          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 0.64/0.85      inference('sup-', [status(thm)], ['15', '16'])).
% 0.64/0.85  thf('18', plain,
% 0.64/0.85      (![X0 : $i]:
% 0.64/0.85         ((v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0)
% 0.64/0.85          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ (k1_relat_1 @ k1_xboole_0))
% 0.64/0.85          | ~ (v1_xboole_0 @ X0))),
% 0.64/0.85      inference('simplify', [status(thm)], ['17'])).
% 0.64/0.85  thf('19', plain,
% 0.64/0.85      (![X0 : $i, X1 : $i]:
% 0.64/0.85         (~ (v1_xboole_0 @ X0) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.64/0.85      inference('sup-', [status(thm)], ['4', '7'])).
% 0.64/0.85  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.64/0.85  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $o).
% 0.64/0.85  thf(zf_stmt_3, axiom,
% 0.64/0.85    (![B:$i,A:$i]:
% 0.64/0.85     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.64/0.85       ( zip_tseitin_0 @ B @ A ) ))).
% 0.64/0.85  thf(zf_stmt_4, axiom,
% 0.64/0.85    (![A:$i,B:$i,C:$i]:
% 0.64/0.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.64/0.85       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.64/0.85         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.64/0.85           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.64/0.85             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.64/0.85  thf('20', plain,
% 0.64/0.85      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.64/0.85         (((X25) != (k1_xboole_0))
% 0.64/0.85          | ((X26) = (k1_xboole_0))
% 0.64/0.85          | (v1_funct_2 @ X27 @ X26 @ X25)
% 0.64/0.85          | ((X27) != (k1_xboole_0))
% 0.64/0.85          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.64/0.85      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.64/0.85  thf('21', plain,
% 0.64/0.85      (![X26 : $i]:
% 0.64/0.85         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 0.64/0.85             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ k1_xboole_0)))
% 0.64/0.85          | (v1_funct_2 @ k1_xboole_0 @ X26 @ k1_xboole_0)
% 0.64/0.85          | ((X26) = (k1_xboole_0)))),
% 0.64/0.85      inference('simplify', [status(thm)], ['20'])).
% 0.64/0.85  thf('22', plain,
% 0.64/0.85      (![X0 : $i]:
% 0.64/0.85         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.64/0.85          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.64/0.85          | ((X0) = (k1_xboole_0))
% 0.64/0.85          | (v1_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.64/0.85      inference('sup-', [status(thm)], ['19', '21'])).
% 0.64/0.85  thf('23', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.64/0.85      inference('demod', [status(thm)], ['0', '1'])).
% 0.64/0.85  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.64/0.85  thf('24', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.64/0.85      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.64/0.85  thf('25', plain,
% 0.64/0.85      (![X0 : $i]:
% 0.64/0.85         (((X0) = (k1_xboole_0))
% 0.64/0.85          | (v1_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.64/0.85      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.64/0.85  thf(t3_funct_2, conjecture,
% 0.64/0.85    (![A:$i]:
% 0.64/0.85     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.64/0.85       ( ( v1_funct_1 @ A ) & 
% 0.64/0.85         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.64/0.85         ( m1_subset_1 @
% 0.64/0.85           A @ 
% 0.64/0.85           ( k1_zfmisc_1 @
% 0.64/0.85             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.64/0.85  thf(zf_stmt_5, negated_conjecture,
% 0.64/0.85    (~( ![A:$i]:
% 0.64/0.85        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.64/0.85          ( ( v1_funct_1 @ A ) & 
% 0.64/0.85            ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.64/0.85            ( m1_subset_1 @
% 0.64/0.85              A @ 
% 0.64/0.85              ( k1_zfmisc_1 @
% 0.64/0.85                ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 0.64/0.85    inference('cnf.neg', [status(esa)], [t3_funct_2])).
% 0.64/0.85  thf('26', plain,
% 0.64/0.85      ((~ (v1_funct_1 @ sk_A)
% 0.64/0.85        | ~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.64/0.85        | ~ (m1_subset_1 @ sk_A @ 
% 0.64/0.85             (k1_zfmisc_1 @ 
% 0.64/0.85              (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.64/0.85      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.64/0.85  thf('27', plain,
% 0.64/0.85      ((~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 0.64/0.85         <= (~
% 0.64/0.85             ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))),
% 0.64/0.85      inference('split', [status(esa)], ['26'])).
% 0.64/0.85  thf('28', plain, ((v1_funct_1 @ sk_A)),
% 0.64/0.85      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.64/0.85  thf('29', plain, ((~ (v1_funct_1 @ sk_A)) <= (~ ((v1_funct_1 @ sk_A)))),
% 0.64/0.85      inference('split', [status(esa)], ['26'])).
% 0.64/0.85  thf('30', plain, (((v1_funct_1 @ sk_A))),
% 0.64/0.85      inference('sup-', [status(thm)], ['28', '29'])).
% 0.64/0.85  thf('31', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.64/0.85      inference('demod', [status(thm)], ['0', '1'])).
% 0.64/0.85  thf(t3_subset, axiom,
% 0.64/0.85    (![A:$i,B:$i]:
% 0.64/0.85     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.64/0.85  thf('32', plain,
% 0.64/0.85      (![X5 : $i, X6 : $i]:
% 0.64/0.85         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.64/0.85      inference('cnf', [status(esa)], [t3_subset])).
% 0.64/0.85  thf('33', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.64/0.85      inference('sup-', [status(thm)], ['31', '32'])).
% 0.64/0.85  thf('34', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.64/0.85      inference('sup-', [status(thm)], ['31', '32'])).
% 0.64/0.85  thf(t11_relset_1, axiom,
% 0.64/0.85    (![A:$i,B:$i,C:$i]:
% 0.64/0.85     ( ( v1_relat_1 @ C ) =>
% 0.64/0.85       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.64/0.85           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.64/0.85         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.64/0.85  thf('35', plain,
% 0.64/0.85      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.64/0.85         (~ (r1_tarski @ (k1_relat_1 @ X14) @ X15)
% 0.64/0.85          | ~ (r1_tarski @ (k2_relat_1 @ X14) @ X16)
% 0.64/0.85          | (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.64/0.85          | ~ (v1_relat_1 @ X14))),
% 0.64/0.85      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.64/0.85  thf('36', plain,
% 0.64/0.85      (![X0 : $i, X1 : $i]:
% 0.64/0.85         (~ (v1_relat_1 @ X0)
% 0.64/0.85          | (m1_subset_1 @ X0 @ 
% 0.64/0.85             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.64/0.85          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.64/0.85      inference('sup-', [status(thm)], ['34', '35'])).
% 0.64/0.85  thf('37', plain,
% 0.64/0.85      (![X0 : $i]:
% 0.64/0.85         ((m1_subset_1 @ X0 @ 
% 0.64/0.85           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.64/0.85          | ~ (v1_relat_1 @ X0))),
% 0.64/0.85      inference('sup-', [status(thm)], ['33', '36'])).
% 0.64/0.85  thf('38', plain,
% 0.64/0.85      ((~ (m1_subset_1 @ sk_A @ 
% 0.64/0.85           (k1_zfmisc_1 @ 
% 0.64/0.85            (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))
% 0.64/0.85         <= (~
% 0.64/0.85             ((m1_subset_1 @ sk_A @ 
% 0.64/0.85               (k1_zfmisc_1 @ 
% 0.64/0.85                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.64/0.85      inference('split', [status(esa)], ['26'])).
% 0.64/0.85  thf('39', plain,
% 0.64/0.85      ((~ (v1_relat_1 @ sk_A))
% 0.64/0.85         <= (~
% 0.64/0.85             ((m1_subset_1 @ sk_A @ 
% 0.64/0.85               (k1_zfmisc_1 @ 
% 0.64/0.85                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.64/0.85      inference('sup-', [status(thm)], ['37', '38'])).
% 0.64/0.85  thf('40', plain, ((v1_relat_1 @ sk_A)),
% 0.64/0.85      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.64/0.85  thf('41', plain,
% 0.64/0.85      (((m1_subset_1 @ sk_A @ 
% 0.64/0.85         (k1_zfmisc_1 @ 
% 0.64/0.85          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.64/0.85      inference('demod', [status(thm)], ['39', '40'])).
% 0.64/0.85  thf('42', plain,
% 0.64/0.85      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) | 
% 0.64/0.85       ~
% 0.64/0.85       ((m1_subset_1 @ sk_A @ 
% 0.64/0.85         (k1_zfmisc_1 @ 
% 0.64/0.85          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))) | 
% 0.64/0.85       ~ ((v1_funct_1 @ sk_A))),
% 0.64/0.85      inference('split', [status(esa)], ['26'])).
% 0.64/0.85  thf('43', plain,
% 0.64/0.85      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 0.64/0.85      inference('sat_resolution*', [status(thm)], ['30', '41', '42'])).
% 0.64/0.85  thf('44', plain,
% 0.64/0.85      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.64/0.85      inference('simpl_trail', [status(thm)], ['27', '43'])).
% 0.64/0.85  thf('45', plain,
% 0.64/0.85      (![X20 : $i, X21 : $i]:
% 0.64/0.85         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 0.64/0.85      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.64/0.85  thf('46', plain,
% 0.64/0.85      (![X0 : $i]:
% 0.64/0.85         ((m1_subset_1 @ X0 @ 
% 0.64/0.85           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.64/0.85          | ~ (v1_relat_1 @ X0))),
% 0.64/0.85      inference('sup-', [status(thm)], ['33', '36'])).
% 0.64/0.85  thf('47', plain,
% 0.64/0.85      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.64/0.85         (~ (zip_tseitin_0 @ X25 @ X26)
% 0.64/0.85          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 0.64/0.85          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.64/0.85      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.64/0.85  thf('48', plain,
% 0.64/0.85      (![X0 : $i]:
% 0.64/0.85         (~ (v1_relat_1 @ X0)
% 0.64/0.85          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.64/0.85          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.64/0.85      inference('sup-', [status(thm)], ['46', '47'])).
% 0.64/0.85  thf('49', plain,
% 0.64/0.85      (![X0 : $i]:
% 0.64/0.85         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.64/0.85          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.64/0.85          | ~ (v1_relat_1 @ X0))),
% 0.64/0.85      inference('sup-', [status(thm)], ['45', '48'])).
% 0.64/0.85  thf('50', plain,
% 0.64/0.85      (![X0 : $i]:
% 0.64/0.85         ((m1_subset_1 @ X0 @ 
% 0.64/0.85           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.64/0.85          | ~ (v1_relat_1 @ X0))),
% 0.64/0.85      inference('sup-', [status(thm)], ['33', '36'])).
% 0.64/0.85  thf('51', plain,
% 0.64/0.85      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.64/0.85         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 0.64/0.85          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.64/0.85      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.64/0.85  thf('52', plain,
% 0.64/0.85      (![X0 : $i]:
% 0.64/0.85         (~ (v1_relat_1 @ X0)
% 0.64/0.85          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.64/0.85              = (k1_relat_1 @ X0)))),
% 0.64/0.85      inference('sup-', [status(thm)], ['50', '51'])).
% 0.64/0.85  thf('53', plain,
% 0.64/0.85      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.64/0.85         (((X22) != (k1_relset_1 @ X22 @ X23 @ X24))
% 0.64/0.85          | (v1_funct_2 @ X24 @ X22 @ X23)
% 0.64/0.85          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 0.64/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.85  thf('54', plain,
% 0.64/0.85      (![X0 : $i]:
% 0.64/0.85         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.64/0.85          | ~ (v1_relat_1 @ X0)
% 0.64/0.85          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.64/0.85          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.64/0.85      inference('sup-', [status(thm)], ['52', '53'])).
% 0.64/0.85  thf('55', plain,
% 0.64/0.85      (![X0 : $i]:
% 0.64/0.85         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.64/0.85          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.64/0.85          | ~ (v1_relat_1 @ X0))),
% 0.64/0.85      inference('simplify', [status(thm)], ['54'])).
% 0.64/0.85  thf('56', plain,
% 0.64/0.85      (![X0 : $i]:
% 0.64/0.85         (~ (v1_relat_1 @ X0)
% 0.64/0.85          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.64/0.85          | ~ (v1_relat_1 @ X0)
% 0.64/0.85          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.64/0.85      inference('sup-', [status(thm)], ['49', '55'])).
% 0.64/0.85  thf('57', plain,
% 0.64/0.85      (![X0 : $i]:
% 0.64/0.85         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.64/0.85          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.64/0.85          | ~ (v1_relat_1 @ X0))),
% 0.64/0.85      inference('simplify', [status(thm)], ['56'])).
% 0.64/0.85  thf('58', plain,
% 0.64/0.85      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.64/0.85      inference('simpl_trail', [status(thm)], ['27', '43'])).
% 0.64/0.85  thf('59', plain,
% 0.64/0.85      ((~ (v1_relat_1 @ sk_A) | ((k2_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.64/0.85      inference('sup-', [status(thm)], ['57', '58'])).
% 0.64/0.85  thf('60', plain, ((v1_relat_1 @ sk_A)),
% 0.64/0.85      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.64/0.85  thf('61', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.64/0.85      inference('demod', [status(thm)], ['59', '60'])).
% 0.64/0.85  thf('62', plain, (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ k1_xboole_0)),
% 0.64/0.85      inference('demod', [status(thm)], ['44', '61'])).
% 0.64/0.85  thf('63', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.64/0.85      inference('demod', [status(thm)], ['59', '60'])).
% 0.64/0.85  thf('64', plain,
% 0.64/0.85      (![X0 : $i]:
% 0.64/0.85         ((m1_subset_1 @ X0 @ 
% 0.64/0.85           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.64/0.85          | ~ (v1_relat_1 @ X0))),
% 0.64/0.85      inference('sup-', [status(thm)], ['33', '36'])).
% 0.64/0.85  thf('65', plain,
% 0.64/0.85      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.64/0.85         (~ (v1_xboole_0 @ X8)
% 0.64/0.85          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X8)))
% 0.64/0.85          | (v1_xboole_0 @ X9))),
% 0.64/0.85      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.64/0.85  thf('66', plain,
% 0.64/0.85      (![X0 : $i]:
% 0.64/0.85         (~ (v1_relat_1 @ X0)
% 0.64/0.85          | (v1_xboole_0 @ X0)
% 0.64/0.85          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0)))),
% 0.64/0.85      inference('sup-', [status(thm)], ['64', '65'])).
% 0.64/0.85  thf('67', plain,
% 0.64/0.85      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.64/0.85        | (v1_xboole_0 @ sk_A)
% 0.64/0.85        | ~ (v1_relat_1 @ sk_A))),
% 0.64/0.85      inference('sup-', [status(thm)], ['63', '66'])).
% 0.64/0.85  thf('68', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.64/0.85      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.64/0.85  thf('69', plain, ((v1_relat_1 @ sk_A)),
% 0.64/0.85      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.64/0.85  thf('70', plain, ((v1_xboole_0 @ sk_A)),
% 0.64/0.85      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.64/0.85  thf('71', plain,
% 0.64/0.85      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.64/0.85      inference('sup-', [status(thm)], ['5', '6'])).
% 0.64/0.85  thf('72', plain, (((sk_A) = (k1_xboole_0))),
% 0.64/0.85      inference('sup-', [status(thm)], ['70', '71'])).
% 0.64/0.85  thf('73', plain, (((sk_A) = (k1_xboole_0))),
% 0.64/0.85      inference('sup-', [status(thm)], ['70', '71'])).
% 0.64/0.85  thf('74', plain,
% 0.64/0.85      (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 0.64/0.85      inference('demod', [status(thm)], ['62', '72', '73'])).
% 0.64/0.85  thf('75', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.64/0.85      inference('sup-', [status(thm)], ['25', '74'])).
% 0.64/0.85  thf('76', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.64/0.85      inference('sup-', [status(thm)], ['25', '74'])).
% 0.64/0.85  thf('77', plain,
% 0.64/0.85      (![X0 : $i]:
% 0.64/0.85         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 0.64/0.85          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)
% 0.64/0.85          | ~ (v1_xboole_0 @ X0))),
% 0.64/0.85      inference('demod', [status(thm)], ['18', '75', '76'])).
% 0.64/0.85  thf('78', plain,
% 0.64/0.85      (![X0 : $i, X1 : $i]:
% 0.64/0.85         (~ (v1_xboole_0 @ X0) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.64/0.85      inference('sup-', [status(thm)], ['4', '7'])).
% 0.64/0.85  thf('79', plain,
% 0.64/0.85      (![X20 : $i, X21 : $i]:
% 0.64/0.85         ((zip_tseitin_0 @ X20 @ X21) | ((X21) != (k1_xboole_0)))),
% 0.64/0.85      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.64/0.85  thf('80', plain, (![X20 : $i]: (zip_tseitin_0 @ X20 @ k1_xboole_0)),
% 0.64/0.85      inference('simplify', [status(thm)], ['79'])).
% 0.64/0.85  thf('81', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.64/0.85      inference('demod', [status(thm)], ['0', '1'])).
% 0.64/0.85  thf('82', plain,
% 0.64/0.85      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.64/0.85         (~ (zip_tseitin_0 @ X25 @ X26)
% 0.64/0.85          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 0.64/0.85          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.64/0.85      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.64/0.85  thf('83', plain,
% 0.64/0.85      (![X0 : $i, X1 : $i]:
% 0.64/0.85         ((zip_tseitin_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X0 @ X1)
% 0.64/0.85          | ~ (zip_tseitin_0 @ X0 @ X1))),
% 0.64/0.85      inference('sup-', [status(thm)], ['81', '82'])).
% 0.64/0.85  thf('84', plain,
% 0.64/0.85      (![X0 : $i]:
% 0.64/0.85         (zip_tseitin_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0) @ X0 @ k1_xboole_0)),
% 0.64/0.85      inference('sup-', [status(thm)], ['80', '83'])).
% 0.64/0.85  thf('85', plain,
% 0.64/0.85      (![X0 : $i]:
% 0.64/0.85         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)
% 0.64/0.85          | ~ (v1_xboole_0 @ X0))),
% 0.64/0.85      inference('sup+', [status(thm)], ['78', '84'])).
% 0.64/0.85  thf('86', plain,
% 0.64/0.85      (![X0 : $i]:
% 0.64/0.85         (~ (v1_xboole_0 @ X0) | (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.64/0.85      inference('clc', [status(thm)], ['77', '85'])).
% 0.64/0.85  thf('87', plain,
% 0.64/0.85      (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 0.64/0.85      inference('demod', [status(thm)], ['62', '72', '73'])).
% 0.64/0.85  thf('88', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.64/0.85      inference('sup-', [status(thm)], ['25', '74'])).
% 0.64/0.85  thf('89', plain, (~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.64/0.85      inference('demod', [status(thm)], ['87', '88'])).
% 0.64/0.85  thf('90', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.64/0.85      inference('sup-', [status(thm)], ['86', '89'])).
% 0.64/0.85  thf('91', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.64/0.85      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.64/0.85  thf('92', plain, ($false), inference('demod', [status(thm)], ['90', '91'])).
% 0.64/0.85  
% 0.64/0.85  % SZS output end Refutation
% 0.64/0.85  
% 0.71/0.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
