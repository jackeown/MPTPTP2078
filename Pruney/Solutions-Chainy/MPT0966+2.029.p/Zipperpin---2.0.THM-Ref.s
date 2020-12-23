%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ncCtGClYSh

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:10 EST 2020

% Result     : Theorem 2.69s
% Output     : Refutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :  228 (4051 expanded)
%              Number of leaves         :   44 (1201 expanded)
%              Depth                    :   29
%              Number of atoms          : 1485 (42061 expanded)
%              Number of equality atoms :  131 (3684 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf('0',plain,(
    ! [X30: $i] :
      ( ( X30 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X30 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('4',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('10',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t194_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) @ X17 ) ),
    inference(cnf,[status(esa)],[t194_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X30: $i] :
      ( ( X30 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X30 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('16',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('17',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('18',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('19',plain,(
    m1_subset_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k6_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('22',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k6_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','23'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('25',plain,(
    ! [X19: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('26',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','26'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('28',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','23'])).

thf('31',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('32',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','32'])).

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

thf('34',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( X36
       != ( k1_relset_1 @ X36 @ X37 @ X38 ) )
      | ( v1_funct_2 @ X38 @ X36 @ X37 )
      | ~ ( zip_tseitin_1 @ X38 @ X37 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('37',plain,(
    ! [X34: $i,X35: $i] :
      ( ( zip_tseitin_0 @ X34 @ X35 )
      | ( X35 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('38',plain,(
    ! [X34: $i] :
      ( zip_tseitin_0 @ X34 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','26'])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('40',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( zip_tseitin_0 @ X39 @ X40 )
      | ( zip_tseitin_1 @ X41 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['36','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ X0 @ k1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ X2 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['7','44'])).

thf(t8_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ C )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_5,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C )
         => ( ( ( B = k1_xboole_0 )
              & ( A != k1_xboole_0 ) )
            | ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ C )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_funct_2])).

thf('46',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('47',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,
    ( ( ~ ( v1_xboole_0 @ sk_D )
      | ~ ( v1_xboole_0 @ sk_A ) )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('50',plain,(
    ! [X34: $i,X35: $i] :
      ( ( zip_tseitin_0 @ X34 @ X35 )
      | ( X34 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('51',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','23'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('54',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( zip_tseitin_0 @ X39 @ X40 )
      | ( zip_tseitin_1 @ X41 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('55',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k6_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('58',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_2 @ X38 @ X36 @ X37 )
      | ( X36
        = ( k1_relset_1 @ X36 @ X37 @ X38 ) )
      | ~ ( zip_tseitin_1 @ X38 @ X37 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('61',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('62',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('64',plain,
    ( ( ( k6_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['56','63'])).

thf('65',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('67',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['30','31'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('70',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['24','25'])).

thf('71',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','73'])).

thf('75',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) @ X17 ) ),
    inference(cnf,[status(esa)],[t194_relat_1])).

thf('78',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( sk_B_1
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('82',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['24','25'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['80','83'])).

thf('85',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('86',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['85'])).

thf('87',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('88',plain,
    ( ~ ( v1_funct_1 @ sk_D )
   <= ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['46'])).

thf('89',plain,(
    v1_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['36','42'])).

thf('91',plain,(
    ! [X30: $i] :
      ( ( X30 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X30 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('92',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['85'])).

thf('93',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('94',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('96',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('98',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('99',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['91','99'])).

thf('101',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['85'])).

thf('102',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['46'])).

thf('103',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['100','103'])).

thf('105',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['90','104'])).

thf('106',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('107',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('108',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('110',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['85'])).

thf('111',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['46'])).

thf('112',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['109','112'])).

thf('114',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['108','113'])).

thf('115',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['46'])).

thf('116',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['85'])).

thf('117',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['89','105','114','115','116'])).

thf('118',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['86','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['84','118'])).

thf('120',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['49','119'])).

thf('121',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('122',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('124',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['122','125'])).

thf('127',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['48','126'])).

thf('128',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('129',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('130',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('131',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference(demod,[status(thm)],['128','131'])).

thf('133',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('134',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X26 ) @ X27 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X26 ) @ X28 )
      | ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['132','135'])).

thf('137',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('138',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('139',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('140',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('141',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('142',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['136','137','142'])).

thf('144',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['46'])).

thf('145',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['46'])).

thf('147',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['89','145','146'])).

thf('148',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['127','147'])).

thf('149',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['136','137','142'])).

thf('150',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('151',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('153',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,
    ( ( sk_D
      = ( k2_zfmisc_1 @ sk_A @ sk_C ) )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['151','156'])).

thf('158',plain,(
    ! [X34: $i,X35: $i] :
      ( ( zip_tseitin_0 @ X34 @ X35 )
      | ( X34 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('159',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['136','137','142'])).

thf('160',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( zip_tseitin_0 @ X39 @ X40 )
      | ( zip_tseitin_1 @ X41 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('161',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['136','137','142'])).

thf('163',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('164',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('166',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( X36
       != ( k1_relset_1 @ X36 @ X37 @ X38 ) )
      | ( v1_funct_2 @ X38 @ X36 @ X37 )
      | ~ ( zip_tseitin_1 @ X38 @ X37 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['46'])).

thf('171',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['89','145','146'])).

thf('172',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['170','171'])).

thf('173',plain,(
    ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['169','172'])).

thf('174',plain,(
    ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['161','173'])).

thf('175',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['158','174'])).

thf('176',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('177',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['158','174'])).

thf('178',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('179',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('180',plain,(
    sk_D = k1_xboole_0 ),
    inference(demod,[status(thm)],['157','175','176','177','178','179'])).

thf('181',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('182',plain,(
    $false ),
    inference(demod,[status(thm)],['148','180','181'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ncCtGClYSh
% 0.15/0.36  % Computer   : n001.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 19:39:15 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 2.69/2.90  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.69/2.90  % Solved by: fo/fo7.sh
% 2.69/2.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.69/2.90  % done 3522 iterations in 2.465s
% 2.69/2.90  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.69/2.90  % SZS output start Refutation
% 2.69/2.90  thf(sk_B_type, type, sk_B: $i > $i).
% 2.69/2.90  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.69/2.90  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.69/2.90  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.69/2.90  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.69/2.90  thf(sk_D_type, type, sk_D: $i).
% 2.69/2.90  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.69/2.90  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.69/2.90  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.69/2.90  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.69/2.90  thf(sk_C_type, type, sk_C: $i).
% 2.69/2.90  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 2.69/2.90  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.69/2.90  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.69/2.90  thf(sk_A_type, type, sk_A: $i).
% 2.69/2.90  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.69/2.90  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.69/2.90  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.69/2.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.69/2.90  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.69/2.90  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.69/2.90  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.69/2.90  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.69/2.90  thf(t29_mcart_1, axiom,
% 2.69/2.90    (![A:$i]:
% 2.69/2.90     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 2.69/2.90          ( ![B:$i]:
% 2.69/2.90            ( ~( ( r2_hidden @ B @ A ) & 
% 2.69/2.90                 ( ![C:$i,D:$i,E:$i]:
% 2.69/2.90                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 2.69/2.90                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 2.69/2.90  thf('0', plain,
% 2.69/2.90      (![X30 : $i]:
% 2.69/2.90         (((X30) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X30) @ X30))),
% 2.69/2.90      inference('cnf', [status(esa)], [t29_mcart_1])).
% 2.69/2.90  thf(d10_xboole_0, axiom,
% 2.69/2.90    (![A:$i,B:$i]:
% 2.69/2.90     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.69/2.90  thf('1', plain,
% 2.69/2.90      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 2.69/2.90      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.69/2.90  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.69/2.90      inference('simplify', [status(thm)], ['1'])).
% 2.69/2.90  thf(t3_subset, axiom,
% 2.69/2.90    (![A:$i,B:$i]:
% 2.69/2.90     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.69/2.90  thf('3', plain,
% 2.69/2.90      (![X6 : $i, X8 : $i]:
% 2.69/2.90         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 2.69/2.90      inference('cnf', [status(esa)], [t3_subset])).
% 2.69/2.90  thf('4', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.69/2.90      inference('sup-', [status(thm)], ['2', '3'])).
% 2.69/2.90  thf(t5_subset, axiom,
% 2.69/2.90    (![A:$i,B:$i,C:$i]:
% 2.69/2.90     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 2.69/2.90          ( v1_xboole_0 @ C ) ) ))).
% 2.69/2.90  thf('5', plain,
% 2.69/2.90      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.69/2.90         (~ (r2_hidden @ X9 @ X10)
% 2.69/2.90          | ~ (v1_xboole_0 @ X11)
% 2.69/2.90          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 2.69/2.90      inference('cnf', [status(esa)], [t5_subset])).
% 2.69/2.90  thf('6', plain,
% 2.69/2.90      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 2.69/2.90      inference('sup-', [status(thm)], ['4', '5'])).
% 2.69/2.90  thf('7', plain,
% 2.69/2.90      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.69/2.90      inference('sup-', [status(thm)], ['0', '6'])).
% 2.69/2.90  thf('8', plain,
% 2.69/2.90      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.69/2.90      inference('sup-', [status(thm)], ['0', '6'])).
% 2.69/2.90  thf(t113_zfmisc_1, axiom,
% 2.69/2.90    (![A:$i,B:$i]:
% 2.69/2.90     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.69/2.90       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.69/2.90  thf('9', plain,
% 2.69/2.90      (![X4 : $i, X5 : $i]:
% 2.69/2.90         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 2.69/2.90      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.69/2.90  thf('10', plain,
% 2.69/2.90      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 2.69/2.90      inference('simplify', [status(thm)], ['9'])).
% 2.69/2.90  thf(t194_relat_1, axiom,
% 2.69/2.90    (![A:$i,B:$i]: ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ))).
% 2.69/2.90  thf('11', plain,
% 2.69/2.90      (![X16 : $i, X17 : $i]:
% 2.69/2.90         (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X16 @ X17)) @ X17)),
% 2.69/2.90      inference('cnf', [status(esa)], [t194_relat_1])).
% 2.69/2.90  thf('12', plain, (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)),
% 2.69/2.90      inference('sup+', [status(thm)], ['10', '11'])).
% 2.69/2.90  thf('13', plain,
% 2.69/2.90      (![X6 : $i, X8 : $i]:
% 2.69/2.90         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 2.69/2.90      inference('cnf', [status(esa)], [t3_subset])).
% 2.69/2.90  thf('14', plain,
% 2.69/2.90      (![X0 : $i]:
% 2.69/2.90         (m1_subset_1 @ (k2_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 2.69/2.90      inference('sup-', [status(thm)], ['12', '13'])).
% 2.69/2.90  thf('15', plain,
% 2.69/2.90      (![X30 : $i]:
% 2.69/2.90         (((X30) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X30) @ X30))),
% 2.69/2.90      inference('cnf', [status(esa)], [t29_mcart_1])).
% 2.69/2.90  thf('16', plain,
% 2.69/2.90      (![X4 : $i, X5 : $i]:
% 2.69/2.90         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 2.69/2.90      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.69/2.90  thf('17', plain,
% 2.69/2.90      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 2.69/2.90      inference('simplify', [status(thm)], ['16'])).
% 2.69/2.90  thf(t29_relset_1, axiom,
% 2.69/2.90    (![A:$i]:
% 2.69/2.90     ( m1_subset_1 @
% 2.69/2.90       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 2.69/2.90  thf('18', plain,
% 2.69/2.90      (![X29 : $i]:
% 2.69/2.90         (m1_subset_1 @ (k6_relat_1 @ X29) @ 
% 2.69/2.90          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 2.69/2.90      inference('cnf', [status(esa)], [t29_relset_1])).
% 2.69/2.90  thf('19', plain,
% 2.69/2.90      ((m1_subset_1 @ (k6_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 2.69/2.90      inference('sup+', [status(thm)], ['17', '18'])).
% 2.69/2.90  thf('20', plain,
% 2.69/2.90      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.69/2.90         (~ (r2_hidden @ X9 @ X10)
% 2.69/2.90          | ~ (v1_xboole_0 @ X11)
% 2.69/2.90          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 2.69/2.90      inference('cnf', [status(esa)], [t5_subset])).
% 2.69/2.90  thf('21', plain,
% 2.69/2.90      (![X0 : $i]:
% 2.69/2.90         (~ (v1_xboole_0 @ k1_xboole_0)
% 2.69/2.90          | ~ (r2_hidden @ X0 @ (k6_relat_1 @ k1_xboole_0)))),
% 2.69/2.90      inference('sup-', [status(thm)], ['19', '20'])).
% 2.69/2.90  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.69/2.90  thf('22', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.69/2.90      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.69/2.90  thf('23', plain,
% 2.69/2.90      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k6_relat_1 @ k1_xboole_0))),
% 2.69/2.90      inference('demod', [status(thm)], ['21', '22'])).
% 2.69/2.90  thf('24', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.69/2.90      inference('sup-', [status(thm)], ['15', '23'])).
% 2.69/2.90  thf(t71_relat_1, axiom,
% 2.69/2.90    (![A:$i]:
% 2.69/2.90     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 2.69/2.90       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 2.69/2.90  thf('25', plain, (![X19 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X19)) = (X19))),
% 2.69/2.90      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.69/2.90  thf('26', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.69/2.90      inference('sup+', [status(thm)], ['24', '25'])).
% 2.69/2.90  thf('27', plain,
% 2.69/2.90      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 2.69/2.90      inference('demod', [status(thm)], ['14', '26'])).
% 2.69/2.90  thf(redefinition_k1_relset_1, axiom,
% 2.69/2.90    (![A:$i,B:$i,C:$i]:
% 2.69/2.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.69/2.90       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.69/2.90  thf('28', plain,
% 2.69/2.90      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.69/2.90         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 2.69/2.90          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 2.69/2.90      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.69/2.90  thf('29', plain,
% 2.69/2.90      (![X0 : $i, X1 : $i]:
% 2.69/2.90         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 2.69/2.90      inference('sup-', [status(thm)], ['27', '28'])).
% 2.69/2.90  thf('30', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.69/2.90      inference('sup-', [status(thm)], ['15', '23'])).
% 2.69/2.90  thf('31', plain, (![X18 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 2.69/2.90      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.69/2.90  thf('32', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.69/2.90      inference('sup+', [status(thm)], ['30', '31'])).
% 2.69/2.90  thf('33', plain,
% 2.69/2.90      (![X0 : $i, X1 : $i]:
% 2.69/2.90         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 2.69/2.90      inference('demod', [status(thm)], ['29', '32'])).
% 2.69/2.90  thf(d1_funct_2, axiom,
% 2.69/2.90    (![A:$i,B:$i,C:$i]:
% 2.69/2.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.69/2.90       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.69/2.90           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.69/2.90             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.69/2.90         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.69/2.90           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.69/2.90             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.69/2.90  thf(zf_stmt_0, axiom,
% 2.69/2.90    (![C:$i,B:$i,A:$i]:
% 2.69/2.90     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.69/2.90       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.69/2.90  thf('34', plain,
% 2.69/2.90      (![X36 : $i, X37 : $i, X38 : $i]:
% 2.69/2.90         (((X36) != (k1_relset_1 @ X36 @ X37 @ X38))
% 2.69/2.90          | (v1_funct_2 @ X38 @ X36 @ X37)
% 2.69/2.90          | ~ (zip_tseitin_1 @ X38 @ X37 @ X36))),
% 2.69/2.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.69/2.90  thf('35', plain,
% 2.69/2.90      (![X0 : $i, X1 : $i]:
% 2.69/2.90         (((X1) != (k1_xboole_0))
% 2.69/2.90          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 2.69/2.90          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 2.69/2.90      inference('sup-', [status(thm)], ['33', '34'])).
% 2.69/2.90  thf('36', plain,
% 2.69/2.90      (![X0 : $i]:
% 2.69/2.90         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 2.69/2.90          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 2.69/2.90      inference('simplify', [status(thm)], ['35'])).
% 2.69/2.90  thf(zf_stmt_1, axiom,
% 2.69/2.90    (![B:$i,A:$i]:
% 2.69/2.90     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.69/2.90       ( zip_tseitin_0 @ B @ A ) ))).
% 2.69/2.90  thf('37', plain,
% 2.69/2.90      (![X34 : $i, X35 : $i]:
% 2.69/2.90         ((zip_tseitin_0 @ X34 @ X35) | ((X35) != (k1_xboole_0)))),
% 2.69/2.90      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.69/2.90  thf('38', plain, (![X34 : $i]: (zip_tseitin_0 @ X34 @ k1_xboole_0)),
% 2.69/2.90      inference('simplify', [status(thm)], ['37'])).
% 2.69/2.90  thf('39', plain,
% 2.69/2.90      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 2.69/2.90      inference('demod', [status(thm)], ['14', '26'])).
% 2.69/2.90  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.69/2.90  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 2.69/2.90  thf(zf_stmt_4, axiom,
% 2.69/2.90    (![A:$i,B:$i,C:$i]:
% 2.69/2.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.69/2.90       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.69/2.90         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.69/2.90           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.69/2.90             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.69/2.90  thf('40', plain,
% 2.69/2.90      (![X39 : $i, X40 : $i, X41 : $i]:
% 2.69/2.90         (~ (zip_tseitin_0 @ X39 @ X40)
% 2.69/2.90          | (zip_tseitin_1 @ X41 @ X39 @ X40)
% 2.69/2.90          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39))))),
% 2.69/2.90      inference('cnf', [status(esa)], [zf_stmt_4])).
% 2.69/2.90  thf('41', plain,
% 2.69/2.90      (![X0 : $i, X1 : $i]:
% 2.69/2.90         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 2.69/2.90      inference('sup-', [status(thm)], ['39', '40'])).
% 2.69/2.90  thf('42', plain,
% 2.69/2.90      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 2.69/2.90      inference('sup-', [status(thm)], ['38', '41'])).
% 2.69/2.90  thf('43', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 2.69/2.90      inference('demod', [status(thm)], ['36', '42'])).
% 2.69/2.90  thf('44', plain,
% 2.69/2.90      (![X0 : $i, X1 : $i]:
% 2.69/2.90         ((v1_funct_2 @ X0 @ k1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 2.69/2.90      inference('sup+', [status(thm)], ['8', '43'])).
% 2.69/2.90  thf('45', plain,
% 2.69/2.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.69/2.90         ((v1_funct_2 @ X2 @ X0 @ X1)
% 2.69/2.90          | ~ (v1_xboole_0 @ X0)
% 2.69/2.90          | ~ (v1_xboole_0 @ X2))),
% 2.69/2.90      inference('sup+', [status(thm)], ['7', '44'])).
% 2.69/2.90  thf(t8_funct_2, conjecture,
% 2.69/2.90    (![A:$i,B:$i,C:$i,D:$i]:
% 2.69/2.90     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.69/2.90         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.69/2.90       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 2.69/2.90         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 2.69/2.90           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 2.69/2.90             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 2.69/2.90  thf(zf_stmt_5, negated_conjecture,
% 2.69/2.90    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 2.69/2.90        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.69/2.90            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.69/2.90          ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 2.69/2.90            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 2.69/2.90              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 2.69/2.90                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 2.69/2.90    inference('cnf.neg', [status(esa)], [t8_funct_2])).
% 2.69/2.90  thf('46', plain,
% 2.69/2.90      ((~ (v1_funct_1 @ sk_D)
% 2.69/2.90        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 2.69/2.90        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 2.69/2.90      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.69/2.90  thf('47', plain,
% 2.69/2.90      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 2.69/2.90         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 2.69/2.90      inference('split', [status(esa)], ['46'])).
% 2.69/2.90  thf('48', plain,
% 2.69/2.90      (((~ (v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_A)))
% 2.69/2.90         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 2.69/2.90      inference('sup-', [status(thm)], ['45', '47'])).
% 2.69/2.90  thf('49', plain,
% 2.69/2.90      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 2.69/2.90      inference('simplify', [status(thm)], ['9'])).
% 2.69/2.90  thf('50', plain,
% 2.69/2.90      (![X34 : $i, X35 : $i]:
% 2.69/2.90         ((zip_tseitin_0 @ X34 @ X35) | ((X34) = (k1_xboole_0)))),
% 2.69/2.90      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.69/2.90  thf('51', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.69/2.90      inference('sup-', [status(thm)], ['15', '23'])).
% 2.69/2.90  thf('52', plain,
% 2.69/2.90      (![X0 : $i, X1 : $i]:
% 2.69/2.90         (((k6_relat_1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X1))),
% 2.69/2.90      inference('sup+', [status(thm)], ['50', '51'])).
% 2.69/2.90  thf('53', plain,
% 2.69/2.90      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.69/2.90      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.69/2.90  thf('54', plain,
% 2.69/2.90      (![X39 : $i, X40 : $i, X41 : $i]:
% 2.69/2.90         (~ (zip_tseitin_0 @ X39 @ X40)
% 2.69/2.90          | (zip_tseitin_1 @ X41 @ X39 @ X40)
% 2.69/2.90          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39))))),
% 2.69/2.90      inference('cnf', [status(esa)], [zf_stmt_4])).
% 2.69/2.90  thf('55', plain,
% 2.69/2.90      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 2.69/2.90        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 2.69/2.90      inference('sup-', [status(thm)], ['53', '54'])).
% 2.69/2.90  thf('56', plain,
% 2.69/2.90      ((((k6_relat_1 @ sk_B_1) = (k1_xboole_0))
% 2.69/2.90        | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 2.69/2.90      inference('sup-', [status(thm)], ['52', '55'])).
% 2.69/2.90  thf('57', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 2.69/2.90      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.69/2.90  thf('58', plain,
% 2.69/2.90      (![X36 : $i, X37 : $i, X38 : $i]:
% 2.69/2.90         (~ (v1_funct_2 @ X38 @ X36 @ X37)
% 2.69/2.90          | ((X36) = (k1_relset_1 @ X36 @ X37 @ X38))
% 2.69/2.90          | ~ (zip_tseitin_1 @ X38 @ X37 @ X36))),
% 2.69/2.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.69/2.90  thf('59', plain,
% 2.69/2.90      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 2.69/2.90        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 2.69/2.90      inference('sup-', [status(thm)], ['57', '58'])).
% 2.69/2.90  thf('60', plain,
% 2.69/2.90      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.69/2.90      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.69/2.90  thf('61', plain,
% 2.69/2.90      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.69/2.90         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 2.69/2.90          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 2.69/2.90      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.69/2.90  thf('62', plain,
% 2.69/2.90      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 2.69/2.90      inference('sup-', [status(thm)], ['60', '61'])).
% 2.69/2.90  thf('63', plain,
% 2.69/2.90      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 2.69/2.90        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.69/2.90      inference('demod', [status(thm)], ['59', '62'])).
% 2.69/2.90  thf('64', plain,
% 2.69/2.90      ((((k6_relat_1 @ sk_B_1) = (k1_xboole_0))
% 2.69/2.90        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.69/2.90      inference('sup-', [status(thm)], ['56', '63'])).
% 2.69/2.90  thf('65', plain, (![X18 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 2.69/2.90      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.69/2.90  thf('66', plain,
% 2.69/2.90      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.69/2.90      inference('sup-', [status(thm)], ['0', '6'])).
% 2.69/2.90  thf('67', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.69/2.90      inference('sup+', [status(thm)], ['30', '31'])).
% 2.69/2.90  thf('68', plain,
% 2.69/2.90      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.69/2.90      inference('sup+', [status(thm)], ['66', '67'])).
% 2.69/2.90  thf('69', plain, (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)),
% 2.69/2.90      inference('sup+', [status(thm)], ['10', '11'])).
% 2.69/2.90  thf('70', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.69/2.90      inference('sup+', [status(thm)], ['24', '25'])).
% 2.69/2.90  thf('71', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 2.69/2.90      inference('demod', [status(thm)], ['69', '70'])).
% 2.69/2.90  thf('72', plain,
% 2.69/2.90      (![X0 : $i, X1 : $i]:
% 2.69/2.90         ((r1_tarski @ (k1_relat_1 @ X0) @ X1) | ~ (v1_xboole_0 @ X0))),
% 2.69/2.90      inference('sup+', [status(thm)], ['68', '71'])).
% 2.69/2.90  thf('73', plain,
% 2.69/2.90      (![X0 : $i, X1 : $i]:
% 2.69/2.90         ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ (k6_relat_1 @ X0)))),
% 2.69/2.90      inference('sup+', [status(thm)], ['65', '72'])).
% 2.69/2.90  thf('74', plain,
% 2.69/2.90      (![X0 : $i]:
% 2.69/2.90         (~ (v1_xboole_0 @ k1_xboole_0)
% 2.69/2.90          | ((sk_A) = (k1_relat_1 @ sk_D))
% 2.69/2.90          | (r1_tarski @ sk_B_1 @ X0))),
% 2.69/2.90      inference('sup-', [status(thm)], ['64', '73'])).
% 2.69/2.90  thf('75', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.69/2.90      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.69/2.90  thf('76', plain,
% 2.69/2.90      (![X0 : $i]: (((sk_A) = (k1_relat_1 @ sk_D)) | (r1_tarski @ sk_B_1 @ X0))),
% 2.69/2.90      inference('demod', [status(thm)], ['74', '75'])).
% 2.69/2.90  thf('77', plain,
% 2.69/2.90      (![X16 : $i, X17 : $i]:
% 2.69/2.90         (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X16 @ X17)) @ X17)),
% 2.69/2.90      inference('cnf', [status(esa)], [t194_relat_1])).
% 2.69/2.90  thf('78', plain,
% 2.69/2.90      (![X0 : $i, X2 : $i]:
% 2.69/2.90         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.69/2.90      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.69/2.90  thf('79', plain,
% 2.69/2.90      (![X0 : $i, X1 : $i]:
% 2.69/2.90         (~ (r1_tarski @ X0 @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 2.69/2.90          | ((X0) = (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 2.69/2.90      inference('sup-', [status(thm)], ['77', '78'])).
% 2.69/2.90  thf('80', plain,
% 2.69/2.90      (![X0 : $i]:
% 2.69/2.90         (((sk_A) = (k1_relat_1 @ sk_D))
% 2.69/2.90          | ((sk_B_1) = (k2_relat_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1))))),
% 2.69/2.90      inference('sup-', [status(thm)], ['76', '79'])).
% 2.69/2.90  thf('81', plain,
% 2.69/2.90      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.69/2.90      inference('sup-', [status(thm)], ['0', '6'])).
% 2.69/2.90  thf('82', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.69/2.90      inference('sup+', [status(thm)], ['24', '25'])).
% 2.69/2.90  thf('83', plain,
% 2.69/2.90      (![X0 : $i]: (((k2_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.69/2.90      inference('sup+', [status(thm)], ['81', '82'])).
% 2.69/2.90  thf('84', plain,
% 2.69/2.90      (![X0 : $i]:
% 2.69/2.90         (((sk_B_1) = (k1_xboole_0))
% 2.69/2.90          | ((sk_A) = (k1_relat_1 @ sk_D))
% 2.69/2.90          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))),
% 2.69/2.90      inference('sup+', [status(thm)], ['80', '83'])).
% 2.69/2.90  thf('85', plain, ((((sk_B_1) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 2.69/2.90      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.69/2.90  thf('86', plain,
% 2.69/2.90      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 2.69/2.90      inference('split', [status(esa)], ['85'])).
% 2.69/2.90  thf('87', plain, ((v1_funct_1 @ sk_D)),
% 2.69/2.90      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.69/2.90  thf('88', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 2.69/2.90      inference('split', [status(esa)], ['46'])).
% 2.69/2.90  thf('89', plain, (((v1_funct_1 @ sk_D))),
% 2.69/2.90      inference('sup-', [status(thm)], ['87', '88'])).
% 2.69/2.90  thf('90', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 2.69/2.90      inference('demod', [status(thm)], ['36', '42'])).
% 2.69/2.90  thf('91', plain,
% 2.69/2.90      (![X30 : $i]:
% 2.69/2.90         (((X30) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X30) @ X30))),
% 2.69/2.90      inference('cnf', [status(esa)], [t29_mcart_1])).
% 2.69/2.90  thf('92', plain,
% 2.69/2.90      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.69/2.90      inference('split', [status(esa)], ['85'])).
% 2.69/2.90  thf('93', plain,
% 2.69/2.90      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.69/2.90      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.69/2.90  thf('94', plain,
% 2.69/2.90      (((m1_subset_1 @ sk_D @ 
% 2.69/2.90         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 2.69/2.90         <= ((((sk_A) = (k1_xboole_0))))),
% 2.69/2.90      inference('sup+', [status(thm)], ['92', '93'])).
% 2.69/2.90  thf('95', plain,
% 2.69/2.90      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.69/2.90         (~ (r2_hidden @ X9 @ X10)
% 2.69/2.90          | ~ (v1_xboole_0 @ X11)
% 2.69/2.90          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 2.69/2.90      inference('cnf', [status(esa)], [t5_subset])).
% 2.69/2.90  thf('96', plain,
% 2.69/2.90      ((![X0 : $i]:
% 2.69/2.90          (~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))
% 2.69/2.90           | ~ (r2_hidden @ X0 @ sk_D)))
% 2.69/2.90         <= ((((sk_A) = (k1_xboole_0))))),
% 2.69/2.90      inference('sup-', [status(thm)], ['94', '95'])).
% 2.69/2.90  thf('97', plain,
% 2.69/2.90      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 2.69/2.90      inference('simplify', [status(thm)], ['9'])).
% 2.69/2.90  thf('98', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.69/2.90      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.69/2.90  thf('99', plain,
% 2.69/2.90      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_D)) <= ((((sk_A) = (k1_xboole_0))))),
% 2.69/2.90      inference('demod', [status(thm)], ['96', '97', '98'])).
% 2.69/2.90  thf('100', plain,
% 2.69/2.90      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.69/2.90      inference('sup-', [status(thm)], ['91', '99'])).
% 2.69/2.90  thf('101', plain,
% 2.69/2.90      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.69/2.90      inference('split', [status(esa)], ['85'])).
% 2.69/2.90  thf('102', plain,
% 2.69/2.90      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 2.69/2.90         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 2.69/2.90      inference('split', [status(esa)], ['46'])).
% 2.69/2.90  thf('103', plain,
% 2.69/2.90      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C))
% 2.69/2.90         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 2.69/2.90      inference('sup-', [status(thm)], ['101', '102'])).
% 2.69/2.90  thf('104', plain,
% 2.69/2.90      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C))
% 2.69/2.90         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 2.69/2.90      inference('sup-', [status(thm)], ['100', '103'])).
% 2.69/2.90  thf('105', plain,
% 2.69/2.90      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ (((sk_A) = (k1_xboole_0)))),
% 2.69/2.90      inference('sup-', [status(thm)], ['90', '104'])).
% 2.69/2.90  thf('106', plain,
% 2.69/2.90      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 2.69/2.90      inference('simplify', [status(thm)], ['9'])).
% 2.69/2.90  thf('107', plain,
% 2.69/2.90      (((m1_subset_1 @ sk_D @ 
% 2.69/2.90         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 2.69/2.90         <= ((((sk_A) = (k1_xboole_0))))),
% 2.69/2.90      inference('sup+', [status(thm)], ['92', '93'])).
% 2.69/2.90  thf('108', plain,
% 2.69/2.90      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 2.69/2.90         <= ((((sk_A) = (k1_xboole_0))))),
% 2.69/2.90      inference('sup+', [status(thm)], ['106', '107'])).
% 2.69/2.90  thf('109', plain,
% 2.69/2.90      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 2.69/2.90      inference('simplify', [status(thm)], ['9'])).
% 2.69/2.90  thf('110', plain,
% 2.69/2.90      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 2.69/2.90      inference('split', [status(esa)], ['85'])).
% 2.69/2.90  thf('111', plain,
% 2.69/2.90      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 2.69/2.90         <= (~
% 2.69/2.90             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 2.69/2.90      inference('split', [status(esa)], ['46'])).
% 2.69/2.90  thf('112', plain,
% 2.69/2.90      ((~ (m1_subset_1 @ sk_D @ 
% 2.69/2.90           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 2.69/2.90         <= (~
% 2.69/2.90             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 2.69/2.90             (((sk_A) = (k1_xboole_0))))),
% 2.69/2.90      inference('sup-', [status(thm)], ['110', '111'])).
% 2.69/2.90  thf('113', plain,
% 2.69/2.90      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 2.69/2.90         <= (~
% 2.69/2.90             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 2.69/2.90             (((sk_A) = (k1_xboole_0))))),
% 2.69/2.90      inference('sup-', [status(thm)], ['109', '112'])).
% 2.69/2.90  thf('114', plain,
% 2.69/2.90      (~ (((sk_A) = (k1_xboole_0))) | 
% 2.69/2.90       ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 2.69/2.90      inference('sup-', [status(thm)], ['108', '113'])).
% 2.69/2.90  thf('115', plain,
% 2.69/2.90      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 2.69/2.90       ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ ((v1_funct_1 @ sk_D))),
% 2.69/2.90      inference('split', [status(esa)], ['46'])).
% 2.69/2.90  thf('116', plain,
% 2.69/2.90      (~ (((sk_B_1) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 2.69/2.90      inference('split', [status(esa)], ['85'])).
% 2.69/2.90  thf('117', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 2.69/2.90      inference('sat_resolution*', [status(thm)],
% 2.69/2.90                ['89', '105', '114', '115', '116'])).
% 2.69/2.90  thf('118', plain, (((sk_B_1) != (k1_xboole_0))),
% 2.69/2.90      inference('simpl_trail', [status(thm)], ['86', '117'])).
% 2.69/2.90  thf('119', plain,
% 2.69/2.90      (![X0 : $i]:
% 2.69/2.90         (((sk_A) = (k1_relat_1 @ sk_D))
% 2.69/2.90          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))),
% 2.69/2.90      inference('simplify_reflect-', [status(thm)], ['84', '118'])).
% 2.69/2.90  thf('120', plain,
% 2.69/2.90      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.69/2.90      inference('sup-', [status(thm)], ['49', '119'])).
% 2.69/2.90  thf('121', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.69/2.90      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.69/2.90  thf('122', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 2.69/2.90      inference('demod', [status(thm)], ['120', '121'])).
% 2.69/2.90  thf('123', plain,
% 2.69/2.90      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.69/2.90      inference('sup+', [status(thm)], ['66', '67'])).
% 2.69/2.90  thf('124', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.69/2.90      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.69/2.90  thf('125', plain,
% 2.69/2.90      (![X0 : $i]: ((v1_xboole_0 @ (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 2.69/2.90      inference('sup+', [status(thm)], ['123', '124'])).
% 2.69/2.90  thf('126', plain, (((v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ sk_D))),
% 2.69/2.90      inference('sup+', [status(thm)], ['122', '125'])).
% 2.69/2.90  thf('127', plain,
% 2.69/2.90      ((~ (v1_xboole_0 @ sk_D)) <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 2.69/2.90      inference('clc', [status(thm)], ['48', '126'])).
% 2.69/2.90  thf('128', plain,
% 2.69/2.90      ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) @ sk_C)),
% 2.69/2.90      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.69/2.90  thf('129', plain,
% 2.69/2.90      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.69/2.90      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.69/2.90  thf(redefinition_k2_relset_1, axiom,
% 2.69/2.90    (![A:$i,B:$i,C:$i]:
% 2.69/2.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.69/2.90       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.69/2.90  thf('130', plain,
% 2.69/2.90      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.69/2.90         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 2.69/2.90          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 2.69/2.90      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.69/2.90  thf('131', plain,
% 2.69/2.90      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.69/2.90      inference('sup-', [status(thm)], ['129', '130'])).
% 2.69/2.90  thf('132', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 2.69/2.90      inference('demod', [status(thm)], ['128', '131'])).
% 2.69/2.90  thf('133', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.69/2.90      inference('simplify', [status(thm)], ['1'])).
% 2.69/2.90  thf(t11_relset_1, axiom,
% 2.69/2.90    (![A:$i,B:$i,C:$i]:
% 2.69/2.90     ( ( v1_relat_1 @ C ) =>
% 2.69/2.90       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 2.69/2.90           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 2.69/2.90         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 2.69/2.90  thf('134', plain,
% 2.69/2.90      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.69/2.90         (~ (r1_tarski @ (k1_relat_1 @ X26) @ X27)
% 2.69/2.90          | ~ (r1_tarski @ (k2_relat_1 @ X26) @ X28)
% 2.69/2.90          | (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 2.69/2.90          | ~ (v1_relat_1 @ X26))),
% 2.69/2.90      inference('cnf', [status(esa)], [t11_relset_1])).
% 2.69/2.90  thf('135', plain,
% 2.69/2.90      (![X0 : $i, X1 : $i]:
% 2.69/2.90         (~ (v1_relat_1 @ X0)
% 2.69/2.90          | (m1_subset_1 @ X0 @ 
% 2.69/2.90             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 2.69/2.90          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 2.69/2.90      inference('sup-', [status(thm)], ['133', '134'])).
% 2.69/2.90  thf('136', plain,
% 2.69/2.90      (((m1_subset_1 @ sk_D @ 
% 2.69/2.90         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C)))
% 2.69/2.90        | ~ (v1_relat_1 @ sk_D))),
% 2.69/2.90      inference('sup-', [status(thm)], ['132', '135'])).
% 2.69/2.90  thf('137', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 2.69/2.90      inference('demod', [status(thm)], ['120', '121'])).
% 2.69/2.90  thf('138', plain,
% 2.69/2.90      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.69/2.90      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.69/2.90  thf(cc2_relat_1, axiom,
% 2.69/2.90    (![A:$i]:
% 2.69/2.90     ( ( v1_relat_1 @ A ) =>
% 2.69/2.90       ( ![B:$i]:
% 2.69/2.90         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.69/2.90  thf('139', plain,
% 2.69/2.90      (![X12 : $i, X13 : $i]:
% 2.69/2.90         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 2.69/2.90          | (v1_relat_1 @ X12)
% 2.69/2.90          | ~ (v1_relat_1 @ X13))),
% 2.69/2.90      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.69/2.90  thf('140', plain,
% 2.69/2.90      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D))),
% 2.69/2.90      inference('sup-', [status(thm)], ['138', '139'])).
% 2.69/2.90  thf(fc6_relat_1, axiom,
% 2.69/2.90    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.69/2.90  thf('141', plain,
% 2.69/2.90      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X14 @ X15))),
% 2.69/2.90      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.69/2.90  thf('142', plain, ((v1_relat_1 @ sk_D)),
% 2.69/2.90      inference('demod', [status(thm)], ['140', '141'])).
% 2.69/2.90  thf('143', plain,
% 2.69/2.90      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 2.69/2.90      inference('demod', [status(thm)], ['136', '137', '142'])).
% 2.69/2.90  thf('144', plain,
% 2.69/2.90      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 2.69/2.90         <= (~
% 2.69/2.90             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 2.69/2.90      inference('split', [status(esa)], ['46'])).
% 2.69/2.90  thf('145', plain,
% 2.69/2.90      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 2.69/2.90      inference('sup-', [status(thm)], ['143', '144'])).
% 2.69/2.90  thf('146', plain,
% 2.69/2.90      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | 
% 2.69/2.90       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 2.69/2.90       ~ ((v1_funct_1 @ sk_D))),
% 2.69/2.90      inference('split', [status(esa)], ['46'])).
% 2.69/2.90  thf('147', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 2.69/2.90      inference('sat_resolution*', [status(thm)], ['89', '145', '146'])).
% 2.69/2.90  thf('148', plain, (~ (v1_xboole_0 @ sk_D)),
% 2.69/2.90      inference('simpl_trail', [status(thm)], ['127', '147'])).
% 2.69/2.90  thf('149', plain,
% 2.69/2.90      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 2.69/2.90      inference('demod', [status(thm)], ['136', '137', '142'])).
% 2.69/2.90  thf('150', plain,
% 2.69/2.90      (![X6 : $i, X7 : $i]:
% 2.69/2.90         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 2.69/2.90      inference('cnf', [status(esa)], [t3_subset])).
% 2.69/2.90  thf('151', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_C))),
% 2.69/2.90      inference('sup-', [status(thm)], ['149', '150'])).
% 2.69/2.90  thf('152', plain,
% 2.69/2.90      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.69/2.90      inference('sup-', [status(thm)], ['0', '6'])).
% 2.69/2.90  thf('153', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 2.69/2.90      inference('demod', [status(thm)], ['69', '70'])).
% 2.69/2.90  thf('154', plain,
% 2.69/2.90      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 2.69/2.90      inference('sup+', [status(thm)], ['152', '153'])).
% 2.69/2.90  thf('155', plain,
% 2.69/2.90      (![X0 : $i, X2 : $i]:
% 2.69/2.90         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.69/2.90      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.69/2.90  thf('156', plain,
% 2.69/2.90      (![X0 : $i, X1 : $i]:
% 2.69/2.90         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 2.69/2.90      inference('sup-', [status(thm)], ['154', '155'])).
% 2.69/2.90  thf('157', plain,
% 2.69/2.90      ((((sk_D) = (k2_zfmisc_1 @ sk_A @ sk_C))
% 2.69/2.90        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 2.69/2.90      inference('sup-', [status(thm)], ['151', '156'])).
% 2.69/2.90  thf('158', plain,
% 2.69/2.90      (![X34 : $i, X35 : $i]:
% 2.69/2.90         ((zip_tseitin_0 @ X34 @ X35) | ((X34) = (k1_xboole_0)))),
% 2.69/2.90      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.69/2.90  thf('159', plain,
% 2.69/2.90      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 2.69/2.90      inference('demod', [status(thm)], ['136', '137', '142'])).
% 2.69/2.90  thf('160', plain,
% 2.69/2.90      (![X39 : $i, X40 : $i, X41 : $i]:
% 2.69/2.90         (~ (zip_tseitin_0 @ X39 @ X40)
% 2.69/2.90          | (zip_tseitin_1 @ X41 @ X39 @ X40)
% 2.69/2.90          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39))))),
% 2.69/2.90      inference('cnf', [status(esa)], [zf_stmt_4])).
% 2.69/2.90  thf('161', plain,
% 2.69/2.90      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_A) | ~ (zip_tseitin_0 @ sk_C @ sk_A))),
% 2.69/2.90      inference('sup-', [status(thm)], ['159', '160'])).
% 2.69/2.90  thf('162', plain,
% 2.69/2.90      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 2.69/2.90      inference('demod', [status(thm)], ['136', '137', '142'])).
% 2.69/2.90  thf('163', plain,
% 2.69/2.90      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.69/2.90         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 2.69/2.90          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 2.69/2.90      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.69/2.90  thf('164', plain,
% 2.69/2.90      (((k1_relset_1 @ sk_A @ sk_C @ sk_D) = (k1_relat_1 @ sk_D))),
% 2.69/2.90      inference('sup-', [status(thm)], ['162', '163'])).
% 2.69/2.90  thf('165', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 2.69/2.90      inference('demod', [status(thm)], ['120', '121'])).
% 2.69/2.90  thf('166', plain, (((k1_relset_1 @ sk_A @ sk_C @ sk_D) = (sk_A))),
% 2.69/2.90      inference('demod', [status(thm)], ['164', '165'])).
% 2.69/2.90  thf('167', plain,
% 2.69/2.90      (![X36 : $i, X37 : $i, X38 : $i]:
% 2.69/2.90         (((X36) != (k1_relset_1 @ X36 @ X37 @ X38))
% 2.69/2.90          | (v1_funct_2 @ X38 @ X36 @ X37)
% 2.69/2.90          | ~ (zip_tseitin_1 @ X38 @ X37 @ X36))),
% 2.69/2.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.69/2.90  thf('168', plain,
% 2.69/2.90      ((((sk_A) != (sk_A))
% 2.69/2.90        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)
% 2.69/2.90        | (v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 2.69/2.90      inference('sup-', [status(thm)], ['166', '167'])).
% 2.69/2.90  thf('169', plain,
% 2.69/2.90      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 2.69/2.90        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A))),
% 2.69/2.90      inference('simplify', [status(thm)], ['168'])).
% 2.69/2.90  thf('170', plain,
% 2.69/2.90      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 2.69/2.90         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 2.69/2.90      inference('split', [status(esa)], ['46'])).
% 2.69/2.90  thf('171', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 2.69/2.90      inference('sat_resolution*', [status(thm)], ['89', '145', '146'])).
% 2.69/2.90  thf('172', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 2.69/2.90      inference('simpl_trail', [status(thm)], ['170', '171'])).
% 2.69/2.90  thf('173', plain, (~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)),
% 2.69/2.90      inference('clc', [status(thm)], ['169', '172'])).
% 2.69/2.90  thf('174', plain, (~ (zip_tseitin_0 @ sk_C @ sk_A)),
% 2.69/2.90      inference('clc', [status(thm)], ['161', '173'])).
% 2.69/2.90  thf('175', plain, (((sk_C) = (k1_xboole_0))),
% 2.69/2.90      inference('sup-', [status(thm)], ['158', '174'])).
% 2.69/2.90  thf('176', plain,
% 2.69/2.90      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 2.69/2.90      inference('simplify', [status(thm)], ['16'])).
% 2.69/2.90  thf('177', plain, (((sk_C) = (k1_xboole_0))),
% 2.69/2.90      inference('sup-', [status(thm)], ['158', '174'])).
% 2.69/2.90  thf('178', plain,
% 2.69/2.90      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 2.69/2.90      inference('simplify', [status(thm)], ['16'])).
% 2.69/2.90  thf('179', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.69/2.90      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.69/2.90  thf('180', plain, (((sk_D) = (k1_xboole_0))),
% 2.69/2.90      inference('demod', [status(thm)],
% 2.69/2.90                ['157', '175', '176', '177', '178', '179'])).
% 2.69/2.90  thf('181', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.69/2.90      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.69/2.90  thf('182', plain, ($false),
% 2.69/2.90      inference('demod', [status(thm)], ['148', '180', '181'])).
% 2.69/2.90  
% 2.69/2.90  % SZS output end Refutation
% 2.69/2.90  
% 2.69/2.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
