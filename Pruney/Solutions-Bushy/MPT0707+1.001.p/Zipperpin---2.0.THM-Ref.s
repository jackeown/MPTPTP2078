%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0707+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bg1MuaXZeJ

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:21 EST 2020

% Result     : Theorem 4.71s
% Output     : Refutation 4.71s
% Verified   : 
% Statistics : Number of formulae       :  280 (398191 expanded)
%              Number of leaves         :   26 (127357 expanded)
%              Depth                    :   74
%              Number of atoms          : 4501 (6129895 expanded)
%              Number of equality atoms :  253 (331084 expanded)
%              Maximal formula depth    :   19 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(d12_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_funct_1 @ A )
        & ( v1_relat_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) )
                  & ( r2_hidden @ E @ B )
                  & ( D
                    = ( k1_funct_1 @ A @ E ) ) ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( D
          = ( k1_funct_1 @ A @ E ) )
        & ( r2_hidden @ E @ B )
        & ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ) )).

thf(zf_stmt_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ ( sk_D @ X5 @ X6 @ X7 ) @ X5 )
      | ( zip_tseitin_0 @ ( sk_E @ X5 @ X6 @ X7 ) @ ( sk_D @ X5 @ X6 @ X7 ) @ X6 @ X7 )
      | ( X5
        = ( k9_relat_1 @ X7 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X2
        = ( k1_funct_1 @ X0 @ X1 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X2
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( ( sk_D @ X2 @ X1 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_E @ X2 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t34_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( B
          = ( k6_relat_1 @ A ) )
      <=> ( ( ( k1_relat_1 @ B )
            = A )
          & ! [C: $i] :
              ( ( r2_hidden @ C @ A )
             => ( ( k1_funct_1 @ B @ C )
                = C ) ) ) ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X18
       != ( k6_relat_1 @ X17 ) )
      | ( ( k1_relat_1 @ X18 )
        = X17 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('4',plain,(
    ! [X17: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X17 ) )
      | ( ( k1_relat_1 @ ( k6_relat_1 @ X17 ) )
        = X17 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('6',plain,(
    ! [X14: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('7',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ ( sk_D @ X5 @ X6 @ X7 ) @ X5 )
      | ( zip_tseitin_0 @ ( sk_E @ X5 @ X6 @ X7 ) @ ( sk_D @ X5 @ X6 @ X7 ) @ X6 @ X7 )
      | ( X5
        = ( k9_relat_1 @ X7 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X2
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_E @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ( X2
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X14: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('13',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_E @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ( X2
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X2
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('16',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('17',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X4 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X4 ) )
      | ~ ( r2_hidden @ X1 @ X3 )
      | ( X2
       != ( k1_funct_1 @ X4 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('18',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X1 @ X3 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X4 ) )
      | ( zip_tseitin_0 @ X1 @ ( k1_funct_1 @ X4 @ X1 ) @ X3 @ X4 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( zip_tseitin_0 @ X1 @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X2 @ ( k6_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X3 )
      | ( zip_tseitin_0 @ ( sk_E @ X2 @ X1 @ X0 ) @ ( k1_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( sk_E @ X2 @ X1 @ X0 ) ) @ X3 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ( zip_tseitin_0 @ ( sk_E @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k1_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) @ ( sk_E @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( X2
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('23',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('24',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('25',plain,(
    ! [X14: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ( zip_tseitin_0 @ ( sk_E @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ ( sk_E @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 @ ( k6_relat_1 @ X0 ) )
      | ( X2
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ ( sk_E @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ ( sk_E @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 @ ( k6_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ( X2
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X6: $i,X7: $i,X9: $i,X11: $i,X12: $i] :
      ( ( X9
       != ( k9_relat_1 @ X7 @ X6 ) )
      | ( r2_hidden @ X11 @ X9 )
      | ~ ( zip_tseitin_0 @ X12 @ X11 @ X6 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('29',plain,(
    ! [X6: $i,X7: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( zip_tseitin_0 @ X12 @ X11 @ X6 @ X7 )
      | ( r2_hidden @ X11 @ ( k9_relat_1 @ X7 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ ( sk_E @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X2
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( ( sk_D @ X2 @ X1 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_E @ X2 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('32',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ ( sk_D @ X5 @ X6 @ X7 ) @ X5 )
      | ( zip_tseitin_0 @ ( sk_E @ X5 @ X6 @ X7 ) @ ( sk_D @ X5 @ X6 @ X7 ) @ X6 @ X7 )
      | ( X5
        = ( k9_relat_1 @ X7 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X1 @ X3 )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X2
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( X18
       != ( k6_relat_1 @ X17 ) )
      | ( ( k1_funct_1 @ X18 @ X19 )
        = X19 )
      | ~ ( r2_hidden @ X19 @ X17 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('36',plain,(
    ! [X17: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X17 ) )
      | ~ ( r2_hidden @ X19 @ X17 )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ X17 ) @ X19 )
        = X19 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('38',plain,(
    ! [X14: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('39',plain,(
    ! [X17: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X17 )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ X17 ) @ X19 )
        = X19 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ X2 @ X1 ) @ X2 )
      | ( X0
        = ( k9_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ ( sk_D @ X0 @ X2 @ X1 ) )
        = ( sk_D @ X0 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X2
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X2
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( zip_tseitin_0 @ X1 @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X2 @ ( k6_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ X2 @ X1 ) @ X2 )
      | ( X0
        = ( k9_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X3 )
      | ( zip_tseitin_0 @ ( sk_D @ X0 @ X2 @ X1 ) @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ ( sk_D @ X0 @ X2 @ X1 ) ) @ X3 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ X2 @ X1 ) @ X2 )
      | ( X0
        = ( k9_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( zip_tseitin_0 @ ( sk_D @ X0 @ X2 @ X1 ) @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ ( sk_D @ X0 @ X2 @ X1 ) ) @ X0 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X0
        = ( k9_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_E @ X0 @ X2 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ ( sk_D @ X0 @ X2 @ X1 ) @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ ( sk_D @ X0 @ X2 @ X1 ) ) @ X0 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X0
        = ( k9_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_E @ X0 @ X2 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ ( sk_D @ X2 @ X1 @ X0 ) @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 @ ( k6_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X2
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X1 )
      | ( X2
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X1 )
      | ( X2
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_0 @ ( sk_D @ X2 @ X1 @ X0 ) @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 @ ( k6_relat_1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X2
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('50',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X5 @ X6 @ X7 ) @ X5 )
      | ~ ( zip_tseitin_0 @ X8 @ ( sk_D @ X5 @ X6 @ X7 ) @ X6 @ X7 )
      | ( X5
        = ( k9_relat_1 @ X7 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ X2 @ X1 ) @ X2 )
      | ( X0
        = ( k9_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X0
        = ( k9_relat_1 @ X1 @ X2 ) )
      | ~ ( zip_tseitin_0 @ X3 @ ( sk_D @ X0 @ X2 @ X1 ) @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( zip_tseitin_0 @ X3 @ ( sk_D @ X0 @ X2 @ X1 ) @ X2 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X0
        = ( k9_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_E @ X0 @ X2 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ( r2_hidden @ ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( r2_hidden @ ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','52'])).

thf('54',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('55',plain,(
    ! [X14: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('56',plain,(
    ! [X14: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('57',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ( r2_hidden @ ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( r2_hidden @ ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['53','54','55','56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X17: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X17 )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ X17 ) @ X19 )
        = X19 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) )
        = ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( zip_tseitin_0 @ X1 @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X2 @ ( k6_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ~ ( r2_hidden @ ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X1 )
      | ( zip_tseitin_0 @ ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) ) @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) ) @ X0 @ ( k6_relat_1 @ X0 ) )
      | ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) ) @ X0 @ ( k6_relat_1 @ X0 ) )
      | ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X6: $i,X7: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( zip_tseitin_0 @ X12 @ X11 @ X6 @ X7 )
      | ( r2_hidden @ X11 @ ( k9_relat_1 @ X7 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) ) @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X14: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('71',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) ) @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['61','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ( r2_hidden @ ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X6: $i,X7: $i,X9: $i,X10: $i] :
      ( ( X9
       != ( k9_relat_1 @ X7 @ X6 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X10 @ X6 @ X7 ) @ X10 @ X6 @ X7 )
      | ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('76',plain,(
    ! [X6: $i,X7: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k9_relat_1 @ X7 @ X6 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X10 @ X6 @ X7 ) @ X10 @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 @ ( k6_relat_1 @ X0 ) ) @ ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['74','76'])).

thf('78',plain,(
    ! [X14: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('79',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 @ ( k6_relat_1 @ X0 ) ) @ ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X2
        = ( k1_funct_1 @ X0 @ X1 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ( ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) )
        = ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ ( sk_E_1 @ ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 @ ( k6_relat_1 @ X0 ) ) @ ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X1 @ X3 )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X17: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X17 )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ X17 ) @ X19 )
        = X19 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ ( sk_E_1 @ ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 @ ( k6_relat_1 @ X0 ) ) )
        = ( sk_E_1 @ ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) )
        = ( sk_E_1 @ ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 @ ( k6_relat_1 @ X0 ) ) )
      | ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['82','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ( ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) )
        = ( sk_E_1 @ ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ ( sk_E_1 @ ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 @ ( k6_relat_1 @ X0 ) ) )
        = ( sk_E_1 @ ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) )
        = ( sk_E_1 @ ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 @ ( k6_relat_1 @ X0 ) ) )
      | ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) )
        = ( sk_E_1 @ ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
      | ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ ( sk_E @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','95'])).

thf('97',plain,(
    ! [X14: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('98',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X17: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X17 )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ X17 ) @ X19 )
        = X19 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ ( sk_D @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) )
        = ( sk_D @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( zip_tseitin_0 @ X1 @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X2 @ ( k6_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X1 )
      | ( zip_tseitin_0 @ ( sk_D @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ ( sk_D @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) ) @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_D @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ ( sk_D @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) ) @ X0 @ ( k6_relat_1 @ X0 ) )
      | ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['103','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_D @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ ( sk_D @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) ) @ X0 @ ( k6_relat_1 @ X0 ) )
      | ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_D @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ ( sk_D @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 @ ( k6_relat_1 @ X0 ) )
      | ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['102','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_D @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ ( sk_D @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('112',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X5 @ X6 @ X7 ) @ X5 )
      | ~ ( zip_tseitin_0 @ X8 @ ( sk_D @ X5 @ X6 @ X7 ) @ X6 @ X7 )
      | ( X5
        = ( k9_relat_1 @ X7 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ ( sk_D @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('115',plain,(
    ! [X14: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ ( sk_D @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_0 @ X1 @ ( sk_D @ X0 @ X0 @ ( k6_relat_1 @ X0 ) ) @ X0 @ ( k6_relat_1 @ X0 ) )
      | ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( X0
      = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['110','117'])).

thf('119',plain,(
    ! [X14: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('120',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ ( sk_E @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['30','118','119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ( X2
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ( X2
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['2','121'])).

thf('123',plain,(
    ! [X14: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('124',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ( X2
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ( X2
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['122','123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    ! [X17: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X17 )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ X17 ) @ X19 )
        = X19 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('128',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ( X2
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ ( sk_D @ X5 @ X6 @ X7 ) @ X5 )
      | ( zip_tseitin_0 @ ( sk_E @ X5 @ X6 @ X7 ) @ ( sk_D @ X5 @ X6 @ X7 ) @ X6 @ X7 )
      | ( X5
        = ( k9_relat_1 @ X7 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('130',plain,(
    ! [X6: $i,X7: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( zip_tseitin_0 @ X12 @ X11 @ X6 @ X7 )
      | ( r2_hidden @ X11 @ ( k9_relat_1 @ X7 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('131',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X2
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ! [X6: $i,X7: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k9_relat_1 @ X7 @ X6 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X10 @ X6 @ X7 ) @ X10 @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('134',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X2
        = ( k9_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ X2 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ ( sk_D @ X2 @ X0 @ X1 ) @ X0 @ X1 ) @ ( sk_D @ X2 @ X0 @ X1 ) @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ ( sk_E_1 @ ( sk_D @ X2 @ X0 @ X1 ) @ X0 @ X1 ) @ ( sk_D @ X2 @ X0 @ X1 ) @ X0 @ X1 )
      | ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ X2 )
      | ( X2
        = ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X2
        = ( k1_funct_1 @ X0 @ X1 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('137',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X2
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( ( sk_D @ X2 @ X1 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_E_1 @ ( sk_D @ X2 @ X1 @ X0 ) @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('139',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ ( sk_E_1 @ ( sk_D @ X2 @ X0 @ X1 ) @ X0 @ X1 ) @ ( sk_D @ X2 @ X0 @ X1 ) @ X0 @ X1 )
      | ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ X2 )
      | ( X2
        = ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('140',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('141',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X2
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_D @ X2 @ X1 @ X0 ) @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_E_1 @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X1 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ( X2
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['138','141'])).

thf('143',plain,(
    ! [X14: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('144',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('145',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_E_1 @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X1 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ( X2
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('146',plain,(
    ! [X17: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X17 )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ X17 ) @ X19 )
        = X19 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('147',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ ( sk_E_1 @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( sk_E_1 @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( sk_E_1 @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ( X2
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ( X2
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['137','147'])).

thf('149',plain,(
    ! [X14: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('150',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('151',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( sk_E_1 @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ( X2
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ( X2
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['148','149','150'])).

thf('152',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ( ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( sk_E_1 @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ ( sk_E_1 @ ( sk_D @ X2 @ X0 @ X1 ) @ X0 @ X1 ) @ ( sk_D @ X2 @ X0 @ X1 ) @ X0 @ X1 )
      | ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ X2 )
      | ( X2
        = ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('154',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X1 @ X3 )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('155',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X2
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_D @ X2 @ X1 @ X0 ) @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ( X2
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ( X2
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['152','155'])).

thf('157',plain,(
    ! [X14: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('158',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('159',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ( X2
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ( X2
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['156','157','158'])).

thf('160',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ ( k6_relat_1 @ X1 ) ) @ X0 )
      | ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['160'])).

thf('162',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['162'])).

thf('164',plain,(
    ! [X17: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X17 )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ X17 ) @ X19 )
        = X19 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ ( sk_D @ X0 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( sk_D @ X0 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['162'])).

thf(t162_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B )
        = B ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t162_funct_1])).

thf('167',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('168',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( m1_subset_1 @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k9_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ X0 @ ( k6_relat_1 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['166','169'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('171',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k9_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) )
      | ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ ( k6_relat_1 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['162'])).

thf('174',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( zip_tseitin_0 @ X1 @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X2 @ ( k6_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('175',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      | ( zip_tseitin_0 @ ( sk_D @ X0 @ X1 @ ( k6_relat_1 @ X0 ) ) @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ ( sk_D @ X0 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X2 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( sk_B
        = ( k9_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_D @ sk_B @ X0 @ ( k6_relat_1 @ sk_B ) ) @ ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ ( sk_D @ sk_B @ X0 @ ( k6_relat_1 @ sk_B ) ) ) @ sk_A @ ( k6_relat_1 @ sk_B ) )
      | ( sk_B
        = ( k9_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['172','175'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_D @ sk_B @ X0 @ ( k6_relat_1 @ sk_B ) ) @ ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ ( sk_D @ sk_B @ X0 @ ( k6_relat_1 @ sk_B ) ) ) @ sk_A @ ( k6_relat_1 @ sk_B ) )
      | ( sk_B
        = ( k9_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_D @ sk_B @ X0 @ ( k6_relat_1 @ sk_B ) ) @ ( sk_D @ sk_B @ X0 @ ( k6_relat_1 @ sk_B ) ) @ sk_A @ ( k6_relat_1 @ sk_B ) )
      | ( sk_B
        = ( k9_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) )
      | ( v1_xboole_0 @ sk_A )
      | ( sk_B
        = ( k9_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['165','177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( sk_B
        = ( k9_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_D @ sk_B @ X0 @ ( k6_relat_1 @ sk_B ) ) @ ( sk_D @ sk_B @ X0 @ ( k6_relat_1 @ sk_B ) ) @ sk_A @ ( k6_relat_1 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['178'])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['162'])).

thf('181',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X5 @ X6 @ X7 ) @ X5 )
      | ~ ( zip_tseitin_0 @ X8 @ ( sk_D @ X5 @ X6 @ X7 ) @ X6 @ X7 )
      | ( X5
        = ( k9_relat_1 @ X7 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('182',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( zip_tseitin_0 @ X2 @ ( sk_D @ X0 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('184',plain,(
    ! [X14: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('185',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( zip_tseitin_0 @ X2 @ ( sk_D @ X0 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['182','183','184'])).

thf('186',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( zip_tseitin_0 @ X2 @ ( sk_D @ X0 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X1 @ ( k6_relat_1 @ X0 ) )
      | ( X0
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['185'])).

thf('187',plain,
    ( ( sk_B
      = ( k9_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( sk_B
      = ( k9_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['179','186'])).

thf('188',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_B
      = ( k9_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['187'])).

thf('189',plain,(
    ! [X6: $i,X7: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k9_relat_1 @ X7 @ X6 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X10 @ X6 @ X7 ) @ X10 @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X0 @ sk_A @ ( k6_relat_1 @ sk_B ) ) @ X0 @ sk_A @ ( k6_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X14: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('192',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('193',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X0 @ sk_A @ ( k6_relat_1 @ sk_B ) ) @ X0 @ sk_A @ ( k6_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['190','191','192'])).

thf('194',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('195',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X23 @ X24 )
      | ~ ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('196',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_E_1 @ X0 @ sk_A @ ( k6_relat_1 @ sk_B ) ) @ X0 @ sk_A @ ( k6_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['193','196'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ X0 ) ) @ sk_A @ ( k6_relat_1 @ sk_B ) ) @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ X0 ) ) @ sk_A @ ( k6_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['161','197'])).

thf('199',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X2
        = ( k1_funct_1 @ X0 @ X1 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('200',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) )
      | ( ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ X0 ) )
        = ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ ( sk_E_1 @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ X0 ) ) @ sk_A @ ( k6_relat_1 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ X0 ) ) @ sk_A @ ( k6_relat_1 @ sk_B ) ) @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ X0 ) ) @ sk_A @ ( k6_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['161','197'])).

thf('202',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('203',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ X0 ) ) @ sk_A @ ( k6_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('205',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ X0 ) ) @ sk_A @ ( k6_relat_1 @ sk_B ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['203','204'])).

thf('206',plain,(
    ! [X17: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X17 )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ X17 ) @ X19 )
        = X19 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('207',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ ( sk_E_1 @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ X0 ) ) @ sk_A @ ( k6_relat_1 @ sk_B ) ) )
        = ( sk_E_1 @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ X0 ) ) @ sk_A @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ X0 ) )
        = ( sk_E_1 @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ X0 ) ) @ sk_A @ ( k6_relat_1 @ sk_B ) ) )
      | ( sk_B
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) )
      | ( sk_B
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['200','207'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) )
      | ( ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ X0 ) )
        = ( sk_E_1 @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ X0 ) ) @ sk_A @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['208'])).

thf('210',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ X0 ) ) @ sk_A @ ( k6_relat_1 @ sk_B ) ) @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ X0 ) ) @ sk_A @ ( k6_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['161','197'])).

thf('211',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X1 @ X3 )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('212',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ X0 ) ) @ sk_A @ ( k6_relat_1 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,(
    ! [X17: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X17 )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ X17 ) @ X19 )
        = X19 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('214',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ sk_A ) @ ( sk_E_1 @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ X0 ) ) @ sk_A @ ( k6_relat_1 @ sk_B ) ) )
        = ( sk_E_1 @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ X0 ) ) @ sk_A @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['212','213'])).

thf('215',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k6_relat_1 @ sk_A ) @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ X0 ) ) )
        = ( sk_E_1 @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ X0 ) ) @ sk_A @ ( k6_relat_1 @ sk_B ) ) )
      | ( sk_B
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) )
      | ( sk_B
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['209','214'])).

thf('216',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ sk_A ) @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ X0 ) ) )
        = ( sk_E_1 @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ X0 ) ) @ sk_A @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['215'])).

thf('217',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ X0 ) ) @ sk_A @ ( k6_relat_1 @ sk_B ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['203','204'])).

thf('218',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ ( k6_relat_1 @ sk_A ) @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ X0 ) ) ) @ sk_B )
      | ( sk_B
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) )
      | ( sk_B
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['216','217'])).

thf('219',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k6_relat_1 @ sk_A ) @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ X0 ) ) ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['218'])).

thf('220',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ sk_A ) ) @ sk_B )
    | ( sk_B
      = ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ sk_A ) ) @ sk_B )
    | ( sk_B
      = ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['128','219'])).

thf('221',plain,
    ( ( sk_B
      = ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ sk_A ) ) @ sk_B ) ),
    inference(simplify,[status(thm)],['220'])).

thf('222',plain,(
    ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('223',plain,(
    r2_hidden @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ sk_A ) ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['221','222'])).

thf('224',plain,(
    r2_hidden @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ sk_A ) ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['221','222'])).

thf('225',plain,(
    ! [X17: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X17 )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ X17 ) @ X19 )
        = X19 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('226',plain,
    ( ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ sk_A ) ) )
    = ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['224','225'])).

thf('227',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) )
      | ( ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ X0 ) )
        = ( sk_E_1 @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ X0 ) ) @ sk_A @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['208'])).

thf('228',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ ( sk_E_1 @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ X0 ) ) @ sk_A @ ( k6_relat_1 @ sk_B ) ) )
        = ( sk_E_1 @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ X0 ) ) @ sk_A @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('229',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ X0 ) ) )
        = ( sk_E_1 @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ X0 ) ) @ sk_A @ ( k6_relat_1 @ sk_B ) ) )
      | ( sk_B
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) )
      | ( sk_B
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['227','228'])).

thf('230',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ X0 ) ) )
        = ( sk_E_1 @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ X0 ) ) @ sk_A @ ( k6_relat_1 @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['229'])).

thf('231',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ X0 ) ) @ sk_A @ ( k6_relat_1 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('232',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ X0 ) ) ) @ sk_A )
      | ( sk_B
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) )
      | ( sk_B
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['230','231'])).

thf('233',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ X0 ) ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['232'])).

thf('234',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ sk_A ) ) @ sk_A )
    | ( sk_B
      = ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['226','233'])).

thf('235',plain,(
    ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('236',plain,(
    r2_hidden @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ sk_A ) ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['234','235'])).

thf('237',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( zip_tseitin_0 @ X1 @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X2 @ ( k6_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('238',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ sk_A ) ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ sk_A ) ) @ ( k1_funct_1 @ ( k6_relat_1 @ sk_A ) @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ sk_A ) ) ) @ X0 @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['236','237'])).

thf('239',plain,(
    r2_hidden @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ sk_A ) ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['234','235'])).

thf('240',plain,(
    ! [X17: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X17 )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ X17 ) @ X19 )
        = X19 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('241',plain,
    ( ( k1_funct_1 @ ( k6_relat_1 @ sk_A ) @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ sk_A ) ) )
    = ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['239','240'])).

thf('242',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ sk_A ) ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ sk_A ) ) @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ sk_A ) ) @ X0 @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['238','241'])).

thf('243',plain,(
    zip_tseitin_0 @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ sk_A ) ) @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ sk_A ) ) @ sk_B @ ( k6_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['223','242'])).

thf('244',plain,(
    r2_hidden @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ sk_A ) ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['221','222'])).

thf('245',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X5 @ X6 @ X7 ) @ X5 )
      | ~ ( zip_tseitin_0 @ X8 @ ( sk_D @ X5 @ X6 @ X7 ) @ X6 @ X7 )
      | ( X5
        = ( k9_relat_1 @ X7 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('246',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ sk_A ) )
      | ( sk_B
        = ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
      | ~ ( zip_tseitin_0 @ X0 @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ sk_A ) ) @ sk_B @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['244','245'])).

thf('247',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('248',plain,(
    ! [X14: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('249',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
      | ~ ( zip_tseitin_0 @ X0 @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ sk_A ) ) @ sk_B @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['246','247','248'])).

thf('250',plain,(
    ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('251',plain,(
    ! [X0: $i] :
      ~ ( zip_tseitin_0 @ X0 @ ( sk_D @ sk_B @ sk_B @ ( k6_relat_1 @ sk_A ) ) @ sk_B @ ( k6_relat_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['249','250'])).

thf('252',plain,(
    $false ),
    inference('sup-',[status(thm)],['243','251'])).


%------------------------------------------------------------------------------
