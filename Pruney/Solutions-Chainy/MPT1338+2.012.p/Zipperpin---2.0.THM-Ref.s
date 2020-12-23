%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.L9yOyY8Jvv

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:48 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :  264 (3339 expanded)
%              Number of leaves         :   53 ( 972 expanded)
%              Depth                    :   30
%              Number of atoms          : 2297 (83329 expanded)
%              Number of equality atoms :  151 (4229 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t62_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_struct_0 @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v2_funct_1 @ C ) )
               => ( ( ( k1_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                    = ( k2_struct_0 @ B ) )
                  & ( ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                    = ( k2_struct_0 @ A ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( l1_struct_0 @ B ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                      = ( k2_struct_0 @ B ) )
                    & ( v2_funct_1 @ C ) )
                 => ( ( ( k1_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                      = ( k2_struct_0 @ B ) )
                    & ( ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                      = ( k2_struct_0 @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_tops_2])).

thf('1',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_B_1 ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_B_1 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('9',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('10',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['7','12'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('14',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( v1_partfun1 @ X24 @ X25 )
      | ~ ( v1_funct_2 @ X24 @ X25 @ X26 )
      | ~ ( v1_funct_1 @ X24 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('15',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) )
    | ( v1_partfun1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('18',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('23',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( v1_partfun1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','23'])).

thf('25',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('26',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('27',plain,(
    ! [X38: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X38 ) )
      | ~ ( l1_struct_0 @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( l1_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf('31',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    v1_partfun1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['24','34'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('36',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v1_partfun1 @ X36 @ X35 )
      | ( ( k1_relat_1 @ X36 )
        = X35 )
      | ~ ( v4_relat_1 @ X36 @ X35 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v4_relat_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('39',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('40',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('42',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v4_relat_1 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('43',plain,(
    v4_relat_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['37','40','43'])).

thf('45',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['37','40','43'])).

thf('46',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('47',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('48',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('53',plain,(
    v1_partfun1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['24','34'])).

thf('54',plain,
    ( ( v1_partfun1 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_partfun1 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v1_partfun1 @ X36 @ X35 )
      | ( ( k1_relat_1 @ X36 )
        = X35 )
      | ~ ( v4_relat_1 @ X36 @ X35 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('58',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v4_relat_1 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('60',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('61',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v4_relat_1 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('62',plain,(
    v4_relat_1 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['58','59','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['51','63'])).

thf(d4_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( k2_tops_2 @ A @ B @ C )
          = ( k2_funct_1 @ C ) ) ) ) )).

thf('65',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k2_relset_1 @ X40 @ X39 @ X41 )
       != X39 )
      | ~ ( v2_funct_1 @ X41 )
      | ( ( k2_tops_2 @ X40 @ X39 @ X41 )
        = ( k2_funct_1 @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) )
      | ~ ( v1_funct_2 @ X41 @ X40 @ X39 )
      | ~ ( v1_funct_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('66',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
      = ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
     != ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('69',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['58','59','62'])).

thf('74',plain,(
    v1_funct_2 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('77',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('78',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['58','59','62'])).

thf('80',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
      = ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k2_relat_1 @ sk_C_1 )
     != ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['66','67','74','75','80'])).

thf('82',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
     != ( k2_struct_0 @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_B_1 )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
      = ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['46','81'])).

thf('83',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('84',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
     != ( k2_relat_1 @ sk_C_1 ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
      = ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
    = ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('88',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C_1 ) @ ( k2_funct_1 @ sk_C_1 ) )
     != ( k2_relat_1 @ sk_C_1 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['2','44','45','86','87'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('89',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k1_relat_1 @ X14 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('90',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['51','63'])).

thf(dt_k2_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) )
        & ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A )
        & ( m1_subset_1 @ ( k2_tops_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) )).

thf('91',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X42 @ X43 @ X44 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X42 @ X43 )
      | ~ ( v1_funct_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('92',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_funct_2 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('95',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
    = ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['85'])).

thf('97',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('99',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C_1 ) @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['58','59','62'])).

thf('101',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('102',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('103',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('104',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B_1 ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['101','106'])).

thf('108',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['100','109'])).

thf('111',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('112',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['58','59','62'])).

thf('113',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) @ sk_C_1 ) )
     != ( k1_relat_1 @ sk_C_1 ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['37','40','43'])).

thf('115',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('116',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('117',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('121',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['58','59','62'])).

thf('123',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k2_relset_1 @ X40 @ X39 @ X41 )
       != X39 )
      | ~ ( v2_funct_1 @ X41 )
      | ( ( k2_tops_2 @ X40 @ X39 @ X41 )
        = ( k2_funct_1 @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) )
      | ~ ( v1_funct_2 @ X41 @ X40 @ X39 )
      | ~ ( v1_funct_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('125',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) @ sk_C_1 )
      = ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) @ sk_C_1 )
     != ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('128',plain,(
    v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('129',plain,
    ( ( v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('133',plain,(
    v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['58','59','62'])).

thf('135',plain,(
    v1_funct_2 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('138',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('139',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
      = ( k2_struct_0 @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['138','139'])).

thf('141',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C_1 )
      = ( k2_struct_0 @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['137','142'])).

thf('144',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('147',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('148',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['145','146','147'])).

thf('149',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['58','59','62'])).

thf('150',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) @ sk_C_1 )
      = ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k2_relat_1 @ sk_C_1 )
     != ( k2_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['125','126','135','136','150'])).

thf('152',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) @ sk_C_1 )
    = ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C_1 ) @ ( k2_funct_1 @ sk_C_1 ) )
     != ( k1_relat_1 @ sk_C_1 ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['113','114','152'])).

thf('154',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
     != ( k1_relat_1 @ sk_C_1 ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['99','153'])).

thf('155',plain,
    ( ( ( ( k1_relat_1 @ sk_C_1 )
       != ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v2_funct_1 @ sk_C_1 ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','154'])).

thf('156',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('157',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
     != ( k1_relat_1 @ sk_C_1 ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['155','156','157','158'])).

thf('160',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_B_1 ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('162',plain,(
    ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
 != ( k2_struct_0 @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['160','161'])).

thf('163',plain,(
    ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C_1 ) @ ( k2_funct_1 @ sk_C_1 ) )
 != ( k2_relat_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['88','162'])).

thf('164',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['51','63'])).

thf('165',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( v1_funct_2 @ ( k2_tops_2 @ X42 @ X43 @ X44 ) @ X43 @ X42 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X42 @ X43 )
      | ~ ( v1_funct_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('166',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_funct_2 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    v1_funct_2 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('169',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['166','167','168'])).

thf('170',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
    = ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['85'])).

thf('171',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['169','170'])).

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

thf('172',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('173',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( ( u1_struct_0 @ sk_B_1 )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C_1 ) @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('174',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('175',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('176',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['174','176'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('178',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('179',plain,(
    ! [X13: $i] :
      ( ( r1_tarski @ X13 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X13 ) @ ( k2_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('180',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['178','181'])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('184',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['177','184'])).

thf('186',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('187',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('188',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['187'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('189',plain,(
    ! [X10: $i,X11: $i] :
      ~ ( r2_hidden @ X10 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('190',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['186','190'])).

thf('192',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['185','191'])).

thf('193',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['95','96'])).

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

thf('194',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('195',plain,
    ( ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( zip_tseitin_0 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['192','195'])).

thf('197',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('198',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['196','197'])).

thf(fc11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('199',plain,(
    ! [X12: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X12 ) )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf('200',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('201',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,(
    zip_tseitin_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['198','201'])).

thf('203',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C_1 ) @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['173','202'])).

thf('204',plain,(
    ( u1_struct_0 @ sk_B_1 )
 != ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['163','203'])).

thf('205',plain,
    ( ( ( k2_struct_0 @ sk_B_1 )
     != ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','204'])).

thf('206',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('207',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['205','206','207'])).

thf('209',plain,(
    $false ),
    inference(simplify,[status(thm)],['208'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.L9yOyY8Jvv
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.35  % CPULimit   : 60
% 0.20/0.35  % DateTime   : Tue Dec  1 12:52:22 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  % Running portfolio for 600 s
% 0.20/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 1.06/1.27  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.06/1.27  % Solved by: fo/fo7.sh
% 1.06/1.27  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.06/1.27  % done 1032 iterations in 0.835s
% 1.06/1.27  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.06/1.27  % SZS output start Refutation
% 1.06/1.27  thf(sk_B_type, type, sk_B: $i > $i).
% 1.06/1.27  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.06/1.27  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.06/1.27  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.06/1.27  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.06/1.27  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.06/1.27  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.06/1.27  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.06/1.27  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.06/1.27  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.06/1.27  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.06/1.27  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.06/1.27  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.06/1.27  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.06/1.27  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.06/1.27  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.06/1.27  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.06/1.27  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.06/1.27  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.06/1.27  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.06/1.27  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.06/1.27  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.06/1.27  thf(sk_A_type, type, sk_A: $i).
% 1.06/1.27  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.06/1.27  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.06/1.27  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.06/1.27  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 1.06/1.27  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.06/1.27  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.06/1.27  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.06/1.27  thf(d3_struct_0, axiom,
% 1.06/1.27    (![A:$i]:
% 1.06/1.27     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.06/1.27  thf('0', plain,
% 1.06/1.27      (![X37 : $i]:
% 1.06/1.27         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 1.06/1.27      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.06/1.27  thf(t62_tops_2, conjecture,
% 1.06/1.27    (![A:$i]:
% 1.06/1.27     ( ( l1_struct_0 @ A ) =>
% 1.06/1.27       ( ![B:$i]:
% 1.06/1.27         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.06/1.27           ( ![C:$i]:
% 1.06/1.27             ( ( ( v1_funct_1 @ C ) & 
% 1.06/1.27                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.06/1.27                 ( m1_subset_1 @
% 1.06/1.27                   C @ 
% 1.06/1.27                   ( k1_zfmisc_1 @
% 1.06/1.27                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.06/1.27               ( ( ( ( k2_relset_1 @
% 1.06/1.27                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.06/1.27                     ( k2_struct_0 @ B ) ) & 
% 1.06/1.27                   ( v2_funct_1 @ C ) ) =>
% 1.06/1.27                 ( ( ( k1_relset_1 @
% 1.06/1.27                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.06/1.27                       ( k2_tops_2 @
% 1.06/1.27                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.06/1.27                     ( k2_struct_0 @ B ) ) & 
% 1.06/1.27                   ( ( k2_relset_1 @
% 1.06/1.27                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.06/1.27                       ( k2_tops_2 @
% 1.06/1.27                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.06/1.27                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 1.06/1.27  thf(zf_stmt_0, negated_conjecture,
% 1.06/1.27    (~( ![A:$i]:
% 1.06/1.27        ( ( l1_struct_0 @ A ) =>
% 1.06/1.27          ( ![B:$i]:
% 1.06/1.27            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.06/1.27              ( ![C:$i]:
% 1.06/1.27                ( ( ( v1_funct_1 @ C ) & 
% 1.06/1.27                    ( v1_funct_2 @
% 1.06/1.27                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.06/1.27                    ( m1_subset_1 @
% 1.06/1.27                      C @ 
% 1.06/1.27                      ( k1_zfmisc_1 @
% 1.06/1.27                        ( k2_zfmisc_1 @
% 1.06/1.27                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.06/1.27                  ( ( ( ( k2_relset_1 @
% 1.06/1.27                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.06/1.27                        ( k2_struct_0 @ B ) ) & 
% 1.06/1.27                      ( v2_funct_1 @ C ) ) =>
% 1.06/1.27                    ( ( ( k1_relset_1 @
% 1.06/1.27                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.06/1.27                          ( k2_tops_2 @
% 1.06/1.27                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.06/1.27                        ( k2_struct_0 @ B ) ) & 
% 1.06/1.27                      ( ( k2_relset_1 @
% 1.06/1.27                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.06/1.27                          ( k2_tops_2 @
% 1.06/1.27                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.06/1.27                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 1.06/1.27    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 1.06/1.27  thf('1', plain,
% 1.06/1.27      ((((k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.27          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1))
% 1.06/1.27          != (k2_struct_0 @ sk_B_1))
% 1.06/1.27        | ((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.27            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1))
% 1.06/1.27            != (k2_struct_0 @ sk_A)))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('2', plain,
% 1.06/1.27      ((((k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.27          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1))
% 1.06/1.27          != (k2_struct_0 @ sk_B_1)))
% 1.06/1.27         <= (~
% 1.06/1.27             (((k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.27                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 1.06/1.27                 sk_C_1))
% 1.06/1.27                = (k2_struct_0 @ sk_B_1))))),
% 1.06/1.27      inference('split', [status(esa)], ['1'])).
% 1.06/1.27  thf('3', plain,
% 1.06/1.27      (![X37 : $i]:
% 1.06/1.27         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 1.06/1.27      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.06/1.27  thf('4', plain,
% 1.06/1.27      ((m1_subset_1 @ sk_C_1 @ 
% 1.06/1.27        (k1_zfmisc_1 @ 
% 1.06/1.27         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('5', plain,
% 1.06/1.27      (((m1_subset_1 @ sk_C_1 @ 
% 1.06/1.27         (k1_zfmisc_1 @ 
% 1.06/1.27          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))))
% 1.06/1.27        | ~ (l1_struct_0 @ sk_B_1))),
% 1.06/1.27      inference('sup+', [status(thm)], ['3', '4'])).
% 1.06/1.27  thf('6', plain, ((l1_struct_0 @ sk_B_1)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('7', plain,
% 1.06/1.27      ((m1_subset_1 @ sk_C_1 @ 
% 1.06/1.27        (k1_zfmisc_1 @ 
% 1.06/1.27         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))))),
% 1.06/1.27      inference('demod', [status(thm)], ['5', '6'])).
% 1.06/1.27  thf('8', plain,
% 1.06/1.27      ((m1_subset_1 @ sk_C_1 @ 
% 1.06/1.27        (k1_zfmisc_1 @ 
% 1.06/1.27         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf(redefinition_k2_relset_1, axiom,
% 1.06/1.27    (![A:$i,B:$i,C:$i]:
% 1.06/1.27     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.06/1.27       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.06/1.27  thf('9', plain,
% 1.06/1.27      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.06/1.27         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 1.06/1.27          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 1.06/1.27      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.06/1.27  thf('10', plain,
% 1.06/1.27      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 1.06/1.27         = (k2_relat_1 @ sk_C_1))),
% 1.06/1.27      inference('sup-', [status(thm)], ['8', '9'])).
% 1.06/1.27  thf('11', plain,
% 1.06/1.27      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 1.06/1.27         = (k2_struct_0 @ sk_B_1))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('12', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_1))),
% 1.06/1.27      inference('sup+', [status(thm)], ['10', '11'])).
% 1.06/1.27  thf('13', plain,
% 1.06/1.27      ((m1_subset_1 @ sk_C_1 @ 
% 1.06/1.27        (k1_zfmisc_1 @ 
% 1.06/1.27         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1))))),
% 1.06/1.27      inference('demod', [status(thm)], ['7', '12'])).
% 1.06/1.27  thf(cc5_funct_2, axiom,
% 1.06/1.27    (![A:$i,B:$i]:
% 1.06/1.27     ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.06/1.27       ( ![C:$i]:
% 1.06/1.27         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.06/1.27           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 1.06/1.27             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 1.06/1.27  thf('14', plain,
% 1.06/1.27      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.06/1.27         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 1.06/1.27          | (v1_partfun1 @ X24 @ X25)
% 1.06/1.27          | ~ (v1_funct_2 @ X24 @ X25 @ X26)
% 1.06/1.27          | ~ (v1_funct_1 @ X24)
% 1.06/1.27          | (v1_xboole_0 @ X26))),
% 1.06/1.27      inference('cnf', [status(esa)], [cc5_funct_2])).
% 1.06/1.27  thf('15', plain,
% 1.06/1.27      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1))
% 1.06/1.27        | ~ (v1_funct_1 @ sk_C_1)
% 1.06/1.27        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1))
% 1.06/1.27        | (v1_partfun1 @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.27      inference('sup-', [status(thm)], ['13', '14'])).
% 1.06/1.27  thf('16', plain, ((v1_funct_1 @ sk_C_1)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('17', plain,
% 1.06/1.27      (![X37 : $i]:
% 1.06/1.27         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 1.06/1.27      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.06/1.27  thf('18', plain,
% 1.06/1.27      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('19', plain,
% 1.06/1.27      (((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))
% 1.06/1.27        | ~ (l1_struct_0 @ sk_B_1))),
% 1.06/1.27      inference('sup+', [status(thm)], ['17', '18'])).
% 1.06/1.27  thf('20', plain, ((l1_struct_0 @ sk_B_1)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('21', plain,
% 1.06/1.27      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))),
% 1.06/1.27      inference('demod', [status(thm)], ['19', '20'])).
% 1.06/1.27  thf('22', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_1))),
% 1.06/1.27      inference('sup+', [status(thm)], ['10', '11'])).
% 1.06/1.27  thf('23', plain,
% 1.06/1.27      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1))),
% 1.06/1.27      inference('demod', [status(thm)], ['21', '22'])).
% 1.06/1.27  thf('24', plain,
% 1.06/1.27      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1))
% 1.06/1.27        | (v1_partfun1 @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.27      inference('demod', [status(thm)], ['15', '16', '23'])).
% 1.06/1.27  thf('25', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_1))),
% 1.06/1.27      inference('sup+', [status(thm)], ['10', '11'])).
% 1.06/1.27  thf('26', plain,
% 1.06/1.27      (![X37 : $i]:
% 1.06/1.27         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 1.06/1.27      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.06/1.27  thf(fc2_struct_0, axiom,
% 1.06/1.27    (![A:$i]:
% 1.06/1.27     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.06/1.27       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.06/1.27  thf('27', plain,
% 1.06/1.27      (![X38 : $i]:
% 1.06/1.27         (~ (v1_xboole_0 @ (u1_struct_0 @ X38))
% 1.06/1.27          | ~ (l1_struct_0 @ X38)
% 1.06/1.27          | (v2_struct_0 @ X38))),
% 1.06/1.27      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.06/1.27  thf('28', plain,
% 1.06/1.27      (![X0 : $i]:
% 1.06/1.27         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 1.06/1.27          | ~ (l1_struct_0 @ X0)
% 1.06/1.27          | (v2_struct_0 @ X0)
% 1.06/1.27          | ~ (l1_struct_0 @ X0))),
% 1.06/1.27      inference('sup-', [status(thm)], ['26', '27'])).
% 1.06/1.27  thf('29', plain,
% 1.06/1.27      (![X0 : $i]:
% 1.06/1.27         ((v2_struct_0 @ X0)
% 1.06/1.27          | ~ (l1_struct_0 @ X0)
% 1.06/1.27          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 1.06/1.27      inference('simplify', [status(thm)], ['28'])).
% 1.06/1.27  thf('30', plain,
% 1.06/1.27      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_1))
% 1.06/1.27        | ~ (l1_struct_0 @ sk_B_1)
% 1.06/1.27        | (v2_struct_0 @ sk_B_1))),
% 1.06/1.27      inference('sup-', [status(thm)], ['25', '29'])).
% 1.06/1.27  thf('31', plain, ((l1_struct_0 @ sk_B_1)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('32', plain,
% 1.06/1.27      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_1)) | (v2_struct_0 @ sk_B_1))),
% 1.06/1.27      inference('demod', [status(thm)], ['30', '31'])).
% 1.06/1.27  thf('33', plain, (~ (v2_struct_0 @ sk_B_1)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('34', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_1))),
% 1.06/1.27      inference('clc', [status(thm)], ['32', '33'])).
% 1.06/1.27  thf('35', plain, ((v1_partfun1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 1.06/1.27      inference('clc', [status(thm)], ['24', '34'])).
% 1.06/1.27  thf(d4_partfun1, axiom,
% 1.06/1.27    (![A:$i,B:$i]:
% 1.06/1.27     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.06/1.27       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 1.06/1.27  thf('36', plain,
% 1.06/1.27      (![X35 : $i, X36 : $i]:
% 1.06/1.27         (~ (v1_partfun1 @ X36 @ X35)
% 1.06/1.27          | ((k1_relat_1 @ X36) = (X35))
% 1.06/1.27          | ~ (v4_relat_1 @ X36 @ X35)
% 1.06/1.27          | ~ (v1_relat_1 @ X36))),
% 1.06/1.27      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.06/1.27  thf('37', plain,
% 1.06/1.27      ((~ (v1_relat_1 @ sk_C_1)
% 1.06/1.27        | ~ (v4_relat_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 1.06/1.27        | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 1.06/1.27      inference('sup-', [status(thm)], ['35', '36'])).
% 1.06/1.27  thf('38', plain,
% 1.06/1.27      ((m1_subset_1 @ sk_C_1 @ 
% 1.06/1.27        (k1_zfmisc_1 @ 
% 1.06/1.27         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf(cc1_relset_1, axiom,
% 1.06/1.27    (![A:$i,B:$i,C:$i]:
% 1.06/1.27     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.06/1.27       ( v1_relat_1 @ C ) ))).
% 1.06/1.27  thf('39', plain,
% 1.06/1.27      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.06/1.27         ((v1_relat_1 @ X15)
% 1.06/1.27          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 1.06/1.27      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.06/1.27  thf('40', plain, ((v1_relat_1 @ sk_C_1)),
% 1.06/1.27      inference('sup-', [status(thm)], ['38', '39'])).
% 1.06/1.27  thf('41', plain,
% 1.06/1.27      ((m1_subset_1 @ sk_C_1 @ 
% 1.06/1.27        (k1_zfmisc_1 @ 
% 1.06/1.27         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf(cc2_relset_1, axiom,
% 1.06/1.27    (![A:$i,B:$i,C:$i]:
% 1.06/1.27     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.06/1.27       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.06/1.27  thf('42', plain,
% 1.06/1.27      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.06/1.27         ((v4_relat_1 @ X18 @ X19)
% 1.06/1.27          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.06/1.27      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.06/1.27  thf('43', plain, ((v4_relat_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 1.06/1.27      inference('sup-', [status(thm)], ['41', '42'])).
% 1.06/1.27  thf('44', plain, (((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A))),
% 1.06/1.27      inference('demod', [status(thm)], ['37', '40', '43'])).
% 1.06/1.27  thf('45', plain, (((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A))),
% 1.06/1.27      inference('demod', [status(thm)], ['37', '40', '43'])).
% 1.06/1.27  thf('46', plain,
% 1.06/1.27      (![X37 : $i]:
% 1.06/1.27         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 1.06/1.27      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.06/1.27  thf('47', plain,
% 1.06/1.27      (![X37 : $i]:
% 1.06/1.27         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 1.06/1.27      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.06/1.27  thf('48', plain,
% 1.06/1.27      ((m1_subset_1 @ sk_C_1 @ 
% 1.06/1.27        (k1_zfmisc_1 @ 
% 1.06/1.27         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('49', plain,
% 1.06/1.27      (((m1_subset_1 @ sk_C_1 @ 
% 1.06/1.27         (k1_zfmisc_1 @ 
% 1.06/1.27          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))
% 1.06/1.27        | ~ (l1_struct_0 @ sk_A))),
% 1.06/1.27      inference('sup+', [status(thm)], ['47', '48'])).
% 1.06/1.27  thf('50', plain, ((l1_struct_0 @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('51', plain,
% 1.06/1.27      ((m1_subset_1 @ sk_C_1 @ 
% 1.06/1.27        (k1_zfmisc_1 @ 
% 1.06/1.27         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 1.06/1.27      inference('demod', [status(thm)], ['49', '50'])).
% 1.06/1.27  thf('52', plain,
% 1.06/1.27      (![X37 : $i]:
% 1.06/1.27         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 1.06/1.27      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.06/1.27  thf('53', plain, ((v1_partfun1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 1.06/1.27      inference('clc', [status(thm)], ['24', '34'])).
% 1.06/1.27  thf('54', plain,
% 1.06/1.27      (((v1_partfun1 @ sk_C_1 @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 1.06/1.27      inference('sup+', [status(thm)], ['52', '53'])).
% 1.06/1.27  thf('55', plain, ((l1_struct_0 @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('56', plain, ((v1_partfun1 @ sk_C_1 @ (k2_struct_0 @ sk_A))),
% 1.06/1.27      inference('demod', [status(thm)], ['54', '55'])).
% 1.06/1.27  thf('57', plain,
% 1.06/1.27      (![X35 : $i, X36 : $i]:
% 1.06/1.27         (~ (v1_partfun1 @ X36 @ X35)
% 1.06/1.27          | ((k1_relat_1 @ X36) = (X35))
% 1.06/1.27          | ~ (v4_relat_1 @ X36 @ X35)
% 1.06/1.27          | ~ (v1_relat_1 @ X36))),
% 1.06/1.27      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.06/1.27  thf('58', plain,
% 1.06/1.27      ((~ (v1_relat_1 @ sk_C_1)
% 1.06/1.27        | ~ (v4_relat_1 @ sk_C_1 @ (k2_struct_0 @ sk_A))
% 1.06/1.27        | ((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A)))),
% 1.06/1.27      inference('sup-', [status(thm)], ['56', '57'])).
% 1.06/1.27  thf('59', plain, ((v1_relat_1 @ sk_C_1)),
% 1.06/1.27      inference('sup-', [status(thm)], ['38', '39'])).
% 1.06/1.27  thf('60', plain,
% 1.06/1.27      ((m1_subset_1 @ sk_C_1 @ 
% 1.06/1.27        (k1_zfmisc_1 @ 
% 1.06/1.27         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 1.06/1.27      inference('demod', [status(thm)], ['49', '50'])).
% 1.06/1.27  thf('61', plain,
% 1.06/1.27      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.06/1.27         ((v4_relat_1 @ X18 @ X19)
% 1.06/1.27          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.06/1.27      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.06/1.27  thf('62', plain, ((v4_relat_1 @ sk_C_1 @ (k2_struct_0 @ sk_A))),
% 1.06/1.27      inference('sup-', [status(thm)], ['60', '61'])).
% 1.06/1.27  thf('63', plain, (((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A))),
% 1.06/1.27      inference('demod', [status(thm)], ['58', '59', '62'])).
% 1.06/1.27  thf('64', plain,
% 1.06/1.27      ((m1_subset_1 @ sk_C_1 @ 
% 1.06/1.27        (k1_zfmisc_1 @ 
% 1.06/1.27         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1))))),
% 1.06/1.27      inference('demod', [status(thm)], ['51', '63'])).
% 1.06/1.27  thf(d4_tops_2, axiom,
% 1.06/1.27    (![A:$i,B:$i,C:$i]:
% 1.06/1.27     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.06/1.27         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.06/1.27       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.06/1.27         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 1.06/1.27  thf('65', plain,
% 1.06/1.27      (![X39 : $i, X40 : $i, X41 : $i]:
% 1.06/1.27         (((k2_relset_1 @ X40 @ X39 @ X41) != (X39))
% 1.06/1.27          | ~ (v2_funct_1 @ X41)
% 1.06/1.27          | ((k2_tops_2 @ X40 @ X39 @ X41) = (k2_funct_1 @ X41))
% 1.06/1.27          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39)))
% 1.06/1.27          | ~ (v1_funct_2 @ X41 @ X40 @ X39)
% 1.06/1.27          | ~ (v1_funct_1 @ X41))),
% 1.06/1.27      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.06/1.27  thf('66', plain,
% 1.06/1.27      ((~ (v1_funct_1 @ sk_C_1)
% 1.06/1.27        | ~ (v1_funct_2 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ 
% 1.06/1.27             (u1_struct_0 @ sk_B_1))
% 1.06/1.27        | ((k2_tops_2 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 1.06/1.27            = (k2_funct_1 @ sk_C_1))
% 1.06/1.27        | ~ (v2_funct_1 @ sk_C_1)
% 1.06/1.27        | ((k2_relset_1 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.06/1.27            sk_C_1) != (u1_struct_0 @ sk_B_1)))),
% 1.06/1.27      inference('sup-', [status(thm)], ['64', '65'])).
% 1.06/1.27  thf('67', plain, ((v1_funct_1 @ sk_C_1)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('68', plain,
% 1.06/1.27      (![X37 : $i]:
% 1.06/1.27         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 1.06/1.27      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.06/1.27  thf('69', plain,
% 1.06/1.27      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('70', plain,
% 1.06/1.27      (((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))
% 1.06/1.27        | ~ (l1_struct_0 @ sk_A))),
% 1.06/1.27      inference('sup+', [status(thm)], ['68', '69'])).
% 1.06/1.27  thf('71', plain, ((l1_struct_0 @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('72', plain,
% 1.06/1.27      ((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 1.06/1.27      inference('demod', [status(thm)], ['70', '71'])).
% 1.06/1.27  thf('73', plain, (((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A))),
% 1.06/1.27      inference('demod', [status(thm)], ['58', '59', '62'])).
% 1.06/1.27  thf('74', plain,
% 1.06/1.27      ((v1_funct_2 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1))),
% 1.06/1.27      inference('demod', [status(thm)], ['72', '73'])).
% 1.06/1.27  thf('75', plain, ((v2_funct_1 @ sk_C_1)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('76', plain,
% 1.06/1.27      ((m1_subset_1 @ sk_C_1 @ 
% 1.06/1.27        (k1_zfmisc_1 @ 
% 1.06/1.27         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 1.06/1.27      inference('demod', [status(thm)], ['49', '50'])).
% 1.06/1.27  thf('77', plain,
% 1.06/1.27      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.06/1.27         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 1.06/1.27          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 1.06/1.27      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.06/1.27  thf('78', plain,
% 1.06/1.27      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 1.06/1.27         = (k2_relat_1 @ sk_C_1))),
% 1.06/1.27      inference('sup-', [status(thm)], ['76', '77'])).
% 1.06/1.27  thf('79', plain, (((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A))),
% 1.06/1.27      inference('demod', [status(thm)], ['58', '59', '62'])).
% 1.06/1.27  thf('80', plain,
% 1.06/1.27      (((k2_relset_1 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 1.06/1.27         = (k2_relat_1 @ sk_C_1))),
% 1.06/1.27      inference('demod', [status(thm)], ['78', '79'])).
% 1.06/1.27  thf('81', plain,
% 1.06/1.27      ((((k2_tops_2 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 1.06/1.27          = (k2_funct_1 @ sk_C_1))
% 1.06/1.27        | ((k2_relat_1 @ sk_C_1) != (u1_struct_0 @ sk_B_1)))),
% 1.06/1.27      inference('demod', [status(thm)], ['66', '67', '74', '75', '80'])).
% 1.06/1.27  thf('82', plain,
% 1.06/1.27      ((((k2_relat_1 @ sk_C_1) != (k2_struct_0 @ sk_B_1))
% 1.06/1.27        | ~ (l1_struct_0 @ sk_B_1)
% 1.06/1.27        | ((k2_tops_2 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 1.06/1.27            = (k2_funct_1 @ sk_C_1)))),
% 1.06/1.27      inference('sup-', [status(thm)], ['46', '81'])).
% 1.06/1.27  thf('83', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_1))),
% 1.06/1.27      inference('sup+', [status(thm)], ['10', '11'])).
% 1.06/1.27  thf('84', plain, ((l1_struct_0 @ sk_B_1)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('85', plain,
% 1.06/1.27      ((((k2_relat_1 @ sk_C_1) != (k2_relat_1 @ sk_C_1))
% 1.06/1.27        | ((k2_tops_2 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 1.06/1.27            = (k2_funct_1 @ sk_C_1)))),
% 1.06/1.27      inference('demod', [status(thm)], ['82', '83', '84'])).
% 1.06/1.27  thf('86', plain,
% 1.06/1.27      (((k2_tops_2 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 1.06/1.27         = (k2_funct_1 @ sk_C_1))),
% 1.06/1.27      inference('simplify', [status(thm)], ['85'])).
% 1.06/1.27  thf('87', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_1))),
% 1.06/1.27      inference('sup+', [status(thm)], ['10', '11'])).
% 1.06/1.27  thf('88', plain,
% 1.06/1.27      ((((k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (k1_relat_1 @ sk_C_1) @ 
% 1.06/1.27          (k2_funct_1 @ sk_C_1)) != (k2_relat_1 @ sk_C_1)))
% 1.06/1.27         <= (~
% 1.06/1.27             (((k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.27                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 1.06/1.27                 sk_C_1))
% 1.06/1.27                = (k2_struct_0 @ sk_B_1))))),
% 1.06/1.27      inference('demod', [status(thm)], ['2', '44', '45', '86', '87'])).
% 1.06/1.27  thf(t55_funct_1, axiom,
% 1.06/1.27    (![A:$i]:
% 1.06/1.27     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.06/1.27       ( ( v2_funct_1 @ A ) =>
% 1.06/1.27         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.06/1.27           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.06/1.27  thf('89', plain,
% 1.06/1.27      (![X14 : $i]:
% 1.06/1.27         (~ (v2_funct_1 @ X14)
% 1.06/1.27          | ((k1_relat_1 @ X14) = (k2_relat_1 @ (k2_funct_1 @ X14)))
% 1.06/1.27          | ~ (v1_funct_1 @ X14)
% 1.06/1.27          | ~ (v1_relat_1 @ X14))),
% 1.06/1.27      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.06/1.27  thf('90', plain,
% 1.06/1.27      ((m1_subset_1 @ sk_C_1 @ 
% 1.06/1.27        (k1_zfmisc_1 @ 
% 1.06/1.27         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1))))),
% 1.06/1.27      inference('demod', [status(thm)], ['51', '63'])).
% 1.06/1.27  thf(dt_k2_tops_2, axiom,
% 1.06/1.27    (![A:$i,B:$i,C:$i]:
% 1.06/1.27     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.06/1.27         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.06/1.27       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 1.06/1.27         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 1.06/1.27         ( m1_subset_1 @
% 1.06/1.27           ( k2_tops_2 @ A @ B @ C ) @ 
% 1.06/1.27           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 1.06/1.27  thf('91', plain,
% 1.06/1.27      (![X42 : $i, X43 : $i, X44 : $i]:
% 1.06/1.27         ((m1_subset_1 @ (k2_tops_2 @ X42 @ X43 @ X44) @ 
% 1.06/1.27           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42)))
% 1.06/1.27          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 1.06/1.27          | ~ (v1_funct_2 @ X44 @ X42 @ X43)
% 1.06/1.27          | ~ (v1_funct_1 @ X44))),
% 1.06/1.27      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 1.06/1.27  thf('92', plain,
% 1.06/1.27      ((~ (v1_funct_1 @ sk_C_1)
% 1.06/1.27        | ~ (v1_funct_2 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ 
% 1.06/1.27             (u1_struct_0 @ sk_B_1))
% 1.06/1.27        | (m1_subset_1 @ 
% 1.06/1.27           (k2_tops_2 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ sk_C_1) @ 
% 1.06/1.27           (k1_zfmisc_1 @ 
% 1.06/1.27            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (k1_relat_1 @ sk_C_1)))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['90', '91'])).
% 1.06/1.27  thf('93', plain, ((v1_funct_1 @ sk_C_1)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('94', plain,
% 1.06/1.27      ((v1_funct_2 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1))),
% 1.06/1.27      inference('demod', [status(thm)], ['72', '73'])).
% 1.06/1.27  thf('95', plain,
% 1.06/1.27      ((m1_subset_1 @ 
% 1.06/1.27        (k2_tops_2 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ sk_C_1) @ 
% 1.06/1.27        (k1_zfmisc_1 @ 
% 1.06/1.27         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (k1_relat_1 @ sk_C_1))))),
% 1.06/1.27      inference('demod', [status(thm)], ['92', '93', '94'])).
% 1.06/1.27  thf('96', plain,
% 1.06/1.27      (((k2_tops_2 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 1.06/1.27         = (k2_funct_1 @ sk_C_1))),
% 1.06/1.27      inference('simplify', [status(thm)], ['85'])).
% 1.06/1.27  thf('97', plain,
% 1.06/1.27      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.06/1.27        (k1_zfmisc_1 @ 
% 1.06/1.27         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (k1_relat_1 @ sk_C_1))))),
% 1.06/1.27      inference('demod', [status(thm)], ['95', '96'])).
% 1.06/1.27  thf('98', plain,
% 1.06/1.27      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.06/1.27         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 1.06/1.27          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 1.06/1.27      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.06/1.27  thf('99', plain,
% 1.06/1.27      (((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (k1_relat_1 @ sk_C_1) @ 
% 1.06/1.27         (k2_funct_1 @ sk_C_1)) = (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 1.06/1.27      inference('sup-', [status(thm)], ['97', '98'])).
% 1.06/1.27  thf('100', plain, (((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A))),
% 1.06/1.27      inference('demod', [status(thm)], ['58', '59', '62'])).
% 1.06/1.27  thf('101', plain,
% 1.06/1.27      (![X37 : $i]:
% 1.06/1.27         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 1.06/1.27      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.06/1.27  thf('102', plain,
% 1.06/1.27      (![X37 : $i]:
% 1.06/1.27         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 1.06/1.27      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.06/1.27  thf('103', plain,
% 1.06/1.27      ((((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.27          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1))
% 1.06/1.27          != (k2_struct_0 @ sk_A)))
% 1.06/1.27         <= (~
% 1.06/1.27             (((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.27                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 1.06/1.27                 sk_C_1))
% 1.06/1.27                = (k2_struct_0 @ sk_A))))),
% 1.06/1.27      inference('split', [status(esa)], ['1'])).
% 1.06/1.27  thf('104', plain,
% 1.06/1.27      (((((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.27           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1))
% 1.06/1.27           != (k2_struct_0 @ sk_A))
% 1.06/1.27         | ~ (l1_struct_0 @ sk_A)))
% 1.06/1.27         <= (~
% 1.06/1.27             (((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.27                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 1.06/1.27                 sk_C_1))
% 1.06/1.27                = (k2_struct_0 @ sk_A))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['102', '103'])).
% 1.06/1.27  thf('105', plain, ((l1_struct_0 @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('106', plain,
% 1.06/1.27      ((((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.27          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1))
% 1.06/1.27          != (k2_struct_0 @ sk_A)))
% 1.06/1.27         <= (~
% 1.06/1.27             (((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.27                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 1.06/1.27                 sk_C_1))
% 1.06/1.27                = (k2_struct_0 @ sk_A))))),
% 1.06/1.27      inference('demod', [status(thm)], ['104', '105'])).
% 1.06/1.27  thf('107', plain,
% 1.06/1.27      (((((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.27           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1) @ sk_C_1))
% 1.06/1.28           != (k2_struct_0 @ sk_A))
% 1.06/1.28         | ~ (l1_struct_0 @ sk_B_1)))
% 1.06/1.28         <= (~
% 1.06/1.28             (((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.28                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 1.06/1.28                 sk_C_1))
% 1.06/1.28                = (k2_struct_0 @ sk_A))))),
% 1.06/1.28      inference('sup-', [status(thm)], ['101', '106'])).
% 1.06/1.28  thf('108', plain, ((l1_struct_0 @ sk_B_1)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('109', plain,
% 1.06/1.28      ((((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.28          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1) @ sk_C_1))
% 1.06/1.28          != (k2_struct_0 @ sk_A)))
% 1.06/1.28         <= (~
% 1.06/1.28             (((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.28                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 1.06/1.28                 sk_C_1))
% 1.06/1.28                = (k2_struct_0 @ sk_A))))),
% 1.06/1.28      inference('demod', [status(thm)], ['107', '108'])).
% 1.06/1.28  thf('110', plain,
% 1.06/1.28      ((((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.28          (k2_tops_2 @ (k1_relat_1 @ sk_C_1) @ (k2_struct_0 @ sk_B_1) @ sk_C_1))
% 1.06/1.28          != (k2_struct_0 @ sk_A)))
% 1.06/1.28         <= (~
% 1.06/1.28             (((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.28                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 1.06/1.28                 sk_C_1))
% 1.06/1.28                = (k2_struct_0 @ sk_A))))),
% 1.06/1.28      inference('sup-', [status(thm)], ['100', '109'])).
% 1.06/1.28  thf('111', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_1))),
% 1.06/1.28      inference('sup+', [status(thm)], ['10', '11'])).
% 1.06/1.28  thf('112', plain, (((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A))),
% 1.06/1.28      inference('demod', [status(thm)], ['58', '59', '62'])).
% 1.06/1.28  thf('113', plain,
% 1.06/1.28      ((((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.28          (k2_tops_2 @ (k1_relat_1 @ sk_C_1) @ (k2_relat_1 @ sk_C_1) @ sk_C_1))
% 1.06/1.28          != (k1_relat_1 @ sk_C_1)))
% 1.06/1.28         <= (~
% 1.06/1.28             (((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.28                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 1.06/1.28                 sk_C_1))
% 1.06/1.28                = (k2_struct_0 @ sk_A))))),
% 1.06/1.28      inference('demod', [status(thm)], ['110', '111', '112'])).
% 1.06/1.28  thf('114', plain, (((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A))),
% 1.06/1.28      inference('demod', [status(thm)], ['37', '40', '43'])).
% 1.06/1.28  thf('115', plain,
% 1.06/1.28      (![X37 : $i]:
% 1.06/1.28         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 1.06/1.28      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.06/1.28  thf('116', plain,
% 1.06/1.28      ((m1_subset_1 @ sk_C_1 @ 
% 1.06/1.28        (k1_zfmisc_1 @ 
% 1.06/1.28         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 1.06/1.28      inference('demod', [status(thm)], ['49', '50'])).
% 1.06/1.28  thf('117', plain,
% 1.06/1.28      (((m1_subset_1 @ sk_C_1 @ 
% 1.06/1.28         (k1_zfmisc_1 @ 
% 1.06/1.28          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))))
% 1.06/1.28        | ~ (l1_struct_0 @ sk_B_1))),
% 1.06/1.28      inference('sup+', [status(thm)], ['115', '116'])).
% 1.06/1.28  thf('118', plain, ((l1_struct_0 @ sk_B_1)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('119', plain,
% 1.06/1.28      ((m1_subset_1 @ sk_C_1 @ 
% 1.06/1.28        (k1_zfmisc_1 @ 
% 1.06/1.28         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))))),
% 1.06/1.28      inference('demod', [status(thm)], ['117', '118'])).
% 1.06/1.28  thf('120', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_1))),
% 1.06/1.28      inference('sup+', [status(thm)], ['10', '11'])).
% 1.06/1.28  thf('121', plain,
% 1.06/1.28      ((m1_subset_1 @ sk_C_1 @ 
% 1.06/1.28        (k1_zfmisc_1 @ 
% 1.06/1.28         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1))))),
% 1.06/1.28      inference('demod', [status(thm)], ['119', '120'])).
% 1.06/1.28  thf('122', plain, (((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A))),
% 1.06/1.28      inference('demod', [status(thm)], ['58', '59', '62'])).
% 1.06/1.28  thf('123', plain,
% 1.06/1.28      ((m1_subset_1 @ sk_C_1 @ 
% 1.06/1.28        (k1_zfmisc_1 @ 
% 1.06/1.28         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ (k2_relat_1 @ sk_C_1))))),
% 1.06/1.28      inference('demod', [status(thm)], ['121', '122'])).
% 1.06/1.28  thf('124', plain,
% 1.06/1.28      (![X39 : $i, X40 : $i, X41 : $i]:
% 1.06/1.28         (((k2_relset_1 @ X40 @ X39 @ X41) != (X39))
% 1.06/1.28          | ~ (v2_funct_1 @ X41)
% 1.06/1.28          | ((k2_tops_2 @ X40 @ X39 @ X41) = (k2_funct_1 @ X41))
% 1.06/1.28          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39)))
% 1.06/1.28          | ~ (v1_funct_2 @ X41 @ X40 @ X39)
% 1.06/1.28          | ~ (v1_funct_1 @ X41))),
% 1.06/1.28      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.06/1.28  thf('125', plain,
% 1.06/1.28      ((~ (v1_funct_1 @ sk_C_1)
% 1.06/1.28        | ~ (v1_funct_2 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ 
% 1.06/1.28             (k2_relat_1 @ sk_C_1))
% 1.06/1.28        | ((k2_tops_2 @ (k1_relat_1 @ sk_C_1) @ (k2_relat_1 @ sk_C_1) @ sk_C_1)
% 1.06/1.28            = (k2_funct_1 @ sk_C_1))
% 1.06/1.28        | ~ (v2_funct_1 @ sk_C_1)
% 1.06/1.28        | ((k2_relset_1 @ (k1_relat_1 @ sk_C_1) @ (k2_relat_1 @ sk_C_1) @ 
% 1.06/1.28            sk_C_1) != (k2_relat_1 @ sk_C_1)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['123', '124'])).
% 1.06/1.28  thf('126', plain, ((v1_funct_1 @ sk_C_1)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('127', plain,
% 1.06/1.28      (![X37 : $i]:
% 1.06/1.28         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 1.06/1.28      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.06/1.28  thf('128', plain,
% 1.06/1.28      ((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 1.06/1.28      inference('demod', [status(thm)], ['70', '71'])).
% 1.06/1.28  thf('129', plain,
% 1.06/1.28      (((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))
% 1.06/1.28        | ~ (l1_struct_0 @ sk_B_1))),
% 1.06/1.28      inference('sup+', [status(thm)], ['127', '128'])).
% 1.06/1.28  thf('130', plain, ((l1_struct_0 @ sk_B_1)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('131', plain,
% 1.06/1.28      ((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))),
% 1.06/1.28      inference('demod', [status(thm)], ['129', '130'])).
% 1.06/1.28  thf('132', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_1))),
% 1.06/1.28      inference('sup+', [status(thm)], ['10', '11'])).
% 1.06/1.28  thf('133', plain,
% 1.06/1.28      ((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1))),
% 1.06/1.28      inference('demod', [status(thm)], ['131', '132'])).
% 1.06/1.28  thf('134', plain, (((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A))),
% 1.06/1.28      inference('demod', [status(thm)], ['58', '59', '62'])).
% 1.06/1.28  thf('135', plain,
% 1.06/1.28      ((v1_funct_2 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ (k2_relat_1 @ sk_C_1))),
% 1.06/1.28      inference('demod', [status(thm)], ['133', '134'])).
% 1.06/1.28  thf('136', plain, ((v2_funct_1 @ sk_C_1)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('137', plain,
% 1.06/1.28      (![X37 : $i]:
% 1.06/1.28         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 1.06/1.28      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.06/1.28  thf('138', plain,
% 1.06/1.28      (![X37 : $i]:
% 1.06/1.28         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 1.06/1.28      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.06/1.28  thf('139', plain,
% 1.06/1.28      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 1.06/1.28         = (k2_struct_0 @ sk_B_1))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('140', plain,
% 1.06/1.28      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 1.06/1.28          = (k2_struct_0 @ sk_B_1))
% 1.06/1.28        | ~ (l1_struct_0 @ sk_A))),
% 1.06/1.28      inference('sup+', [status(thm)], ['138', '139'])).
% 1.06/1.28  thf('141', plain, ((l1_struct_0 @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('142', plain,
% 1.06/1.28      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 1.06/1.28         = (k2_struct_0 @ sk_B_1))),
% 1.06/1.28      inference('demod', [status(thm)], ['140', '141'])).
% 1.06/1.28  thf('143', plain,
% 1.06/1.28      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1) @ sk_C_1)
% 1.06/1.28          = (k2_struct_0 @ sk_B_1))
% 1.06/1.28        | ~ (l1_struct_0 @ sk_B_1))),
% 1.06/1.28      inference('sup+', [status(thm)], ['137', '142'])).
% 1.06/1.28  thf('144', plain, ((l1_struct_0 @ sk_B_1)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('145', plain,
% 1.06/1.28      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1) @ sk_C_1)
% 1.06/1.28         = (k2_struct_0 @ sk_B_1))),
% 1.06/1.28      inference('demod', [status(thm)], ['143', '144'])).
% 1.06/1.28  thf('146', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_1))),
% 1.06/1.28      inference('sup+', [status(thm)], ['10', '11'])).
% 1.06/1.28  thf('147', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_1))),
% 1.06/1.28      inference('sup+', [status(thm)], ['10', '11'])).
% 1.06/1.28  thf('148', plain,
% 1.06/1.28      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1) @ sk_C_1)
% 1.06/1.28         = (k2_relat_1 @ sk_C_1))),
% 1.06/1.28      inference('demod', [status(thm)], ['145', '146', '147'])).
% 1.06/1.28  thf('149', plain, (((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A))),
% 1.06/1.28      inference('demod', [status(thm)], ['58', '59', '62'])).
% 1.06/1.28  thf('150', plain,
% 1.06/1.28      (((k2_relset_1 @ (k1_relat_1 @ sk_C_1) @ (k2_relat_1 @ sk_C_1) @ sk_C_1)
% 1.06/1.28         = (k2_relat_1 @ sk_C_1))),
% 1.06/1.28      inference('demod', [status(thm)], ['148', '149'])).
% 1.06/1.28  thf('151', plain,
% 1.06/1.28      ((((k2_tops_2 @ (k1_relat_1 @ sk_C_1) @ (k2_relat_1 @ sk_C_1) @ sk_C_1)
% 1.06/1.28          = (k2_funct_1 @ sk_C_1))
% 1.06/1.28        | ((k2_relat_1 @ sk_C_1) != (k2_relat_1 @ sk_C_1)))),
% 1.06/1.28      inference('demod', [status(thm)], ['125', '126', '135', '136', '150'])).
% 1.06/1.28  thf('152', plain,
% 1.06/1.28      (((k2_tops_2 @ (k1_relat_1 @ sk_C_1) @ (k2_relat_1 @ sk_C_1) @ sk_C_1)
% 1.06/1.28         = (k2_funct_1 @ sk_C_1))),
% 1.06/1.28      inference('simplify', [status(thm)], ['151'])).
% 1.06/1.28  thf('153', plain,
% 1.06/1.28      ((((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (k1_relat_1 @ sk_C_1) @ 
% 1.06/1.28          (k2_funct_1 @ sk_C_1)) != (k1_relat_1 @ sk_C_1)))
% 1.06/1.28         <= (~
% 1.06/1.28             (((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.28                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 1.06/1.28                 sk_C_1))
% 1.06/1.28                = (k2_struct_0 @ sk_A))))),
% 1.06/1.28      inference('demod', [status(thm)], ['113', '114', '152'])).
% 1.06/1.28  thf('154', plain,
% 1.06/1.28      ((((k2_relat_1 @ (k2_funct_1 @ sk_C_1)) != (k1_relat_1 @ sk_C_1)))
% 1.06/1.28         <= (~
% 1.06/1.28             (((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.28                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 1.06/1.28                 sk_C_1))
% 1.06/1.28                = (k2_struct_0 @ sk_A))))),
% 1.06/1.28      inference('sup-', [status(thm)], ['99', '153'])).
% 1.06/1.28  thf('155', plain,
% 1.06/1.28      (((((k1_relat_1 @ sk_C_1) != (k1_relat_1 @ sk_C_1))
% 1.06/1.28         | ~ (v1_relat_1 @ sk_C_1)
% 1.06/1.28         | ~ (v1_funct_1 @ sk_C_1)
% 1.06/1.28         | ~ (v2_funct_1 @ sk_C_1)))
% 1.06/1.28         <= (~
% 1.06/1.28             (((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.28                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 1.06/1.28                 sk_C_1))
% 1.06/1.28                = (k2_struct_0 @ sk_A))))),
% 1.06/1.28      inference('sup-', [status(thm)], ['89', '154'])).
% 1.06/1.28  thf('156', plain, ((v1_relat_1 @ sk_C_1)),
% 1.06/1.28      inference('sup-', [status(thm)], ['38', '39'])).
% 1.06/1.28  thf('157', plain, ((v1_funct_1 @ sk_C_1)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('158', plain, ((v2_funct_1 @ sk_C_1)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('159', plain,
% 1.06/1.28      ((((k1_relat_1 @ sk_C_1) != (k1_relat_1 @ sk_C_1)))
% 1.06/1.28         <= (~
% 1.06/1.28             (((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.28                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 1.06/1.28                 sk_C_1))
% 1.06/1.28                = (k2_struct_0 @ sk_A))))),
% 1.06/1.28      inference('demod', [status(thm)], ['155', '156', '157', '158'])).
% 1.06/1.28  thf('160', plain,
% 1.06/1.28      ((((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.28          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1))
% 1.06/1.28          = (k2_struct_0 @ sk_A)))),
% 1.06/1.28      inference('simplify', [status(thm)], ['159'])).
% 1.06/1.28  thf('161', plain,
% 1.06/1.28      (~
% 1.06/1.28       (((k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.28          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1))
% 1.06/1.28          = (k2_struct_0 @ sk_B_1))) | 
% 1.06/1.28       ~
% 1.06/1.28       (((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.28          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1))
% 1.06/1.28          = (k2_struct_0 @ sk_A)))),
% 1.06/1.28      inference('split', [status(esa)], ['1'])).
% 1.06/1.28  thf('162', plain,
% 1.06/1.28      (~
% 1.06/1.28       (((k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.28          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1))
% 1.06/1.28          = (k2_struct_0 @ sk_B_1)))),
% 1.06/1.28      inference('sat_resolution*', [status(thm)], ['160', '161'])).
% 1.06/1.28  thf('163', plain,
% 1.06/1.28      (((k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (k1_relat_1 @ sk_C_1) @ 
% 1.06/1.28         (k2_funct_1 @ sk_C_1)) != (k2_relat_1 @ sk_C_1))),
% 1.06/1.28      inference('simpl_trail', [status(thm)], ['88', '162'])).
% 1.06/1.28  thf('164', plain,
% 1.06/1.28      ((m1_subset_1 @ sk_C_1 @ 
% 1.06/1.28        (k1_zfmisc_1 @ 
% 1.06/1.28         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1))))),
% 1.06/1.28      inference('demod', [status(thm)], ['51', '63'])).
% 1.06/1.28  thf('165', plain,
% 1.06/1.28      (![X42 : $i, X43 : $i, X44 : $i]:
% 1.06/1.28         ((v1_funct_2 @ (k2_tops_2 @ X42 @ X43 @ X44) @ X43 @ X42)
% 1.06/1.28          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 1.06/1.28          | ~ (v1_funct_2 @ X44 @ X42 @ X43)
% 1.06/1.28          | ~ (v1_funct_1 @ X44))),
% 1.06/1.28      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 1.06/1.28  thf('166', plain,
% 1.06/1.28      ((~ (v1_funct_1 @ sk_C_1)
% 1.06/1.28        | ~ (v1_funct_2 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ 
% 1.06/1.28             (u1_struct_0 @ sk_B_1))
% 1.06/1.28        | (v1_funct_2 @ 
% 1.06/1.28           (k2_tops_2 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ sk_C_1) @ 
% 1.06/1.28           (u1_struct_0 @ sk_B_1) @ (k1_relat_1 @ sk_C_1)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['164', '165'])).
% 1.06/1.28  thf('167', plain, ((v1_funct_1 @ sk_C_1)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('168', plain,
% 1.06/1.28      ((v1_funct_2 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1))),
% 1.06/1.28      inference('demod', [status(thm)], ['72', '73'])).
% 1.06/1.28  thf('169', plain,
% 1.06/1.28      ((v1_funct_2 @ 
% 1.06/1.28        (k2_tops_2 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ sk_C_1) @ 
% 1.06/1.28        (u1_struct_0 @ sk_B_1) @ (k1_relat_1 @ sk_C_1))),
% 1.06/1.28      inference('demod', [status(thm)], ['166', '167', '168'])).
% 1.06/1.28  thf('170', plain,
% 1.06/1.28      (((k2_tops_2 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 1.06/1.28         = (k2_funct_1 @ sk_C_1))),
% 1.06/1.28      inference('simplify', [status(thm)], ['85'])).
% 1.06/1.28  thf('171', plain,
% 1.06/1.28      ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 1.06/1.28        (k1_relat_1 @ sk_C_1))),
% 1.06/1.28      inference('demod', [status(thm)], ['169', '170'])).
% 1.06/1.28  thf(d1_funct_2, axiom,
% 1.06/1.28    (![A:$i,B:$i,C:$i]:
% 1.06/1.28     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.06/1.28       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.06/1.28           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.06/1.28             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.06/1.28         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.06/1.28           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.06/1.28             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.06/1.28  thf(zf_stmt_1, axiom,
% 1.06/1.28    (![C:$i,B:$i,A:$i]:
% 1.06/1.28     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.06/1.28       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.06/1.28  thf('172', plain,
% 1.06/1.28      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.06/1.28         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 1.06/1.28          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 1.06/1.28          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.06/1.28  thf('173', plain,
% 1.06/1.28      ((~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C_1) @ (k1_relat_1 @ sk_C_1) @ 
% 1.06/1.28           (u1_struct_0 @ sk_B_1))
% 1.06/1.28        | ((u1_struct_0 @ sk_B_1)
% 1.06/1.28            = (k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (k1_relat_1 @ sk_C_1) @ 
% 1.06/1.28               (k2_funct_1 @ sk_C_1))))),
% 1.06/1.28      inference('sup-', [status(thm)], ['171', '172'])).
% 1.06/1.28  thf(zf_stmt_2, axiom,
% 1.06/1.28    (![B:$i,A:$i]:
% 1.06/1.28     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.06/1.28       ( zip_tseitin_0 @ B @ A ) ))).
% 1.06/1.28  thf('174', plain,
% 1.06/1.28      (![X27 : $i, X28 : $i]:
% 1.06/1.28         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.06/1.28  thf(t113_zfmisc_1, axiom,
% 1.06/1.28    (![A:$i,B:$i]:
% 1.06/1.28     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.06/1.28       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.06/1.28  thf('175', plain,
% 1.06/1.28      (![X8 : $i, X9 : $i]:
% 1.06/1.28         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 1.06/1.28      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.06/1.28  thf('176', plain,
% 1.06/1.28      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 1.06/1.28      inference('simplify', [status(thm)], ['175'])).
% 1.06/1.28  thf('177', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.28         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 1.06/1.28      inference('sup+', [status(thm)], ['174', '176'])).
% 1.06/1.28  thf(d1_xboole_0, axiom,
% 1.06/1.28    (![A:$i]:
% 1.06/1.28     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.06/1.28  thf('178', plain,
% 1.06/1.28      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.06/1.28      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.06/1.28  thf(t21_relat_1, axiom,
% 1.06/1.28    (![A:$i]:
% 1.06/1.28     ( ( v1_relat_1 @ A ) =>
% 1.06/1.28       ( r1_tarski @
% 1.06/1.28         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 1.06/1.28  thf('179', plain,
% 1.06/1.28      (![X13 : $i]:
% 1.06/1.28         ((r1_tarski @ X13 @ 
% 1.06/1.28           (k2_zfmisc_1 @ (k1_relat_1 @ X13) @ (k2_relat_1 @ X13)))
% 1.06/1.28          | ~ (v1_relat_1 @ X13))),
% 1.06/1.28      inference('cnf', [status(esa)], [t21_relat_1])).
% 1.06/1.28  thf(d3_tarski, axiom,
% 1.06/1.28    (![A:$i,B:$i]:
% 1.06/1.28     ( ( r1_tarski @ A @ B ) <=>
% 1.06/1.28       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.06/1.28  thf('180', plain,
% 1.06/1.28      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.06/1.28         (~ (r2_hidden @ X3 @ X4)
% 1.06/1.28          | (r2_hidden @ X3 @ X5)
% 1.06/1.28          | ~ (r1_tarski @ X4 @ X5))),
% 1.06/1.28      inference('cnf', [status(esa)], [d3_tarski])).
% 1.06/1.28  thf('181', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         (~ (v1_relat_1 @ X0)
% 1.06/1.28          | (r2_hidden @ X1 @ 
% 1.06/1.28             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 1.06/1.28          | ~ (r2_hidden @ X1 @ X0))),
% 1.06/1.28      inference('sup-', [status(thm)], ['179', '180'])).
% 1.06/1.28  thf('182', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         ((v1_xboole_0 @ X0)
% 1.06/1.28          | (r2_hidden @ (sk_B @ X0) @ 
% 1.06/1.28             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 1.06/1.28          | ~ (v1_relat_1 @ X0))),
% 1.06/1.28      inference('sup-', [status(thm)], ['178', '181'])).
% 1.06/1.28  thf('183', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.06/1.28      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.06/1.28  thf('184', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         (~ (v1_relat_1 @ X0)
% 1.06/1.28          | (v1_xboole_0 @ X0)
% 1.06/1.28          | ~ (v1_xboole_0 @ 
% 1.06/1.28               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 1.06/1.28      inference('sup-', [status(thm)], ['182', '183'])).
% 1.06/1.28  thf('185', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.06/1.28          | (zip_tseitin_0 @ (k1_relat_1 @ X0) @ X1)
% 1.06/1.28          | (v1_xboole_0 @ X0)
% 1.06/1.28          | ~ (v1_relat_1 @ X0))),
% 1.06/1.28      inference('sup-', [status(thm)], ['177', '184'])).
% 1.06/1.28  thf('186', plain,
% 1.06/1.28      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.06/1.28      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.06/1.28  thf('187', plain,
% 1.06/1.28      (![X8 : $i, X9 : $i]:
% 1.06/1.28         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 1.06/1.28      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.06/1.28  thf('188', plain,
% 1.06/1.28      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 1.06/1.28      inference('simplify', [status(thm)], ['187'])).
% 1.06/1.28  thf(t152_zfmisc_1, axiom,
% 1.06/1.28    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 1.06/1.28  thf('189', plain,
% 1.06/1.28      (![X10 : $i, X11 : $i]: ~ (r2_hidden @ X10 @ (k2_zfmisc_1 @ X10 @ X11))),
% 1.06/1.28      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 1.06/1.28  thf('190', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.06/1.28      inference('sup-', [status(thm)], ['188', '189'])).
% 1.06/1.28  thf('191', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.06/1.28      inference('sup-', [status(thm)], ['186', '190'])).
% 1.06/1.28  thf('192', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         ((zip_tseitin_0 @ (k1_relat_1 @ X0) @ X1)
% 1.06/1.28          | (v1_xboole_0 @ X0)
% 1.06/1.28          | ~ (v1_relat_1 @ X0))),
% 1.06/1.28      inference('demod', [status(thm)], ['185', '191'])).
% 1.06/1.28  thf('193', plain,
% 1.06/1.28      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 1.06/1.28        (k1_zfmisc_1 @ 
% 1.06/1.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (k1_relat_1 @ sk_C_1))))),
% 1.06/1.28      inference('demod', [status(thm)], ['95', '96'])).
% 1.06/1.28  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.06/1.28  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.06/1.28  thf(zf_stmt_5, axiom,
% 1.06/1.28    (![A:$i,B:$i,C:$i]:
% 1.06/1.28     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.06/1.28       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.06/1.28         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.06/1.28           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.06/1.28             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.06/1.28  thf('194', plain,
% 1.06/1.28      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.06/1.28         (~ (zip_tseitin_0 @ X32 @ X33)
% 1.06/1.28          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 1.06/1.28          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.06/1.28  thf('195', plain,
% 1.06/1.28      (((zip_tseitin_1 @ (k2_funct_1 @ sk_C_1) @ (k1_relat_1 @ sk_C_1) @ 
% 1.06/1.28         (u1_struct_0 @ sk_B_1))
% 1.06/1.28        | ~ (zip_tseitin_0 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['193', '194'])).
% 1.06/1.28  thf('196', plain,
% 1.06/1.28      ((~ (v1_relat_1 @ sk_C_1)
% 1.06/1.28        | (v1_xboole_0 @ sk_C_1)
% 1.06/1.28        | (zip_tseitin_1 @ (k2_funct_1 @ sk_C_1) @ (k1_relat_1 @ sk_C_1) @ 
% 1.06/1.28           (u1_struct_0 @ sk_B_1)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['192', '195'])).
% 1.06/1.28  thf('197', plain, ((v1_relat_1 @ sk_C_1)),
% 1.06/1.28      inference('sup-', [status(thm)], ['38', '39'])).
% 1.06/1.28  thf('198', plain,
% 1.06/1.28      (((v1_xboole_0 @ sk_C_1)
% 1.06/1.28        | (zip_tseitin_1 @ (k2_funct_1 @ sk_C_1) @ (k1_relat_1 @ sk_C_1) @ 
% 1.06/1.28           (u1_struct_0 @ sk_B_1)))),
% 1.06/1.28      inference('demod', [status(thm)], ['196', '197'])).
% 1.06/1.28  thf(fc11_relat_1, axiom,
% 1.06/1.28    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ))).
% 1.06/1.28  thf('199', plain,
% 1.06/1.28      (![X12 : $i]:
% 1.06/1.28         ((v1_xboole_0 @ (k2_relat_1 @ X12)) | ~ (v1_xboole_0 @ X12))),
% 1.06/1.28      inference('cnf', [status(esa)], [fc11_relat_1])).
% 1.06/1.28  thf('200', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_1))),
% 1.06/1.28      inference('clc', [status(thm)], ['32', '33'])).
% 1.06/1.28  thf('201', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 1.06/1.28      inference('sup-', [status(thm)], ['199', '200'])).
% 1.06/1.28  thf('202', plain,
% 1.06/1.28      ((zip_tseitin_1 @ (k2_funct_1 @ sk_C_1) @ (k1_relat_1 @ sk_C_1) @ 
% 1.06/1.28        (u1_struct_0 @ sk_B_1))),
% 1.06/1.28      inference('clc', [status(thm)], ['198', '201'])).
% 1.06/1.28  thf('203', plain,
% 1.06/1.28      (((u1_struct_0 @ sk_B_1)
% 1.06/1.28         = (k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (k1_relat_1 @ sk_C_1) @ 
% 1.06/1.28            (k2_funct_1 @ sk_C_1)))),
% 1.06/1.28      inference('demod', [status(thm)], ['173', '202'])).
% 1.06/1.28  thf('204', plain, (((u1_struct_0 @ sk_B_1) != (k2_relat_1 @ sk_C_1))),
% 1.06/1.28      inference('demod', [status(thm)], ['163', '203'])).
% 1.06/1.28  thf('205', plain,
% 1.06/1.28      ((((k2_struct_0 @ sk_B_1) != (k2_relat_1 @ sk_C_1))
% 1.06/1.28        | ~ (l1_struct_0 @ sk_B_1))),
% 1.06/1.28      inference('sup-', [status(thm)], ['0', '204'])).
% 1.06/1.28  thf('206', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_1))),
% 1.06/1.28      inference('sup+', [status(thm)], ['10', '11'])).
% 1.06/1.28  thf('207', plain, ((l1_struct_0 @ sk_B_1)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('208', plain, (((k2_relat_1 @ sk_C_1) != (k2_relat_1 @ sk_C_1))),
% 1.06/1.28      inference('demod', [status(thm)], ['205', '206', '207'])).
% 1.06/1.28  thf('209', plain, ($false), inference('simplify', [status(thm)], ['208'])).
% 1.06/1.28  
% 1.06/1.28  % SZS output end Refutation
% 1.06/1.28  
% 1.06/1.28  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
