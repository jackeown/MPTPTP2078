%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:17 EST 2020

% Result     : Theorem 9.55s
% Output     : CNFRefutation 9.55s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 465 expanded)
%              Number of leaves         :   50 ( 177 expanded)
%              Depth                    :   12
%              Number of atoms          :  309 (1355 expanded)
%              Number of equality atoms :   53 ( 117 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_183,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
             => ( v2_funct_1(C)
                & v2_funct_2(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_141,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_91,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_125,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_129,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_105,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_163,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_76,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_87,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_139,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_113,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_16,plain,(
    ! [A_7,B_8] :
      ( v1_xboole_0(k2_zfmisc_1(A_7,B_8))
      | ~ v1_xboole_0(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_271,plain,(
    ! [B_85,A_86] :
      ( v1_xboole_0(B_85)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_86))
      | ~ v1_xboole_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_289,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_72,c_271])).

tff(c_328,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_289])).

tff(c_343,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_328])).

tff(c_68,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_127,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_82,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_80,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_78,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_76,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_74,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_62,plain,(
    ! [A_48] : k6_relat_1(A_48) = k6_partfun1(A_48) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_38,plain,(
    ! [A_25] : v2_funct_1(k6_relat_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_83,plain,(
    ! [A_25] : v2_funct_1(k6_partfun1(A_25)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_38])).

tff(c_52,plain,(
    ! [A_35,F_40,B_36,C_37,D_38,E_39] :
      ( m1_subset_1(k1_partfun1(A_35,B_36,C_37,D_38,E_39,F_40),k1_zfmisc_1(k2_zfmisc_1(A_35,D_38)))
      | ~ m1_subset_1(F_40,k1_zfmisc_1(k2_zfmisc_1(C_37,D_38)))
      | ~ v1_funct_1(F_40)
      | ~ m1_subset_1(E_39,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36)))
      | ~ v1_funct_1(E_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_58,plain,(
    ! [A_41] : m1_subset_1(k6_partfun1(A_41),k1_zfmisc_1(k2_zfmisc_1(A_41,A_41))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_70,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_812,plain,(
    ! [D_126,C_127,A_128,B_129] :
      ( D_126 = C_127
      | ~ r2_relset_1(A_128,B_129,C_127,D_126)
      | ~ m1_subset_1(D_126,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129)))
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_822,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_70,c_812])).

tff(c_841,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_822])).

tff(c_991,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_841])).

tff(c_4221,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_991])).

tff(c_4225,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_76,c_72,c_4221])).

tff(c_4226,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_841])).

tff(c_6694,plain,(
    ! [C_360,B_361,D_363,A_362,E_359] :
      ( k1_xboole_0 = C_360
      | v2_funct_1(D_363)
      | ~ v2_funct_1(k1_partfun1(A_362,B_361,B_361,C_360,D_363,E_359))
      | ~ m1_subset_1(E_359,k1_zfmisc_1(k2_zfmisc_1(B_361,C_360)))
      | ~ v1_funct_2(E_359,B_361,C_360)
      | ~ v1_funct_1(E_359)
      | ~ m1_subset_1(D_363,k1_zfmisc_1(k2_zfmisc_1(A_362,B_361)))
      | ~ v1_funct_2(D_363,A_362,B_361)
      | ~ v1_funct_1(D_363) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_6696,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4226,c_6694])).

tff(c_6698,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_76,c_74,c_72,c_83,c_6696])).

tff(c_6699,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_6698])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_6747,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6699,c_2])).

tff(c_6749,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_343,c_6747])).

tff(c_6750,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_289])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_6764,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6750,c_4])).

tff(c_132,plain,(
    ! [A_69,B_70] :
      ( v1_xboole_0(k2_zfmisc_1(A_69,B_70))
      | ~ v1_xboole_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_148,plain,(
    ! [A_73,B_74] :
      ( k2_zfmisc_1(A_73,B_74) = k1_xboole_0
      | ~ v1_xboole_0(A_73) ) ),
    inference(resolution,[status(thm)],[c_132,c_4])).

tff(c_157,plain,(
    ! [B_74] : k2_zfmisc_1(k1_xboole_0,B_74) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_148])).

tff(c_176,plain,(
    ! [A_76] : m1_subset_1(k6_partfun1(A_76),k1_zfmisc_1(k2_zfmisc_1(A_76,A_76))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_180,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_176])).

tff(c_274,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_180,c_271])).

tff(c_286,plain,(
    v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_274])).

tff(c_302,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_286,c_4])).

tff(c_322,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_83])).

tff(c_6765,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6764,c_322])).

tff(c_6751,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_289])).

tff(c_14,plain,(
    ! [B_6,A_5] :
      ( ~ v1_xboole_0(B_6)
      | B_6 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6868,plain,(
    ! [A_372] :
      ( A_372 = '#skF_4'
      | ~ v1_xboole_0(A_372) ) ),
    inference(resolution,[status(thm)],[c_6750,c_14])).

tff(c_6881,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6751,c_6868])).

tff(c_6978,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6881,c_72])).

tff(c_7624,plain,(
    ! [D_426,C_427,A_428,B_429] :
      ( D_426 = C_427
      | ~ r2_relset_1(A_428,B_429,C_427,D_426)
      | ~ m1_subset_1(D_426,k1_zfmisc_1(k2_zfmisc_1(A_428,B_429)))
      | ~ m1_subset_1(C_427,k1_zfmisc_1(k2_zfmisc_1(A_428,B_429))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_7634,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_70,c_7624])).

tff(c_7653,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_7634])).

tff(c_7770,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_7653])).

tff(c_9496,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_7770])).

tff(c_9500,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_76,c_6978,c_6881,c_9496])).

tff(c_9501,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_7653])).

tff(c_66,plain,(
    ! [D_52,C_51,E_54,B_50,A_49] :
      ( k1_xboole_0 = C_51
      | v2_funct_1(D_52)
      | ~ v2_funct_1(k1_partfun1(A_49,B_50,B_50,C_51,D_52,E_54))
      | ~ m1_subset_1(E_54,k1_zfmisc_1(k2_zfmisc_1(B_50,C_51)))
      | ~ v1_funct_2(E_54,B_50,C_51)
      | ~ v1_funct_1(E_54)
      | ~ m1_subset_1(D_52,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50)))
      | ~ v1_funct_2(D_52,A_49,B_50)
      | ~ v1_funct_1(D_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_11598,plain,(
    ! [B_596,E_594,D_598,C_595,A_597] :
      ( C_595 = '#skF_4'
      | v2_funct_1(D_598)
      | ~ v2_funct_1(k1_partfun1(A_597,B_596,B_596,C_595,D_598,E_594))
      | ~ m1_subset_1(E_594,k1_zfmisc_1(k2_zfmisc_1(B_596,C_595)))
      | ~ v1_funct_2(E_594,B_596,C_595)
      | ~ v1_funct_1(E_594)
      | ~ m1_subset_1(D_598,k1_zfmisc_1(k2_zfmisc_1(A_597,B_596)))
      | ~ v1_funct_2(D_598,A_597,B_596)
      | ~ v1_funct_1(D_598) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6764,c_66])).

tff(c_11600,plain,
    ( '#skF_1' = '#skF_4'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_9501,c_11598])).

tff(c_11602,plain,
    ( '#skF_1' = '#skF_4'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_76,c_74,c_6978,c_6881,c_83,c_11600])).

tff(c_11603,plain,(
    '#skF_1' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_11602])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( v1_xboole_0(k2_zfmisc_1(A_9,B_10))
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_288,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_78,c_271])).

tff(c_6782,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_288])).

tff(c_6845,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_6782])).

tff(c_11615,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11603,c_6845])).

tff(c_11625,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6750,c_11615])).

tff(c_11626,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_288])).

tff(c_11694,plain,(
    ! [A_603] :
      ( A_603 = '#skF_3'
      | ~ v1_xboole_0(A_603) ) ),
    inference(resolution,[status(thm)],[c_11626,c_14])).

tff(c_11717,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6750,c_11694])).

tff(c_11725,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11717,c_127])).

tff(c_11732,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6765,c_11725])).

tff(c_11733,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_28,plain,(
    ! [A_19,B_20] : v1_relat_1(k2_zfmisc_1(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_11910,plain,(
    ! [B_622,A_623] :
      ( v1_relat_1(B_622)
      | ~ m1_subset_1(B_622,k1_zfmisc_1(A_623))
      | ~ v1_relat_1(A_623) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_11919,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_72,c_11910])).

tff(c_11928,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_11919])).

tff(c_11946,plain,(
    ! [C_624,B_625,A_626] :
      ( v5_relat_1(C_624,B_625)
      | ~ m1_subset_1(C_624,k1_zfmisc_1(k2_zfmisc_1(A_626,B_625))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_11964,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_11946])).

tff(c_26,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k2_relat_1(B_18),A_17)
      | ~ v5_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_11916,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_78,c_11910])).

tff(c_11925,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_11916])).

tff(c_34,plain,(
    ! [A_24] : k2_relat_1(k6_relat_1(A_24)) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_85,plain,(
    ! [A_24] : k2_relat_1(k6_partfun1(A_24)) = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_34])).

tff(c_12474,plain,(
    ! [D_665,C_666,A_667,B_668] :
      ( D_665 = C_666
      | ~ r2_relset_1(A_667,B_668,C_666,D_665)
      | ~ m1_subset_1(D_665,k1_zfmisc_1(k2_zfmisc_1(A_667,B_668)))
      | ~ m1_subset_1(C_666,k1_zfmisc_1(k2_zfmisc_1(A_667,B_668))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_12484,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_70,c_12474])).

tff(c_12503,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_12484])).

tff(c_12545,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_12503])).

tff(c_16162,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_12545])).

tff(c_16166,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_76,c_72,c_16162])).

tff(c_16167,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_12503])).

tff(c_16847,plain,(
    ! [F_838,D_835,B_836,E_834,C_839,A_837] :
      ( k1_partfun1(A_837,B_836,C_839,D_835,E_834,F_838) = k5_relat_1(E_834,F_838)
      | ~ m1_subset_1(F_838,k1_zfmisc_1(k2_zfmisc_1(C_839,D_835)))
      | ~ v1_funct_1(F_838)
      | ~ m1_subset_1(E_834,k1_zfmisc_1(k2_zfmisc_1(A_837,B_836)))
      | ~ v1_funct_1(E_834) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_16861,plain,(
    ! [A_837,B_836,E_834] :
      ( k1_partfun1(A_837,B_836,'#skF_2','#skF_1',E_834,'#skF_4') = k5_relat_1(E_834,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_834,k1_zfmisc_1(k2_zfmisc_1(A_837,B_836)))
      | ~ v1_funct_1(E_834) ) ),
    inference(resolution,[status(thm)],[c_72,c_16847])).

tff(c_18314,plain,(
    ! [A_891,B_892,E_893] :
      ( k1_partfun1(A_891,B_892,'#skF_2','#skF_1',E_893,'#skF_4') = k5_relat_1(E_893,'#skF_4')
      | ~ m1_subset_1(E_893,k1_zfmisc_1(k2_zfmisc_1(A_891,B_892)))
      | ~ v1_funct_1(E_893) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_16861])).

tff(c_18347,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_18314])).

tff(c_18355,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_16167,c_18347])).

tff(c_30,plain,(
    ! [A_21,B_23] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_21,B_23)),k2_relat_1(B_23))
      | ~ v1_relat_1(B_23)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_18362,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_1')),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18355,c_30])).

tff(c_18366,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11925,c_11928,c_85,c_18362])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( B_3 = A_2
      | ~ r1_tarski(B_3,A_2)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_18370,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_18366,c_6])).

tff(c_18371,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_18370])).

tff(c_18374,plain,
    ( ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_18371])).

tff(c_18378,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11928,c_11964,c_18374])).

tff(c_18379,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_18370])).

tff(c_10,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11992,plain,(
    ! [B_628,A_629] :
      ( v5_relat_1(B_628,A_629)
      | ~ r1_tarski(k2_relat_1(B_628),A_629)
      | ~ v1_relat_1(B_628) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_12007,plain,(
    ! [B_628] :
      ( v5_relat_1(B_628,k2_relat_1(B_628))
      | ~ v1_relat_1(B_628) ) ),
    inference(resolution,[status(thm)],[c_10,c_11992])).

tff(c_12117,plain,(
    ! [B_642] :
      ( v2_funct_2(B_642,k2_relat_1(B_642))
      | ~ v5_relat_1(B_642,k2_relat_1(B_642))
      | ~ v1_relat_1(B_642) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_12138,plain,(
    ! [B_628] :
      ( v2_funct_2(B_628,k2_relat_1(B_628))
      | ~ v1_relat_1(B_628) ) ),
    inference(resolution,[status(thm)],[c_12007,c_12117])).

tff(c_18389,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_18379,c_12138])).

tff(c_18404,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11928,c_18389])).

tff(c_18406,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11733,c_18404])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:04:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.55/3.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.55/3.34  
% 9.55/3.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.55/3.34  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.55/3.34  
% 9.55/3.34  %Foreground sorts:
% 9.55/3.34  
% 9.55/3.34  
% 9.55/3.34  %Background operators:
% 9.55/3.34  
% 9.55/3.34  
% 9.55/3.34  %Foreground operators:
% 9.55/3.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.55/3.34  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.55/3.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.55/3.34  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.55/3.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.55/3.34  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.55/3.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.55/3.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.55/3.34  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.55/3.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.55/3.34  tff('#skF_2', type, '#skF_2': $i).
% 9.55/3.34  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 9.55/3.34  tff('#skF_3', type, '#skF_3': $i).
% 9.55/3.34  tff('#skF_1', type, '#skF_1': $i).
% 9.55/3.34  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 9.55/3.34  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.55/3.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.55/3.34  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.55/3.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.55/3.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.55/3.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.55/3.34  tff('#skF_4', type, '#skF_4': $i).
% 9.55/3.34  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.55/3.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.55/3.34  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.55/3.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.55/3.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.55/3.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.55/3.34  
% 9.55/3.37  tff(f_50, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 9.55/3.37  tff(f_183, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 9.55/3.37  tff(f_61, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 9.55/3.37  tff(f_141, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 9.55/3.37  tff(f_91, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 9.55/3.37  tff(f_125, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 9.55/3.37  tff(f_129, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 9.55/3.37  tff(f_105, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 9.55/3.37  tff(f_163, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 9.55/3.37  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.55/3.37  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 9.55/3.37  tff(f_54, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 9.55/3.37  tff(f_46, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 9.55/3.37  tff(f_76, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.55/3.37  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.55/3.37  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.55/3.37  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 9.55/3.37  tff(f_87, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 9.55/3.37  tff(f_139, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 9.55/3.37  tff(f_83, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 9.55/3.37  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.55/3.37  tff(f_113, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 9.55/3.37  tff(c_16, plain, (![A_7, B_8]: (v1_xboole_0(k2_zfmisc_1(A_7, B_8)) | ~v1_xboole_0(B_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.55/3.37  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_183])).
% 9.55/3.37  tff(c_271, plain, (![B_85, A_86]: (v1_xboole_0(B_85) | ~m1_subset_1(B_85, k1_zfmisc_1(A_86)) | ~v1_xboole_0(A_86))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.55/3.37  tff(c_289, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_72, c_271])).
% 9.55/3.37  tff(c_328, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_289])).
% 9.55/3.37  tff(c_343, plain, (~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_328])).
% 9.55/3.37  tff(c_68, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 9.55/3.37  tff(c_127, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_68])).
% 9.55/3.37  tff(c_82, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 9.55/3.37  tff(c_80, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_183])).
% 9.55/3.37  tff(c_78, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_183])).
% 9.55/3.37  tff(c_76, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_183])).
% 9.55/3.37  tff(c_74, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_183])).
% 9.55/3.37  tff(c_62, plain, (![A_48]: (k6_relat_1(A_48)=k6_partfun1(A_48))), inference(cnfTransformation, [status(thm)], [f_141])).
% 9.55/3.37  tff(c_38, plain, (![A_25]: (v2_funct_1(k6_relat_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.55/3.37  tff(c_83, plain, (![A_25]: (v2_funct_1(k6_partfun1(A_25)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_38])).
% 9.55/3.37  tff(c_52, plain, (![A_35, F_40, B_36, C_37, D_38, E_39]: (m1_subset_1(k1_partfun1(A_35, B_36, C_37, D_38, E_39, F_40), k1_zfmisc_1(k2_zfmisc_1(A_35, D_38))) | ~m1_subset_1(F_40, k1_zfmisc_1(k2_zfmisc_1(C_37, D_38))) | ~v1_funct_1(F_40) | ~m1_subset_1(E_39, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))) | ~v1_funct_1(E_39))), inference(cnfTransformation, [status(thm)], [f_125])).
% 9.55/3.37  tff(c_58, plain, (![A_41]: (m1_subset_1(k6_partfun1(A_41), k1_zfmisc_1(k2_zfmisc_1(A_41, A_41))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 9.55/3.37  tff(c_70, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_183])).
% 9.55/3.37  tff(c_812, plain, (![D_126, C_127, A_128, B_129]: (D_126=C_127 | ~r2_relset_1(A_128, B_129, C_127, D_126) | ~m1_subset_1(D_126, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.55/3.37  tff(c_822, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_70, c_812])).
% 9.55/3.37  tff(c_841, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_822])).
% 9.55/3.37  tff(c_991, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_841])).
% 9.55/3.37  tff(c_4221, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_991])).
% 9.55/3.37  tff(c_4225, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_76, c_72, c_4221])).
% 9.55/3.37  tff(c_4226, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_841])).
% 9.55/3.37  tff(c_6694, plain, (![C_360, B_361, D_363, A_362, E_359]: (k1_xboole_0=C_360 | v2_funct_1(D_363) | ~v2_funct_1(k1_partfun1(A_362, B_361, B_361, C_360, D_363, E_359)) | ~m1_subset_1(E_359, k1_zfmisc_1(k2_zfmisc_1(B_361, C_360))) | ~v1_funct_2(E_359, B_361, C_360) | ~v1_funct_1(E_359) | ~m1_subset_1(D_363, k1_zfmisc_1(k2_zfmisc_1(A_362, B_361))) | ~v1_funct_2(D_363, A_362, B_361) | ~v1_funct_1(D_363))), inference(cnfTransformation, [status(thm)], [f_163])).
% 9.55/3.37  tff(c_6696, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4226, c_6694])).
% 9.55/3.37  tff(c_6698, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_76, c_74, c_72, c_83, c_6696])).
% 9.55/3.37  tff(c_6699, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_127, c_6698])).
% 9.55/3.37  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 9.55/3.37  tff(c_6747, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6699, c_2])).
% 9.55/3.37  tff(c_6749, plain, $false, inference(negUnitSimplification, [status(thm)], [c_343, c_6747])).
% 9.55/3.37  tff(c_6750, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_289])).
% 9.55/3.37  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 9.55/3.37  tff(c_6764, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_6750, c_4])).
% 9.55/3.37  tff(c_132, plain, (![A_69, B_70]: (v1_xboole_0(k2_zfmisc_1(A_69, B_70)) | ~v1_xboole_0(A_69))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.55/3.37  tff(c_148, plain, (![A_73, B_74]: (k2_zfmisc_1(A_73, B_74)=k1_xboole_0 | ~v1_xboole_0(A_73))), inference(resolution, [status(thm)], [c_132, c_4])).
% 9.55/3.37  tff(c_157, plain, (![B_74]: (k2_zfmisc_1(k1_xboole_0, B_74)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_148])).
% 9.55/3.37  tff(c_176, plain, (![A_76]: (m1_subset_1(k6_partfun1(A_76), k1_zfmisc_1(k2_zfmisc_1(A_76, A_76))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 9.55/3.37  tff(c_180, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_157, c_176])).
% 9.55/3.37  tff(c_274, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_180, c_271])).
% 9.55/3.37  tff(c_286, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_274])).
% 9.55/3.37  tff(c_302, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_286, c_4])).
% 9.55/3.37  tff(c_322, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_302, c_83])).
% 9.55/3.37  tff(c_6765, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6764, c_322])).
% 9.55/3.37  tff(c_6751, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_289])).
% 9.55/3.37  tff(c_14, plain, (![B_6, A_5]: (~v1_xboole_0(B_6) | B_6=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.55/3.37  tff(c_6868, plain, (![A_372]: (A_372='#skF_4' | ~v1_xboole_0(A_372))), inference(resolution, [status(thm)], [c_6750, c_14])).
% 9.55/3.37  tff(c_6881, plain, (k2_zfmisc_1('#skF_2', '#skF_1')='#skF_4'), inference(resolution, [status(thm)], [c_6751, c_6868])).
% 9.55/3.37  tff(c_6978, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6881, c_72])).
% 9.55/3.37  tff(c_7624, plain, (![D_426, C_427, A_428, B_429]: (D_426=C_427 | ~r2_relset_1(A_428, B_429, C_427, D_426) | ~m1_subset_1(D_426, k1_zfmisc_1(k2_zfmisc_1(A_428, B_429))) | ~m1_subset_1(C_427, k1_zfmisc_1(k2_zfmisc_1(A_428, B_429))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.55/3.37  tff(c_7634, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_70, c_7624])).
% 9.55/3.37  tff(c_7653, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_7634])).
% 9.55/3.37  tff(c_7770, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_7653])).
% 9.55/3.37  tff(c_9496, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_7770])).
% 9.55/3.37  tff(c_9500, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_76, c_6978, c_6881, c_9496])).
% 9.55/3.37  tff(c_9501, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_7653])).
% 9.55/3.37  tff(c_66, plain, (![D_52, C_51, E_54, B_50, A_49]: (k1_xboole_0=C_51 | v2_funct_1(D_52) | ~v2_funct_1(k1_partfun1(A_49, B_50, B_50, C_51, D_52, E_54)) | ~m1_subset_1(E_54, k1_zfmisc_1(k2_zfmisc_1(B_50, C_51))) | ~v1_funct_2(E_54, B_50, C_51) | ~v1_funct_1(E_54) | ~m1_subset_1(D_52, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))) | ~v1_funct_2(D_52, A_49, B_50) | ~v1_funct_1(D_52))), inference(cnfTransformation, [status(thm)], [f_163])).
% 9.55/3.37  tff(c_11598, plain, (![B_596, E_594, D_598, C_595, A_597]: (C_595='#skF_4' | v2_funct_1(D_598) | ~v2_funct_1(k1_partfun1(A_597, B_596, B_596, C_595, D_598, E_594)) | ~m1_subset_1(E_594, k1_zfmisc_1(k2_zfmisc_1(B_596, C_595))) | ~v1_funct_2(E_594, B_596, C_595) | ~v1_funct_1(E_594) | ~m1_subset_1(D_598, k1_zfmisc_1(k2_zfmisc_1(A_597, B_596))) | ~v1_funct_2(D_598, A_597, B_596) | ~v1_funct_1(D_598))), inference(demodulation, [status(thm), theory('equality')], [c_6764, c_66])).
% 9.55/3.37  tff(c_11600, plain, ('#skF_1'='#skF_4' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_9501, c_11598])).
% 9.55/3.37  tff(c_11602, plain, ('#skF_1'='#skF_4' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_76, c_74, c_6978, c_6881, c_83, c_11600])).
% 9.55/3.37  tff(c_11603, plain, ('#skF_1'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_127, c_11602])).
% 9.55/3.37  tff(c_18, plain, (![A_9, B_10]: (v1_xboole_0(k2_zfmisc_1(A_9, B_10)) | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.55/3.37  tff(c_288, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_78, c_271])).
% 9.55/3.37  tff(c_6782, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_288])).
% 9.55/3.37  tff(c_6845, plain, (~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_6782])).
% 9.55/3.37  tff(c_11615, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11603, c_6845])).
% 9.55/3.37  tff(c_11625, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6750, c_11615])).
% 9.55/3.37  tff(c_11626, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_288])).
% 9.55/3.37  tff(c_11694, plain, (![A_603]: (A_603='#skF_3' | ~v1_xboole_0(A_603))), inference(resolution, [status(thm)], [c_11626, c_14])).
% 9.55/3.37  tff(c_11717, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_6750, c_11694])).
% 9.55/3.37  tff(c_11725, plain, (~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11717, c_127])).
% 9.55/3.37  tff(c_11732, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6765, c_11725])).
% 9.55/3.37  tff(c_11733, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_68])).
% 9.55/3.37  tff(c_28, plain, (![A_19, B_20]: (v1_relat_1(k2_zfmisc_1(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.55/3.37  tff(c_11910, plain, (![B_622, A_623]: (v1_relat_1(B_622) | ~m1_subset_1(B_622, k1_zfmisc_1(A_623)) | ~v1_relat_1(A_623))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.55/3.37  tff(c_11919, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_72, c_11910])).
% 9.55/3.37  tff(c_11928, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_11919])).
% 9.55/3.37  tff(c_11946, plain, (![C_624, B_625, A_626]: (v5_relat_1(C_624, B_625) | ~m1_subset_1(C_624, k1_zfmisc_1(k2_zfmisc_1(A_626, B_625))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.55/3.37  tff(c_11964, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_72, c_11946])).
% 9.55/3.37  tff(c_26, plain, (![B_18, A_17]: (r1_tarski(k2_relat_1(B_18), A_17) | ~v5_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.55/3.37  tff(c_11916, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_78, c_11910])).
% 9.55/3.37  tff(c_11925, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_11916])).
% 9.55/3.37  tff(c_34, plain, (![A_24]: (k2_relat_1(k6_relat_1(A_24))=A_24)), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.55/3.37  tff(c_85, plain, (![A_24]: (k2_relat_1(k6_partfun1(A_24))=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_34])).
% 9.55/3.37  tff(c_12474, plain, (![D_665, C_666, A_667, B_668]: (D_665=C_666 | ~r2_relset_1(A_667, B_668, C_666, D_665) | ~m1_subset_1(D_665, k1_zfmisc_1(k2_zfmisc_1(A_667, B_668))) | ~m1_subset_1(C_666, k1_zfmisc_1(k2_zfmisc_1(A_667, B_668))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.55/3.37  tff(c_12484, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_70, c_12474])).
% 9.55/3.37  tff(c_12503, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_12484])).
% 9.55/3.37  tff(c_12545, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_12503])).
% 9.55/3.37  tff(c_16162, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_12545])).
% 9.55/3.37  tff(c_16166, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_76, c_72, c_16162])).
% 9.55/3.37  tff(c_16167, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_12503])).
% 9.55/3.37  tff(c_16847, plain, (![F_838, D_835, B_836, E_834, C_839, A_837]: (k1_partfun1(A_837, B_836, C_839, D_835, E_834, F_838)=k5_relat_1(E_834, F_838) | ~m1_subset_1(F_838, k1_zfmisc_1(k2_zfmisc_1(C_839, D_835))) | ~v1_funct_1(F_838) | ~m1_subset_1(E_834, k1_zfmisc_1(k2_zfmisc_1(A_837, B_836))) | ~v1_funct_1(E_834))), inference(cnfTransformation, [status(thm)], [f_139])).
% 9.55/3.37  tff(c_16861, plain, (![A_837, B_836, E_834]: (k1_partfun1(A_837, B_836, '#skF_2', '#skF_1', E_834, '#skF_4')=k5_relat_1(E_834, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_834, k1_zfmisc_1(k2_zfmisc_1(A_837, B_836))) | ~v1_funct_1(E_834))), inference(resolution, [status(thm)], [c_72, c_16847])).
% 9.55/3.37  tff(c_18314, plain, (![A_891, B_892, E_893]: (k1_partfun1(A_891, B_892, '#skF_2', '#skF_1', E_893, '#skF_4')=k5_relat_1(E_893, '#skF_4') | ~m1_subset_1(E_893, k1_zfmisc_1(k2_zfmisc_1(A_891, B_892))) | ~v1_funct_1(E_893))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_16861])).
% 9.55/3.37  tff(c_18347, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_18314])).
% 9.55/3.37  tff(c_18355, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_16167, c_18347])).
% 9.55/3.37  tff(c_30, plain, (![A_21, B_23]: (r1_tarski(k2_relat_1(k5_relat_1(A_21, B_23)), k2_relat_1(B_23)) | ~v1_relat_1(B_23) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.55/3.37  tff(c_18362, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_1')), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18355, c_30])).
% 9.55/3.37  tff(c_18366, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_11925, c_11928, c_85, c_18362])).
% 9.55/3.37  tff(c_6, plain, (![B_3, A_2]: (B_3=A_2 | ~r1_tarski(B_3, A_2) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.55/3.37  tff(c_18370, plain, (k2_relat_1('#skF_4')='#skF_1' | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(resolution, [status(thm)], [c_18366, c_6])).
% 9.55/3.37  tff(c_18371, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(splitLeft, [status(thm)], [c_18370])).
% 9.55/3.37  tff(c_18374, plain, (~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_18371])).
% 9.55/3.37  tff(c_18378, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11928, c_11964, c_18374])).
% 9.55/3.37  tff(c_18379, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_18370])).
% 9.55/3.37  tff(c_10, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.55/3.37  tff(c_11992, plain, (![B_628, A_629]: (v5_relat_1(B_628, A_629) | ~r1_tarski(k2_relat_1(B_628), A_629) | ~v1_relat_1(B_628))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.55/3.37  tff(c_12007, plain, (![B_628]: (v5_relat_1(B_628, k2_relat_1(B_628)) | ~v1_relat_1(B_628))), inference(resolution, [status(thm)], [c_10, c_11992])).
% 9.55/3.37  tff(c_12117, plain, (![B_642]: (v2_funct_2(B_642, k2_relat_1(B_642)) | ~v5_relat_1(B_642, k2_relat_1(B_642)) | ~v1_relat_1(B_642))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.55/3.37  tff(c_12138, plain, (![B_628]: (v2_funct_2(B_628, k2_relat_1(B_628)) | ~v1_relat_1(B_628))), inference(resolution, [status(thm)], [c_12007, c_12117])).
% 9.55/3.37  tff(c_18389, plain, (v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_18379, c_12138])).
% 9.55/3.37  tff(c_18404, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11928, c_18389])).
% 9.55/3.37  tff(c_18406, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11733, c_18404])).
% 9.55/3.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.55/3.37  
% 9.55/3.37  Inference rules
% 9.55/3.37  ----------------------
% 9.55/3.37  #Ref     : 0
% 9.55/3.37  #Sup     : 4563
% 9.55/3.37  #Fact    : 0
% 9.55/3.37  #Define  : 0
% 9.55/3.37  #Split   : 18
% 9.55/3.37  #Chain   : 0
% 9.55/3.37  #Close   : 0
% 9.55/3.37  
% 9.55/3.37  Ordering : KBO
% 9.55/3.37  
% 9.55/3.37  Simplification rules
% 9.55/3.37  ----------------------
% 9.55/3.37  #Subsume      : 349
% 9.55/3.37  #Demod        : 4081
% 9.55/3.37  #Tautology    : 2897
% 9.55/3.37  #SimpNegUnit  : 4
% 9.55/3.37  #BackRed      : 99
% 9.55/3.37  
% 9.55/3.37  #Partial instantiations: 0
% 9.55/3.37  #Strategies tried      : 1
% 9.55/3.37  
% 9.55/3.37  Timing (in seconds)
% 9.55/3.37  ----------------------
% 9.55/3.37  Preprocessing        : 0.41
% 9.55/3.37  Parsing              : 0.22
% 9.55/3.37  CNF conversion       : 0.03
% 9.55/3.37  Main loop            : 2.19
% 9.55/3.37  Inferencing          : 0.61
% 9.55/3.37  Reduction            : 0.82
% 9.55/3.37  Demodulation         : 0.60
% 9.55/3.37  BG Simplification    : 0.08
% 9.55/3.37  Subsumption          : 0.52
% 9.55/3.37  Abstraction          : 0.09
% 9.55/3.37  MUC search           : 0.00
% 9.55/3.37  Cooper               : 0.00
% 9.55/3.37  Total                : 2.65
% 9.55/3.37  Index Insertion      : 0.00
% 9.55/3.37  Index Deletion       : 0.00
% 9.55/3.37  Index Matching       : 0.00
% 9.55/3.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
