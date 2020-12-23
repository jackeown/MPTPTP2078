%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:33 EST 2020

% Result     : Theorem 5.05s
% Output     : CNFRefutation 5.05s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 281 expanded)
%              Number of leaves         :   38 ( 114 expanded)
%              Depth                    :   12
%              Number of atoms          :  160 ( 662 expanded)
%              Number of equality atoms :   37 ( 146 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_47,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_114,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( r2_hidden(C,k2_relset_1(A,B,D))
            & ! [E] :
                ~ ( r2_hidden(E,A)
                  & k1_funct_1(D,E) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_2)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(E,k1_relat_1(A))
                  & r2_hidden(E,B)
                  & D = k1_funct_1(A,E) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_12,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_62,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_80,plain,(
    ! [B_78,A_79] :
      ( v1_relat_1(B_78)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_79))
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_86,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_62,c_80])).

tff(c_90,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_86])).

tff(c_66,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_64,plain,(
    v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_156,plain,(
    ! [A_93,B_94,C_95] :
      ( k1_relset_1(A_93,B_94,C_95) = k1_relat_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_165,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_62,c_156])).

tff(c_3070,plain,(
    ! [B_381,A_382,C_383] :
      ( k1_xboole_0 = B_381
      | k1_relset_1(A_382,B_381,C_383) = A_382
      | ~ v1_funct_2(C_383,A_382,B_381)
      | ~ m1_subset_1(C_383,k1_zfmisc_1(k2_zfmisc_1(A_382,B_381))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3089,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_3070])).

tff(c_3096,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_165,c_3089])).

tff(c_3097,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_3096])).

tff(c_14,plain,(
    ! [A_13] :
      ( k9_relat_1(A_13,k1_relat_1(A_13)) = k2_relat_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3102,plain,
    ( k9_relat_1('#skF_8','#skF_5') = k2_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_3097,c_14])).

tff(c_3106,plain,(
    k9_relat_1('#skF_8','#skF_5') = k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_3102])).

tff(c_3322,plain,(
    ! [A_407,B_408,D_409] :
      ( k1_funct_1(A_407,'#skF_4'(A_407,B_408,k9_relat_1(A_407,B_408),D_409)) = D_409
      | ~ r2_hidden(D_409,k9_relat_1(A_407,B_408))
      | ~ v1_funct_1(A_407)
      | ~ v1_relat_1(A_407) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_3170,plain,(
    ! [A_390,B_391,D_392] :
      ( r2_hidden('#skF_4'(A_390,B_391,k9_relat_1(A_390,B_391),D_392),B_391)
      | ~ r2_hidden(D_392,k9_relat_1(A_390,B_391))
      | ~ v1_funct_1(A_390)
      | ~ v1_relat_1(A_390) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_58,plain,(
    ! [E_69] :
      ( k1_funct_1('#skF_8',E_69) != '#skF_7'
      | ~ r2_hidden(E_69,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_3184,plain,(
    ! [A_390,D_392] :
      ( k1_funct_1('#skF_8','#skF_4'(A_390,'#skF_5',k9_relat_1(A_390,'#skF_5'),D_392)) != '#skF_7'
      | ~ r2_hidden(D_392,k9_relat_1(A_390,'#skF_5'))
      | ~ v1_funct_1(A_390)
      | ~ v1_relat_1(A_390) ) ),
    inference(resolution,[status(thm)],[c_3170,c_58])).

tff(c_3329,plain,(
    ! [D_409] :
      ( D_409 != '#skF_7'
      | ~ r2_hidden(D_409,k9_relat_1('#skF_8','#skF_5'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_409,k9_relat_1('#skF_8','#skF_5'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3322,c_3184])).

tff(c_3354,plain,(
    ~ r2_hidden('#skF_7',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_66,c_3106,c_90,c_66,c_3106,c_3329])).

tff(c_129,plain,(
    ! [A_88,B_89,C_90] :
      ( k2_relset_1(A_88,B_89,C_90) = k2_relat_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_138,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_62,c_129])).

tff(c_60,plain,(
    r2_hidden('#skF_7',k2_relset_1('#skF_5','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_141,plain,(
    r2_hidden('#skF_7',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_60])).

tff(c_3356,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3354,c_141])).

tff(c_3357,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_3096])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_3378,plain,(
    ! [A_1] : r1_tarski('#skF_6',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3357,c_2])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_170,plain,(
    ! [A_96,B_97,A_98] :
      ( k2_relset_1(A_96,B_97,A_98) = k2_relat_1(A_98)
      | ~ r1_tarski(A_98,k2_zfmisc_1(A_96,B_97)) ) ),
    inference(resolution,[status(thm)],[c_8,c_129])).

tff(c_180,plain,(
    ! [A_96,B_97] : k2_relset_1(A_96,B_97,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_170])).

tff(c_214,plain,(
    ! [A_108,B_109,C_110] :
      ( m1_subset_1(k2_relset_1(A_108,B_109,C_110),k1_zfmisc_1(B_109))
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2839,plain,(
    ! [B_365,A_366] :
      ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(B_365))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_366,B_365))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_214])).

tff(c_2842,plain,(
    ! [B_365,A_366] :
      ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(B_365))
      | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(A_366,B_365)) ) ),
    inference(resolution,[status(thm)],[c_8,c_2839])).

tff(c_2847,plain,(
    ! [B_367] : m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(B_367)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2842])).

tff(c_234,plain,
    ( m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_6'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_214])).

tff(c_240,plain,(
    m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_234])).

tff(c_118,plain,(
    ! [C_83,A_84,B_85] :
      ( r2_hidden(C_83,A_84)
      | ~ r2_hidden(C_83,B_85)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_121,plain,(
    ! [A_84] :
      ( r2_hidden('#skF_7',A_84)
      | ~ m1_subset_1(k2_relset_1('#skF_5','#skF_6','#skF_8'),k1_zfmisc_1(A_84)) ) ),
    inference(resolution,[status(thm)],[c_60,c_118])).

tff(c_140,plain,(
    ! [A_84] :
      ( r2_hidden('#skF_7',A_84)
      | ~ m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1(A_84)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_121])).

tff(c_261,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_240,c_140])).

tff(c_4,plain,(
    ! [C_5,A_2,B_3] :
      ( r2_hidden(C_5,A_2)
      | ~ r2_hidden(C_5,B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_937,plain,(
    ! [A_181] :
      ( r2_hidden('#skF_7',A_181)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_181)) ) ),
    inference(resolution,[status(thm)],[c_261,c_4])).

tff(c_945,plain,(
    ! [B_182] :
      ( r2_hidden('#skF_7',B_182)
      | ~ r1_tarski('#skF_6',B_182) ) ),
    inference(resolution,[status(thm)],[c_8,c_937])).

tff(c_952,plain,(
    ! [A_2,B_182] :
      ( r2_hidden('#skF_7',A_2)
      | ~ m1_subset_1(B_182,k1_zfmisc_1(A_2))
      | ~ r1_tarski('#skF_6',B_182) ) ),
    inference(resolution,[status(thm)],[c_945,c_4])).

tff(c_2882,plain,(
    ! [B_367] :
      ( r2_hidden('#skF_7',B_367)
      | ~ r1_tarski('#skF_6',k2_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_2847,c_952])).

tff(c_2931,plain,(
    ~ r1_tarski('#skF_6',k2_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_2882])).

tff(c_3366,plain,(
    ~ r1_tarski('#skF_6',k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3357,c_2931])).

tff(c_3459,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3378,c_3366])).

tff(c_3460,plain,(
    ! [B_367] : r2_hidden('#skF_7',B_367) ),
    inference(splitRight,[status(thm)],[c_2882])).

tff(c_4242,plain,(
    ! [A_503,B_504,D_505] :
      ( k1_funct_1(A_503,'#skF_4'(A_503,B_504,k9_relat_1(A_503,B_504),D_505)) = D_505
      | ~ r2_hidden(D_505,k9_relat_1(A_503,B_504))
      | ~ v1_funct_1(A_503)
      | ~ v1_relat_1(A_503) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4135,plain,(
    ! [A_481,B_482,D_483] :
      ( r2_hidden('#skF_4'(A_481,B_482,k9_relat_1(A_481,B_482),D_483),B_482)
      | ~ r2_hidden(D_483,k9_relat_1(A_481,B_482))
      | ~ v1_funct_1(A_481)
      | ~ v1_relat_1(A_481) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4146,plain,(
    ! [A_481,D_483] :
      ( k1_funct_1('#skF_8','#skF_4'(A_481,'#skF_5',k9_relat_1(A_481,'#skF_5'),D_483)) != '#skF_7'
      | ~ r2_hidden(D_483,k9_relat_1(A_481,'#skF_5'))
      | ~ v1_funct_1(A_481)
      | ~ v1_relat_1(A_481) ) ),
    inference(resolution,[status(thm)],[c_4135,c_58])).

tff(c_4252,plain,(
    ! [D_505] :
      ( D_505 != '#skF_7'
      | ~ r2_hidden(D_505,k9_relat_1('#skF_8','#skF_5'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_505,k9_relat_1('#skF_8','#skF_5'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4242,c_4146])).

tff(c_4264,plain,(
    ! [D_506] :
      ( D_506 != '#skF_7'
      | ~ r2_hidden(D_506,k9_relat_1('#skF_8','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_66,c_90,c_66,c_4252])).

tff(c_4282,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_3460,c_4264])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:54:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.05/1.92  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.05/1.93  
% 5.05/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.05/1.93  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 5.05/1.93  
% 5.05/1.93  %Foreground sorts:
% 5.05/1.93  
% 5.05/1.93  
% 5.05/1.93  %Background operators:
% 5.05/1.93  
% 5.05/1.93  
% 5.05/1.93  %Foreground operators:
% 5.05/1.93  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.05/1.93  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.05/1.93  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.05/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.05/1.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.05/1.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.05/1.93  tff('#skF_7', type, '#skF_7': $i).
% 5.05/1.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.05/1.93  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.05/1.93  tff('#skF_5', type, '#skF_5': $i).
% 5.05/1.93  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.05/1.93  tff('#skF_6', type, '#skF_6': $i).
% 5.05/1.93  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.05/1.93  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.05/1.93  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.05/1.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.05/1.93  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.05/1.93  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 5.05/1.93  tff('#skF_8', type, '#skF_8': $i).
% 5.05/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.05/1.93  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.05/1.93  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.05/1.93  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.05/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.05/1.93  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.05/1.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.05/1.93  
% 5.05/1.95  tff(f_47, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.05/1.95  tff(f_114, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r2_hidden(C, k2_relset_1(A, B, D)) & (![E]: ~(r2_hidden(E, A) & (k1_funct_1(D, E) = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_funct_2)).
% 5.05/1.95  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.05/1.95  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.05/1.95  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.05/1.95  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 5.05/1.95  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_1)).
% 5.05/1.95  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.05/1.95  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.05/1.95  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.05/1.95  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 5.05/1.95  tff(f_34, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 5.05/1.95  tff(c_12, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.05/1.95  tff(c_62, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.05/1.95  tff(c_80, plain, (![B_78, A_79]: (v1_relat_1(B_78) | ~m1_subset_1(B_78, k1_zfmisc_1(A_79)) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.05/1.95  tff(c_86, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_62, c_80])).
% 5.05/1.95  tff(c_90, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_86])).
% 5.05/1.95  tff(c_66, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.05/1.95  tff(c_64, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.05/1.95  tff(c_156, plain, (![A_93, B_94, C_95]: (k1_relset_1(A_93, B_94, C_95)=k1_relat_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.05/1.95  tff(c_165, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_62, c_156])).
% 5.05/1.95  tff(c_3070, plain, (![B_381, A_382, C_383]: (k1_xboole_0=B_381 | k1_relset_1(A_382, B_381, C_383)=A_382 | ~v1_funct_2(C_383, A_382, B_381) | ~m1_subset_1(C_383, k1_zfmisc_1(k2_zfmisc_1(A_382, B_381))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.05/1.95  tff(c_3089, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_62, c_3070])).
% 5.05/1.95  tff(c_3096, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_165, c_3089])).
% 5.05/1.95  tff(c_3097, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_3096])).
% 5.05/1.95  tff(c_14, plain, (![A_13]: (k9_relat_1(A_13, k1_relat_1(A_13))=k2_relat_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.05/1.95  tff(c_3102, plain, (k9_relat_1('#skF_8', '#skF_5')=k2_relat_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_3097, c_14])).
% 5.05/1.95  tff(c_3106, plain, (k9_relat_1('#skF_8', '#skF_5')=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_3102])).
% 5.05/1.95  tff(c_3322, plain, (![A_407, B_408, D_409]: (k1_funct_1(A_407, '#skF_4'(A_407, B_408, k9_relat_1(A_407, B_408), D_409))=D_409 | ~r2_hidden(D_409, k9_relat_1(A_407, B_408)) | ~v1_funct_1(A_407) | ~v1_relat_1(A_407))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.05/1.95  tff(c_3170, plain, (![A_390, B_391, D_392]: (r2_hidden('#skF_4'(A_390, B_391, k9_relat_1(A_390, B_391), D_392), B_391) | ~r2_hidden(D_392, k9_relat_1(A_390, B_391)) | ~v1_funct_1(A_390) | ~v1_relat_1(A_390))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.05/1.95  tff(c_58, plain, (![E_69]: (k1_funct_1('#skF_8', E_69)!='#skF_7' | ~r2_hidden(E_69, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.05/1.95  tff(c_3184, plain, (![A_390, D_392]: (k1_funct_1('#skF_8', '#skF_4'(A_390, '#skF_5', k9_relat_1(A_390, '#skF_5'), D_392))!='#skF_7' | ~r2_hidden(D_392, k9_relat_1(A_390, '#skF_5')) | ~v1_funct_1(A_390) | ~v1_relat_1(A_390))), inference(resolution, [status(thm)], [c_3170, c_58])).
% 5.05/1.95  tff(c_3329, plain, (![D_409]: (D_409!='#skF_7' | ~r2_hidden(D_409, k9_relat_1('#skF_8', '#skF_5')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_409, k9_relat_1('#skF_8', '#skF_5')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_3322, c_3184])).
% 5.05/1.95  tff(c_3354, plain, (~r2_hidden('#skF_7', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_66, c_3106, c_90, c_66, c_3106, c_3329])).
% 5.05/1.95  tff(c_129, plain, (![A_88, B_89, C_90]: (k2_relset_1(A_88, B_89, C_90)=k2_relat_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.05/1.95  tff(c_138, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_62, c_129])).
% 5.05/1.95  tff(c_60, plain, (r2_hidden('#skF_7', k2_relset_1('#skF_5', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.05/1.95  tff(c_141, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_60])).
% 5.05/1.95  tff(c_3356, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3354, c_141])).
% 5.05/1.95  tff(c_3357, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_3096])).
% 5.05/1.95  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.05/1.95  tff(c_3378, plain, (![A_1]: (r1_tarski('#skF_6', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_3357, c_2])).
% 5.05/1.95  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.05/1.95  tff(c_170, plain, (![A_96, B_97, A_98]: (k2_relset_1(A_96, B_97, A_98)=k2_relat_1(A_98) | ~r1_tarski(A_98, k2_zfmisc_1(A_96, B_97)))), inference(resolution, [status(thm)], [c_8, c_129])).
% 5.05/1.95  tff(c_180, plain, (![A_96, B_97]: (k2_relset_1(A_96, B_97, k1_xboole_0)=k2_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_170])).
% 5.05/1.95  tff(c_214, plain, (![A_108, B_109, C_110]: (m1_subset_1(k2_relset_1(A_108, B_109, C_110), k1_zfmisc_1(B_109)) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.05/1.95  tff(c_2839, plain, (![B_365, A_366]: (m1_subset_1(k2_relat_1(k1_xboole_0), k1_zfmisc_1(B_365)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_366, B_365))))), inference(superposition, [status(thm), theory('equality')], [c_180, c_214])).
% 5.05/1.95  tff(c_2842, plain, (![B_365, A_366]: (m1_subset_1(k2_relat_1(k1_xboole_0), k1_zfmisc_1(B_365)) | ~r1_tarski(k1_xboole_0, k2_zfmisc_1(A_366, B_365)))), inference(resolution, [status(thm)], [c_8, c_2839])).
% 5.05/1.95  tff(c_2847, plain, (![B_367]: (m1_subset_1(k2_relat_1(k1_xboole_0), k1_zfmisc_1(B_367)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2842])).
% 5.05/1.95  tff(c_234, plain, (m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1('#skF_6')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_138, c_214])).
% 5.05/1.95  tff(c_240, plain, (m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_234])).
% 5.05/1.95  tff(c_118, plain, (![C_83, A_84, B_85]: (r2_hidden(C_83, A_84) | ~r2_hidden(C_83, B_85) | ~m1_subset_1(B_85, k1_zfmisc_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.05/1.95  tff(c_121, plain, (![A_84]: (r2_hidden('#skF_7', A_84) | ~m1_subset_1(k2_relset_1('#skF_5', '#skF_6', '#skF_8'), k1_zfmisc_1(A_84)))), inference(resolution, [status(thm)], [c_60, c_118])).
% 5.05/1.95  tff(c_140, plain, (![A_84]: (r2_hidden('#skF_7', A_84) | ~m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1(A_84)))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_121])).
% 5.05/1.95  tff(c_261, plain, (r2_hidden('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_240, c_140])).
% 5.05/1.95  tff(c_4, plain, (![C_5, A_2, B_3]: (r2_hidden(C_5, A_2) | ~r2_hidden(C_5, B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.05/1.95  tff(c_937, plain, (![A_181]: (r2_hidden('#skF_7', A_181) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_181)))), inference(resolution, [status(thm)], [c_261, c_4])).
% 5.05/1.95  tff(c_945, plain, (![B_182]: (r2_hidden('#skF_7', B_182) | ~r1_tarski('#skF_6', B_182))), inference(resolution, [status(thm)], [c_8, c_937])).
% 5.05/1.95  tff(c_952, plain, (![A_2, B_182]: (r2_hidden('#skF_7', A_2) | ~m1_subset_1(B_182, k1_zfmisc_1(A_2)) | ~r1_tarski('#skF_6', B_182))), inference(resolution, [status(thm)], [c_945, c_4])).
% 5.05/1.95  tff(c_2882, plain, (![B_367]: (r2_hidden('#skF_7', B_367) | ~r1_tarski('#skF_6', k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_2847, c_952])).
% 5.05/1.95  tff(c_2931, plain, (~r1_tarski('#skF_6', k2_relat_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_2882])).
% 5.05/1.95  tff(c_3366, plain, (~r1_tarski('#skF_6', k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_3357, c_2931])).
% 5.05/1.95  tff(c_3459, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3378, c_3366])).
% 5.05/1.95  tff(c_3460, plain, (![B_367]: (r2_hidden('#skF_7', B_367))), inference(splitRight, [status(thm)], [c_2882])).
% 5.05/1.95  tff(c_4242, plain, (![A_503, B_504, D_505]: (k1_funct_1(A_503, '#skF_4'(A_503, B_504, k9_relat_1(A_503, B_504), D_505))=D_505 | ~r2_hidden(D_505, k9_relat_1(A_503, B_504)) | ~v1_funct_1(A_503) | ~v1_relat_1(A_503))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.05/1.95  tff(c_4135, plain, (![A_481, B_482, D_483]: (r2_hidden('#skF_4'(A_481, B_482, k9_relat_1(A_481, B_482), D_483), B_482) | ~r2_hidden(D_483, k9_relat_1(A_481, B_482)) | ~v1_funct_1(A_481) | ~v1_relat_1(A_481))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.05/1.95  tff(c_4146, plain, (![A_481, D_483]: (k1_funct_1('#skF_8', '#skF_4'(A_481, '#skF_5', k9_relat_1(A_481, '#skF_5'), D_483))!='#skF_7' | ~r2_hidden(D_483, k9_relat_1(A_481, '#skF_5')) | ~v1_funct_1(A_481) | ~v1_relat_1(A_481))), inference(resolution, [status(thm)], [c_4135, c_58])).
% 5.05/1.95  tff(c_4252, plain, (![D_505]: (D_505!='#skF_7' | ~r2_hidden(D_505, k9_relat_1('#skF_8', '#skF_5')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_505, k9_relat_1('#skF_8', '#skF_5')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_4242, c_4146])).
% 5.05/1.95  tff(c_4264, plain, (![D_506]: (D_506!='#skF_7' | ~r2_hidden(D_506, k9_relat_1('#skF_8', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_66, c_90, c_66, c_4252])).
% 5.05/1.95  tff(c_4282, plain, $false, inference(resolution, [status(thm)], [c_3460, c_4264])).
% 5.05/1.95  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.05/1.95  
% 5.05/1.95  Inference rules
% 5.05/1.95  ----------------------
% 5.05/1.95  #Ref     : 0
% 5.05/1.95  #Sup     : 768
% 5.05/1.95  #Fact    : 0
% 5.05/1.95  #Define  : 0
% 5.05/1.95  #Split   : 60
% 5.05/1.95  #Chain   : 0
% 5.05/1.95  #Close   : 0
% 5.05/1.95  
% 5.05/1.95  Ordering : KBO
% 5.05/1.95  
% 5.05/1.95  Simplification rules
% 5.05/1.95  ----------------------
% 5.05/1.95  #Subsume      : 99
% 5.05/1.95  #Demod        : 1001
% 5.05/1.95  #Tautology    : 380
% 5.05/1.95  #SimpNegUnit  : 104
% 5.05/1.95  #BackRed      : 273
% 5.05/1.95  
% 5.05/1.95  #Partial instantiations: 0
% 5.05/1.95  #Strategies tried      : 1
% 5.05/1.95  
% 5.05/1.95  Timing (in seconds)
% 5.05/1.95  ----------------------
% 5.05/1.95  Preprocessing        : 0.33
% 5.05/1.95  Parsing              : 0.16
% 5.05/1.95  CNF conversion       : 0.03
% 5.05/1.95  Main loop            : 0.85
% 5.05/1.95  Inferencing          : 0.28
% 5.05/1.95  Reduction            : 0.29
% 5.05/1.95  Demodulation         : 0.21
% 5.05/1.95  BG Simplification    : 0.04
% 5.05/1.95  Subsumption          : 0.15
% 5.05/1.95  Abstraction          : 0.04
% 5.05/1.95  MUC search           : 0.00
% 5.05/1.95  Cooper               : 0.00
% 5.05/1.95  Total                : 1.21
% 5.05/1.95  Index Insertion      : 0.00
% 5.05/1.95  Index Deletion       : 0.00
% 5.05/1.96  Index Matching       : 0.00
% 5.05/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
