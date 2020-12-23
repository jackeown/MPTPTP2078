%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:31 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 368 expanded)
%              Number of leaves         :   45 ( 146 expanded)
%              Depth                    :   12
%              Number of atoms          :  151 ( 929 expanded)
%              Number of equality atoms :   49 ( 275 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > r2_hidden > m1_subset_1 > v5_ordinal1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_11 > #skF_9 > #skF_3 > #skF_10 > #skF_8 > #skF_13 > #skF_2 > #skF_7 > #skF_5 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_155,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( r2_hidden(C,k2_relset_1(A,B,D))
            & ! [E] :
                ~ ( r2_hidden(E,A)
                  & k1_funct_1(D,E) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_2)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_139,axiom,(
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

tff(f_108,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_121,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
     => ~ ( r2_hidden(A,D)
          & ! [E,F] :
              ~ ( A = k4_tarski(E,F)
                & r2_hidden(E,B)
                & r2_hidden(F,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_relset_1)).

tff(f_54,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_1287,plain,(
    ! [A_249,B_250,C_251] :
      ( r2_hidden('#skF_1'(A_249,B_250,C_251),A_249)
      | r2_hidden('#skF_2'(A_249,B_250,C_251),C_251)
      | k4_xboole_0(A_249,B_250) = C_251 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1344,plain,(
    ! [A_252,C_253] :
      ( r2_hidden('#skF_2'(A_252,A_252,C_253),C_253)
      | k4_xboole_0(A_252,A_252) = C_253 ) ),
    inference(resolution,[status(thm)],[c_1287,c_16])).

tff(c_92,plain,(
    m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1('#skF_10','#skF_11'))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_122,plain,(
    ! [C_82,A_83,B_84] :
      ( v1_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_126,plain,(
    v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_92,c_122])).

tff(c_96,plain,(
    v1_funct_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_38,plain,(
    ! [A_13,C_49] :
      ( k1_funct_1(A_13,'#skF_7'(A_13,k2_relat_1(A_13),C_49)) = C_49
      | ~ r2_hidden(C_49,k2_relat_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_94,plain,(
    v1_funct_2('#skF_13','#skF_10','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_230,plain,(
    ! [A_114,B_115,C_116] :
      ( k1_relset_1(A_114,B_115,C_116) = k1_relat_1(C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_239,plain,(
    k1_relset_1('#skF_10','#skF_11','#skF_13') = k1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_92,c_230])).

tff(c_745,plain,(
    ! [B_185,A_186,C_187] :
      ( k1_xboole_0 = B_185
      | k1_relset_1(A_186,B_185,C_187) = A_186
      | ~ v1_funct_2(C_187,A_186,B_185)
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(A_186,B_185))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_752,plain,
    ( k1_xboole_0 = '#skF_11'
    | k1_relset_1('#skF_10','#skF_11','#skF_13') = '#skF_10'
    | ~ v1_funct_2('#skF_13','#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_92,c_745])).

tff(c_756,plain,
    ( k1_xboole_0 = '#skF_11'
    | k1_relat_1('#skF_13') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_239,c_752])).

tff(c_757,plain,(
    k1_relat_1('#skF_13') = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_756])).

tff(c_40,plain,(
    ! [A_13,C_49] :
      ( r2_hidden('#skF_7'(A_13,k2_relat_1(A_13),C_49),k1_relat_1(A_13))
      | ~ r2_hidden(C_49,k2_relat_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_762,plain,(
    ! [C_49] :
      ( r2_hidden('#skF_7'('#skF_13',k2_relat_1('#skF_13'),C_49),'#skF_10')
      | ~ r2_hidden(C_49,k2_relat_1('#skF_13'))
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_757,c_40])).

tff(c_778,plain,(
    ! [C_190] :
      ( r2_hidden('#skF_7'('#skF_13',k2_relat_1('#skF_13'),C_190),'#skF_10')
      | ~ r2_hidden(C_190,k2_relat_1('#skF_13')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_96,c_762])).

tff(c_88,plain,(
    ! [E_77] :
      ( k1_funct_1('#skF_13',E_77) != '#skF_12'
      | ~ r2_hidden(E_77,'#skF_10') ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_783,plain,(
    ! [C_191] :
      ( k1_funct_1('#skF_13','#skF_7'('#skF_13',k2_relat_1('#skF_13'),C_191)) != '#skF_12'
      | ~ r2_hidden(C_191,k2_relat_1('#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_778,c_88])).

tff(c_787,plain,(
    ! [C_49] :
      ( C_49 != '#skF_12'
      | ~ r2_hidden(C_49,k2_relat_1('#skF_13'))
      | ~ r2_hidden(C_49,k2_relat_1('#skF_13'))
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_783])).

tff(c_790,plain,(
    ~ r2_hidden('#skF_12',k2_relat_1('#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_96,c_787])).

tff(c_240,plain,(
    ! [A_117,B_118,C_119] :
      ( k2_relset_1(A_117,B_118,C_119) = k2_relat_1(C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_249,plain,(
    k2_relset_1('#skF_10','#skF_11','#skF_13') = k2_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_92,c_240])).

tff(c_90,plain,(
    r2_hidden('#skF_12',k2_relset_1('#skF_10','#skF_11','#skF_13')) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_254,plain,(
    r2_hidden('#skF_12',k2_relat_1('#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_90])).

tff(c_792,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_790,c_254])).

tff(c_793,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_756])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(k1_tarski(A_7),B_8) = k1_xboole_0
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_152,plain,(
    ! [D_87,A_88,B_89] :
      ( r2_hidden(D_87,A_88)
      | ~ r2_hidden(D_87,k4_xboole_0(A_88,B_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_176,plain,(
    ! [D_100,A_101,B_102] :
      ( r2_hidden(D_100,k1_tarski(A_101))
      | ~ r2_hidden(D_100,k1_xboole_0)
      | ~ r2_hidden(A_101,B_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_152])).

tff(c_180,plain,(
    ! [D_103] :
      ( r2_hidden(D_103,k1_tarski('#skF_12'))
      | ~ r2_hidden(D_103,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_90,c_176])).

tff(c_156,plain,(
    ! [D_90,B_91,A_92] :
      ( ~ r2_hidden(D_90,B_91)
      | ~ r2_hidden(D_90,k4_xboole_0(A_92,B_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_159,plain,(
    ! [D_90,B_8,A_7] :
      ( ~ r2_hidden(D_90,B_8)
      | ~ r2_hidden(D_90,k1_xboole_0)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_156])).

tff(c_186,plain,(
    ! [A_7,D_103] :
      ( ~ r2_hidden(A_7,k1_tarski('#skF_12'))
      | ~ r2_hidden(D_103,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_180,c_159])).

tff(c_187,plain,(
    ! [D_103] : ~ r2_hidden(D_103,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_812,plain,(
    ! [D_103] : ~ r2_hidden(D_103,'#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_793,c_187])).

tff(c_314,plain,(
    ! [A_137,B_138,C_139,D_140] :
      ( r2_hidden('#skF_9'(A_137,B_138,C_139,D_140),C_139)
      | ~ r2_hidden(A_137,D_140)
      | ~ m1_subset_1(D_140,k1_zfmisc_1(k2_zfmisc_1(B_138,C_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_321,plain,(
    ! [A_137] :
      ( r2_hidden('#skF_9'(A_137,'#skF_10','#skF_11','#skF_13'),'#skF_11')
      | ~ r2_hidden(A_137,'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_92,c_314])).

tff(c_882,plain,(
    ! [A_137] : ~ r2_hidden(A_137,'#skF_13') ),
    inference(negUnitSimplification,[status(thm)],[c_812,c_321])).

tff(c_336,plain,(
    ! [A_144,B_145,C_146] :
      ( r2_hidden('#skF_1'(A_144,B_145,C_146),A_144)
      | r2_hidden('#skF_2'(A_144,B_145,C_146),C_146)
      | k4_xboole_0(A_144,B_145) = C_146 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_388,plain,(
    ! [A_147,C_148] :
      ( r2_hidden('#skF_2'(A_147,A_147,C_148),C_148)
      | k4_xboole_0(A_147,A_147) = C_148 ) ),
    inference(resolution,[status(thm)],[c_336,c_16])).

tff(c_409,plain,(
    ! [A_147] : k4_xboole_0(A_147,A_147) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_388,c_187])).

tff(c_1007,plain,(
    ! [A_205] : k4_xboole_0(A_205,A_205) = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_793,c_409])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_379,plain,(
    ! [A_144,B_145] :
      ( r2_hidden('#skF_2'(A_144,B_145,A_144),A_144)
      | k4_xboole_0(A_144,B_145) = A_144 ) ),
    inference(resolution,[status(thm)],[c_336,c_14])).

tff(c_906,plain,(
    ! [A_198] : ~ r2_hidden(A_198,'#skF_13') ),
    inference(negUnitSimplification,[status(thm)],[c_812,c_321])).

tff(c_927,plain,(
    ! [B_145] : k4_xboole_0('#skF_13',B_145) = '#skF_13' ),
    inference(resolution,[status(thm)],[c_379,c_906])).

tff(c_1015,plain,(
    '#skF_11' = '#skF_13' ),
    inference(superposition,[status(thm),theory(equality)],[c_1007,c_927])).

tff(c_28,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_822,plain,(
    k2_relat_1('#skF_11') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_793,c_793,c_28])).

tff(c_1058,plain,(
    k2_relat_1('#skF_13') = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1015,c_1015,c_822])).

tff(c_1115,plain,(
    r2_hidden('#skF_12','#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1058,c_254])).

tff(c_1117,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_882,c_1115])).

tff(c_1118,plain,(
    ! [A_7] : ~ r2_hidden(A_7,k1_tarski('#skF_12')) ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_179,plain,(
    ! [D_100] :
      ( r2_hidden(D_100,k1_tarski('#skF_12'))
      | ~ r2_hidden(D_100,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_90,c_176])).

tff(c_1119,plain,(
    ! [D_100] : ~ r2_hidden(D_100,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_1118,c_179])).

tff(c_1375,plain,(
    ! [A_254] : k4_xboole_0(A_254,A_254) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1344,c_1119])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | k4_xboole_0(k1_tarski(A_7),B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1407,plain,(
    ! [A_255] : r2_hidden(A_255,k1_tarski(A_255)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1375,c_20])).

tff(c_1415,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_1407,c_1118])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n016.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 19:07:19 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.36/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.62  
% 3.77/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.62  %$ v1_funct_2 > v5_relat_1 > r2_hidden > m1_subset_1 > v5_ordinal1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_11 > #skF_9 > #skF_3 > #skF_10 > #skF_8 > #skF_13 > #skF_2 > #skF_7 > #skF_5 > #skF_12 > #skF_4
% 3.77/1.62  
% 3.77/1.62  %Foreground sorts:
% 3.77/1.62  
% 3.77/1.62  
% 3.77/1.62  %Background operators:
% 3.77/1.62  
% 3.77/1.62  
% 3.77/1.62  %Foreground operators:
% 3.77/1.62  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.77/1.62  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.77/1.62  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.77/1.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.77/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.77/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.77/1.62  tff('#skF_11', type, '#skF_11': $i).
% 3.77/1.62  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.77/1.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.77/1.62  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.77/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.77/1.62  tff('#skF_9', type, '#skF_9': ($i * $i * $i * $i) > $i).
% 3.77/1.62  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.77/1.62  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.77/1.62  tff('#skF_10', type, '#skF_10': $i).
% 3.77/1.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.77/1.62  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 3.77/1.62  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 3.77/1.62  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.77/1.62  tff('#skF_13', type, '#skF_13': $i).
% 3.77/1.62  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.77/1.62  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.77/1.62  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.77/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.77/1.62  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 3.77/1.62  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.77/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.77/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.77/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.77/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.77/1.62  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.77/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.77/1.62  tff('#skF_12', type, '#skF_12': $i).
% 3.77/1.62  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.77/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.77/1.62  
% 3.77/1.64  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.77/1.64  tff(f_155, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r2_hidden(C, k2_relset_1(A, B, D)) & (![E]: ~(r2_hidden(E, A) & (k1_funct_1(D, E) = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_funct_2)).
% 3.77/1.64  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.77/1.64  tff(f_75, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 3.77/1.64  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.77/1.64  tff(f_139, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.77/1.64  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.77/1.64  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 3.77/1.64  tff(f_121, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => ~(r2_hidden(A, D) & (![E, F]: ~(((A = k4_tarski(E, F)) & r2_hidden(E, B)) & r2_hidden(F, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_relset_1)).
% 3.77/1.64  tff(f_54, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.77/1.64  tff(c_1287, plain, (![A_249, B_250, C_251]: (r2_hidden('#skF_1'(A_249, B_250, C_251), A_249) | r2_hidden('#skF_2'(A_249, B_250, C_251), C_251) | k4_xboole_0(A_249, B_250)=C_251)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.77/1.64  tff(c_16, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.77/1.64  tff(c_1344, plain, (![A_252, C_253]: (r2_hidden('#skF_2'(A_252, A_252, C_253), C_253) | k4_xboole_0(A_252, A_252)=C_253)), inference(resolution, [status(thm)], [c_1287, c_16])).
% 3.77/1.64  tff(c_92, plain, (m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1('#skF_10', '#skF_11')))), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.77/1.64  tff(c_122, plain, (![C_82, A_83, B_84]: (v1_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.77/1.64  tff(c_126, plain, (v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_92, c_122])).
% 3.77/1.64  tff(c_96, plain, (v1_funct_1('#skF_13')), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.77/1.64  tff(c_38, plain, (![A_13, C_49]: (k1_funct_1(A_13, '#skF_7'(A_13, k2_relat_1(A_13), C_49))=C_49 | ~r2_hidden(C_49, k2_relat_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.77/1.64  tff(c_94, plain, (v1_funct_2('#skF_13', '#skF_10', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.77/1.64  tff(c_230, plain, (![A_114, B_115, C_116]: (k1_relset_1(A_114, B_115, C_116)=k1_relat_1(C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.77/1.64  tff(c_239, plain, (k1_relset_1('#skF_10', '#skF_11', '#skF_13')=k1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_92, c_230])).
% 3.77/1.64  tff(c_745, plain, (![B_185, A_186, C_187]: (k1_xboole_0=B_185 | k1_relset_1(A_186, B_185, C_187)=A_186 | ~v1_funct_2(C_187, A_186, B_185) | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(A_186, B_185))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.77/1.64  tff(c_752, plain, (k1_xboole_0='#skF_11' | k1_relset_1('#skF_10', '#skF_11', '#skF_13')='#skF_10' | ~v1_funct_2('#skF_13', '#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_92, c_745])).
% 3.77/1.64  tff(c_756, plain, (k1_xboole_0='#skF_11' | k1_relat_1('#skF_13')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_239, c_752])).
% 3.77/1.64  tff(c_757, plain, (k1_relat_1('#skF_13')='#skF_10'), inference(splitLeft, [status(thm)], [c_756])).
% 3.77/1.64  tff(c_40, plain, (![A_13, C_49]: (r2_hidden('#skF_7'(A_13, k2_relat_1(A_13), C_49), k1_relat_1(A_13)) | ~r2_hidden(C_49, k2_relat_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.77/1.64  tff(c_762, plain, (![C_49]: (r2_hidden('#skF_7'('#skF_13', k2_relat_1('#skF_13'), C_49), '#skF_10') | ~r2_hidden(C_49, k2_relat_1('#skF_13')) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_757, c_40])).
% 3.77/1.64  tff(c_778, plain, (![C_190]: (r2_hidden('#skF_7'('#skF_13', k2_relat_1('#skF_13'), C_190), '#skF_10') | ~r2_hidden(C_190, k2_relat_1('#skF_13')))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_96, c_762])).
% 3.77/1.64  tff(c_88, plain, (![E_77]: (k1_funct_1('#skF_13', E_77)!='#skF_12' | ~r2_hidden(E_77, '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.77/1.64  tff(c_783, plain, (![C_191]: (k1_funct_1('#skF_13', '#skF_7'('#skF_13', k2_relat_1('#skF_13'), C_191))!='#skF_12' | ~r2_hidden(C_191, k2_relat_1('#skF_13')))), inference(resolution, [status(thm)], [c_778, c_88])).
% 3.77/1.64  tff(c_787, plain, (![C_49]: (C_49!='#skF_12' | ~r2_hidden(C_49, k2_relat_1('#skF_13')) | ~r2_hidden(C_49, k2_relat_1('#skF_13')) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_783])).
% 3.77/1.64  tff(c_790, plain, (~r2_hidden('#skF_12', k2_relat_1('#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_96, c_787])).
% 3.77/1.64  tff(c_240, plain, (![A_117, B_118, C_119]: (k2_relset_1(A_117, B_118, C_119)=k2_relat_1(C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.77/1.64  tff(c_249, plain, (k2_relset_1('#skF_10', '#skF_11', '#skF_13')=k2_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_92, c_240])).
% 3.77/1.64  tff(c_90, plain, (r2_hidden('#skF_12', k2_relset_1('#skF_10', '#skF_11', '#skF_13'))), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.77/1.64  tff(c_254, plain, (r2_hidden('#skF_12', k2_relat_1('#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_249, c_90])).
% 3.77/1.64  tff(c_792, plain, $false, inference(negUnitSimplification, [status(thm)], [c_790, c_254])).
% 3.77/1.64  tff(c_793, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_756])).
% 3.77/1.64  tff(c_22, plain, (![A_7, B_8]: (k4_xboole_0(k1_tarski(A_7), B_8)=k1_xboole_0 | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.77/1.64  tff(c_152, plain, (![D_87, A_88, B_89]: (r2_hidden(D_87, A_88) | ~r2_hidden(D_87, k4_xboole_0(A_88, B_89)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.77/1.64  tff(c_176, plain, (![D_100, A_101, B_102]: (r2_hidden(D_100, k1_tarski(A_101)) | ~r2_hidden(D_100, k1_xboole_0) | ~r2_hidden(A_101, B_102))), inference(superposition, [status(thm), theory('equality')], [c_22, c_152])).
% 3.77/1.64  tff(c_180, plain, (![D_103]: (r2_hidden(D_103, k1_tarski('#skF_12')) | ~r2_hidden(D_103, k1_xboole_0))), inference(resolution, [status(thm)], [c_90, c_176])).
% 3.77/1.64  tff(c_156, plain, (![D_90, B_91, A_92]: (~r2_hidden(D_90, B_91) | ~r2_hidden(D_90, k4_xboole_0(A_92, B_91)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.77/1.64  tff(c_159, plain, (![D_90, B_8, A_7]: (~r2_hidden(D_90, B_8) | ~r2_hidden(D_90, k1_xboole_0) | ~r2_hidden(A_7, B_8))), inference(superposition, [status(thm), theory('equality')], [c_22, c_156])).
% 3.77/1.64  tff(c_186, plain, (![A_7, D_103]: (~r2_hidden(A_7, k1_tarski('#skF_12')) | ~r2_hidden(D_103, k1_xboole_0))), inference(resolution, [status(thm)], [c_180, c_159])).
% 3.77/1.64  tff(c_187, plain, (![D_103]: (~r2_hidden(D_103, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_186])).
% 3.77/1.64  tff(c_812, plain, (![D_103]: (~r2_hidden(D_103, '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_793, c_187])).
% 3.77/1.64  tff(c_314, plain, (![A_137, B_138, C_139, D_140]: (r2_hidden('#skF_9'(A_137, B_138, C_139, D_140), C_139) | ~r2_hidden(A_137, D_140) | ~m1_subset_1(D_140, k1_zfmisc_1(k2_zfmisc_1(B_138, C_139))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.77/1.64  tff(c_321, plain, (![A_137]: (r2_hidden('#skF_9'(A_137, '#skF_10', '#skF_11', '#skF_13'), '#skF_11') | ~r2_hidden(A_137, '#skF_13'))), inference(resolution, [status(thm)], [c_92, c_314])).
% 3.77/1.64  tff(c_882, plain, (![A_137]: (~r2_hidden(A_137, '#skF_13'))), inference(negUnitSimplification, [status(thm)], [c_812, c_321])).
% 3.77/1.64  tff(c_336, plain, (![A_144, B_145, C_146]: (r2_hidden('#skF_1'(A_144, B_145, C_146), A_144) | r2_hidden('#skF_2'(A_144, B_145, C_146), C_146) | k4_xboole_0(A_144, B_145)=C_146)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.77/1.64  tff(c_388, plain, (![A_147, C_148]: (r2_hidden('#skF_2'(A_147, A_147, C_148), C_148) | k4_xboole_0(A_147, A_147)=C_148)), inference(resolution, [status(thm)], [c_336, c_16])).
% 3.77/1.64  tff(c_409, plain, (![A_147]: (k4_xboole_0(A_147, A_147)=k1_xboole_0)), inference(resolution, [status(thm)], [c_388, c_187])).
% 3.77/1.64  tff(c_1007, plain, (![A_205]: (k4_xboole_0(A_205, A_205)='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_793, c_409])).
% 3.77/1.64  tff(c_14, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.77/1.64  tff(c_379, plain, (![A_144, B_145]: (r2_hidden('#skF_2'(A_144, B_145, A_144), A_144) | k4_xboole_0(A_144, B_145)=A_144)), inference(resolution, [status(thm)], [c_336, c_14])).
% 3.77/1.64  tff(c_906, plain, (![A_198]: (~r2_hidden(A_198, '#skF_13'))), inference(negUnitSimplification, [status(thm)], [c_812, c_321])).
% 3.77/1.64  tff(c_927, plain, (![B_145]: (k4_xboole_0('#skF_13', B_145)='#skF_13')), inference(resolution, [status(thm)], [c_379, c_906])).
% 3.77/1.64  tff(c_1015, plain, ('#skF_11'='#skF_13'), inference(superposition, [status(thm), theory('equality')], [c_1007, c_927])).
% 3.77/1.64  tff(c_28, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.77/1.64  tff(c_822, plain, (k2_relat_1('#skF_11')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_793, c_793, c_28])).
% 3.77/1.64  tff(c_1058, plain, (k2_relat_1('#skF_13')='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_1015, c_1015, c_822])).
% 3.77/1.64  tff(c_1115, plain, (r2_hidden('#skF_12', '#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_1058, c_254])).
% 3.77/1.64  tff(c_1117, plain, $false, inference(negUnitSimplification, [status(thm)], [c_882, c_1115])).
% 3.77/1.64  tff(c_1118, plain, (![A_7]: (~r2_hidden(A_7, k1_tarski('#skF_12')))), inference(splitRight, [status(thm)], [c_186])).
% 3.77/1.64  tff(c_179, plain, (![D_100]: (r2_hidden(D_100, k1_tarski('#skF_12')) | ~r2_hidden(D_100, k1_xboole_0))), inference(resolution, [status(thm)], [c_90, c_176])).
% 3.77/1.64  tff(c_1119, plain, (![D_100]: (~r2_hidden(D_100, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_1118, c_179])).
% 3.77/1.64  tff(c_1375, plain, (![A_254]: (k4_xboole_0(A_254, A_254)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1344, c_1119])).
% 3.77/1.64  tff(c_20, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | k4_xboole_0(k1_tarski(A_7), B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.77/1.64  tff(c_1407, plain, (![A_255]: (r2_hidden(A_255, k1_tarski(A_255)))), inference(superposition, [status(thm), theory('equality')], [c_1375, c_20])).
% 3.77/1.64  tff(c_1415, plain, $false, inference(resolution, [status(thm)], [c_1407, c_1118])).
% 3.77/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.64  
% 3.77/1.64  Inference rules
% 3.77/1.64  ----------------------
% 3.77/1.64  #Ref     : 0
% 3.77/1.64  #Sup     : 274
% 3.77/1.64  #Fact    : 0
% 3.77/1.64  #Define  : 0
% 3.77/1.64  #Split   : 8
% 3.77/1.64  #Chain   : 0
% 3.77/1.64  #Close   : 0
% 3.77/1.64  
% 3.77/1.64  Ordering : KBO
% 3.77/1.64  
% 3.77/1.64  Simplification rules
% 3.77/1.64  ----------------------
% 3.77/1.64  #Subsume      : 42
% 3.77/1.64  #Demod        : 162
% 3.77/1.64  #Tautology    : 104
% 3.77/1.64  #SimpNegUnit  : 22
% 3.77/1.64  #BackRed      : 60
% 3.77/1.64  
% 3.77/1.64  #Partial instantiations: 0
% 3.77/1.64  #Strategies tried      : 1
% 3.77/1.64  
% 3.77/1.64  Timing (in seconds)
% 3.77/1.64  ----------------------
% 3.77/1.64  Preprocessing        : 0.38
% 3.77/1.64  Parsing              : 0.20
% 3.77/1.64  CNF conversion       : 0.03
% 3.77/1.64  Main loop            : 0.45
% 3.77/1.64  Inferencing          : 0.16
% 3.77/1.64  Reduction            : 0.14
% 3.77/1.64  Demodulation         : 0.09
% 3.77/1.64  BG Simplification    : 0.03
% 3.77/1.64  Subsumption          : 0.09
% 3.77/1.64  Abstraction          : 0.03
% 3.77/1.64  MUC search           : 0.00
% 3.77/1.64  Cooper               : 0.00
% 3.77/1.65  Total                : 0.87
% 3.77/1.65  Index Insertion      : 0.00
% 3.77/1.65  Index Deletion       : 0.00
% 3.77/1.65  Index Matching       : 0.00
% 3.77/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
