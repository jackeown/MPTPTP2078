%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:46 EST 2020

% Result     : Theorem 11.09s
% Output     : CNFRefutation 11.21s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 271 expanded)
%              Number of leaves         :   25 ( 102 expanded)
%              Depth                    :   16
%              Number of atoms          :  100 ( 327 expanded)
%              Number of equality atoms :   69 ( 259 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_57,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_38,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_16,plain,(
    ! [A_11] : k2_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_771,plain,(
    ! [A_74,B_75] : k2_xboole_0(k3_xboole_0(A_74,B_75),k4_xboole_0(A_74,B_75)) = A_74 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_94,plain,(
    ! [B_38,A_39] : k2_xboole_0(B_38,A_39) = k2_xboole_0(A_39,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k2_xboole_0(A_17,B_18)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_109,plain,(
    ! [A_39,B_38] : k4_xboole_0(A_39,k2_xboole_0(B_38,A_39)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_22])).

tff(c_783,plain,(
    ! [A_74,B_75] : k4_xboole_0(k4_xboole_0(A_74,B_75),A_74) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_771,c_109])).

tff(c_306,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(A_50,B_51)
      | k4_xboole_0(A_50,B_51) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2395,plain,(
    ! [A_117,B_118] :
      ( k2_xboole_0(A_117,B_118) = B_118
      | k4_xboole_0(A_117,B_118) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_306,c_14])).

tff(c_2444,plain,(
    ! [A_74,B_75] : k2_xboole_0(k4_xboole_0(A_74,B_75),A_74) = A_74 ),
    inference(superposition,[status(thm),theory(equality)],[c_783,c_2395])).

tff(c_843,plain,(
    ! [A_76,B_77] : k4_xboole_0(k3_xboole_0(A_76,B_77),A_76) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_771,c_22])).

tff(c_18,plain,(
    ! [A_12,B_13] : k2_xboole_0(A_12,k4_xboole_0(B_13,A_12)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_855,plain,(
    ! [A_76,B_77] : k2_xboole_0(A_76,k3_xboole_0(A_76,B_77)) = k2_xboole_0(A_76,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_843,c_18])).

tff(c_888,plain,(
    ! [A_76,B_77] : k2_xboole_0(A_76,k3_xboole_0(A_76,B_77)) = A_76 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_855])).

tff(c_1967,plain,(
    ! [A_103,B_104] : k2_xboole_0(k3_xboole_0(A_103,k2_xboole_0(A_103,B_104)),k1_xboole_0) = A_103 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_771])).

tff(c_502,plain,(
    ! [A_61,B_62] : k2_xboole_0(A_61,k4_xboole_0(B_62,A_61)) = k2_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_546,plain,(
    ! [A_17,B_18] : k2_xboole_0(k2_xboole_0(A_17,B_18),k1_xboole_0) = k2_xboole_0(k2_xboole_0(A_17,B_18),A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_502])).

tff(c_558,plain,(
    ! [A_17,B_18] : k2_xboole_0(k2_xboole_0(A_17,B_18),A_17) = k2_xboole_0(A_17,B_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_546])).

tff(c_1979,plain,(
    ! [A_103,B_104] : k2_xboole_0(k3_xboole_0(A_103,k2_xboole_0(A_103,B_104)),k1_xboole_0) = k2_xboole_0(A_103,k3_xboole_0(A_103,k2_xboole_0(A_103,B_104))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1967,c_558])).

tff(c_2062,plain,(
    ! [A_103,B_104] : k3_xboole_0(A_103,k2_xboole_0(A_103,B_104)) = A_103 ),
    inference(demodulation,[status(thm),theory(equality)],[c_888,c_16,c_1979])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2079,plain,(
    ! [A_105,B_106] : k3_xboole_0(A_105,k2_xboole_0(A_105,B_106)) = A_105 ),
    inference(demodulation,[status(thm),theory(equality)],[c_888,c_16,c_1979])).

tff(c_2132,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,k2_xboole_0(A_1,B_2)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2079])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_658,plain,(
    ! [A_66,B_67,C_68] :
      ( r1_xboole_0(A_66,B_67)
      | ~ r1_xboole_0(A_66,k2_xboole_0(B_67,C_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2568,plain,(
    ! [A_121,B_122,C_123] :
      ( r1_xboole_0(A_121,B_122)
      | k3_xboole_0(A_121,k2_xboole_0(B_122,C_123)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_658])).

tff(c_2674,plain,(
    ! [B_125,A_126] :
      ( r1_xboole_0(B_125,A_126)
      | k1_xboole_0 != B_125 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2132,c_2568])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2738,plain,(
    ! [A_128,B_129] :
      ( r1_xboole_0(A_128,B_129)
      | k1_xboole_0 != B_129 ) ),
    inference(resolution,[status(thm)],[c_2674,c_8])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3110,plain,(
    ! [A_138,B_139] :
      ( k3_xboole_0(A_138,B_139) = k1_xboole_0
      | k1_xboole_0 != B_139 ) ),
    inference(resolution,[status(thm)],[c_2738,c_4])).

tff(c_3847,plain,(
    ! [A_151,B_152] :
      ( k1_xboole_0 = A_151
      | k2_xboole_0(A_151,B_152) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2062,c_3110])).

tff(c_3977,plain,(
    ! [A_154,B_155] :
      ( k4_xboole_0(A_154,B_155) = k1_xboole_0
      | k1_xboole_0 != A_154 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2444,c_3847])).

tff(c_4038,plain,(
    ! [B_155,A_154] :
      ( k2_xboole_0(B_155,k1_xboole_0) = k2_xboole_0(B_155,A_154)
      | k1_xboole_0 != A_154 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3977,c_18])).

tff(c_4480,plain,(
    ! [B_155] : k2_xboole_0(B_155,k1_xboole_0) = B_155 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_4038])).

tff(c_40,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_55,plain,(
    ! [B_33,A_34] :
      ( r1_xboole_0(B_33,A_34)
      | ~ r1_xboole_0(A_34,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_60,plain,(
    r1_xboole_0('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_55])).

tff(c_190,plain,(
    ! [A_41,B_42] :
      ( k3_xboole_0(A_41,B_42) = k1_xboole_0
      | ~ r1_xboole_0(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_204,plain,(
    k3_xboole_0('#skF_2','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_190])).

tff(c_822,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_2','#skF_4')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_771])).

tff(c_116,plain,(
    ! [A_39] : k2_xboole_0(k1_xboole_0,A_39) = A_39 ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_16])).

tff(c_1426,plain,(
    k4_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_822,c_116])).

tff(c_44,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_45,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_44])).

tff(c_246,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k2_xboole_0(B_45,A_44)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_22])).

tff(c_271,plain,(
    k4_xboole_0('#skF_2',k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_246])).

tff(c_1126,plain,(
    ! [A_82,B_83,C_84] : k4_xboole_0(k4_xboole_0(A_82,B_83),C_84) = k4_xboole_0(A_82,k2_xboole_0(B_83,C_84)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20587,plain,(
    ! [C_298,A_299,B_300] : k2_xboole_0(C_298,k4_xboole_0(A_299,k2_xboole_0(B_300,C_298))) = k2_xboole_0(C_298,k4_xboole_0(A_299,B_300)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1126,c_18])).

tff(c_20984,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_2','#skF_4')) = k2_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_20587])).

tff(c_21096,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4480,c_1426,c_20984])).

tff(c_42,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_206,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_190])).

tff(c_825,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_1')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_771])).

tff(c_983,plain,(
    k4_xboole_0('#skF_3','#skF_1') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_825,c_116])).

tff(c_22615,plain,(
    ! [A_305] : k2_xboole_0('#skF_2',k4_xboole_0(A_305,k2_xboole_0('#skF_4','#skF_3'))) = k2_xboole_0('#skF_2',k4_xboole_0(A_305,'#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_20587])).

tff(c_22845,plain,(
    k2_xboole_0('#skF_2',k4_xboole_0('#skF_3','#skF_1')) = k2_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_22615])).

tff(c_22896,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4480,c_21096,c_2,c_983,c_22845])).

tff(c_22898,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_22896])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:52:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.09/4.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.21/4.42  
% 11.21/4.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.21/4.43  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 11.21/4.43  
% 11.21/4.43  %Foreground sorts:
% 11.21/4.43  
% 11.21/4.43  
% 11.21/4.43  %Background operators:
% 11.21/4.43  
% 11.21/4.43  
% 11.21/4.43  %Foreground operators:
% 11.21/4.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.21/4.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.21/4.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.21/4.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.21/4.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.21/4.43  tff('#skF_2', type, '#skF_2': $i).
% 11.21/4.43  tff('#skF_3', type, '#skF_3': $i).
% 11.21/4.43  tff('#skF_1', type, '#skF_1': $i).
% 11.21/4.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.21/4.43  tff('#skF_4', type, '#skF_4': $i).
% 11.21/4.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.21/4.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.21/4.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.21/4.43  
% 11.21/4.44  tff(f_90, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_xboole_1)).
% 11.21/4.44  tff(f_45, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 11.21/4.44  tff(f_57, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 11.21/4.44  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 11.21/4.44  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 11.21/4.44  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 11.21/4.44  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 11.21/4.44  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 11.21/4.44  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 11.21/4.44  tff(f_73, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 11.21/4.44  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 11.21/4.44  tff(f_49, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 11.21/4.44  tff(c_38, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.21/4.44  tff(c_16, plain, (![A_11]: (k2_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.21/4.44  tff(c_771, plain, (![A_74, B_75]: (k2_xboole_0(k3_xboole_0(A_74, B_75), k4_xboole_0(A_74, B_75))=A_74)), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.21/4.44  tff(c_94, plain, (![B_38, A_39]: (k2_xboole_0(B_38, A_39)=k2_xboole_0(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.21/4.44  tff(c_22, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k2_xboole_0(A_17, B_18))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.21/4.44  tff(c_109, plain, (![A_39, B_38]: (k4_xboole_0(A_39, k2_xboole_0(B_38, A_39))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_94, c_22])).
% 11.21/4.44  tff(c_783, plain, (![A_74, B_75]: (k4_xboole_0(k4_xboole_0(A_74, B_75), A_74)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_771, c_109])).
% 11.21/4.44  tff(c_306, plain, (![A_50, B_51]: (r1_tarski(A_50, B_51) | k4_xboole_0(A_50, B_51)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.21/4.44  tff(c_14, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.21/4.44  tff(c_2395, plain, (![A_117, B_118]: (k2_xboole_0(A_117, B_118)=B_118 | k4_xboole_0(A_117, B_118)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_306, c_14])).
% 11.21/4.44  tff(c_2444, plain, (![A_74, B_75]: (k2_xboole_0(k4_xboole_0(A_74, B_75), A_74)=A_74)), inference(superposition, [status(thm), theory('equality')], [c_783, c_2395])).
% 11.21/4.44  tff(c_843, plain, (![A_76, B_77]: (k4_xboole_0(k3_xboole_0(A_76, B_77), A_76)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_771, c_22])).
% 11.21/4.44  tff(c_18, plain, (![A_12, B_13]: (k2_xboole_0(A_12, k4_xboole_0(B_13, A_12))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.21/4.44  tff(c_855, plain, (![A_76, B_77]: (k2_xboole_0(A_76, k3_xboole_0(A_76, B_77))=k2_xboole_0(A_76, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_843, c_18])).
% 11.21/4.44  tff(c_888, plain, (![A_76, B_77]: (k2_xboole_0(A_76, k3_xboole_0(A_76, B_77))=A_76)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_855])).
% 11.21/4.44  tff(c_1967, plain, (![A_103, B_104]: (k2_xboole_0(k3_xboole_0(A_103, k2_xboole_0(A_103, B_104)), k1_xboole_0)=A_103)), inference(superposition, [status(thm), theory('equality')], [c_22, c_771])).
% 11.21/4.44  tff(c_502, plain, (![A_61, B_62]: (k2_xboole_0(A_61, k4_xboole_0(B_62, A_61))=k2_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.21/4.44  tff(c_546, plain, (![A_17, B_18]: (k2_xboole_0(k2_xboole_0(A_17, B_18), k1_xboole_0)=k2_xboole_0(k2_xboole_0(A_17, B_18), A_17))), inference(superposition, [status(thm), theory('equality')], [c_22, c_502])).
% 11.21/4.44  tff(c_558, plain, (![A_17, B_18]: (k2_xboole_0(k2_xboole_0(A_17, B_18), A_17)=k2_xboole_0(A_17, B_18))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_546])).
% 11.21/4.44  tff(c_1979, plain, (![A_103, B_104]: (k2_xboole_0(k3_xboole_0(A_103, k2_xboole_0(A_103, B_104)), k1_xboole_0)=k2_xboole_0(A_103, k3_xboole_0(A_103, k2_xboole_0(A_103, B_104))))), inference(superposition, [status(thm), theory('equality')], [c_1967, c_558])).
% 11.21/4.44  tff(c_2062, plain, (![A_103, B_104]: (k3_xboole_0(A_103, k2_xboole_0(A_103, B_104))=A_103)), inference(demodulation, [status(thm), theory('equality')], [c_888, c_16, c_1979])).
% 11.21/4.44  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.21/4.44  tff(c_2079, plain, (![A_105, B_106]: (k3_xboole_0(A_105, k2_xboole_0(A_105, B_106))=A_105)), inference(demodulation, [status(thm), theory('equality')], [c_888, c_16, c_1979])).
% 11.21/4.44  tff(c_2132, plain, (![B_2, A_1]: (k3_xboole_0(B_2, k2_xboole_0(A_1, B_2))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_2079])).
% 11.21/4.44  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.21/4.44  tff(c_658, plain, (![A_66, B_67, C_68]: (r1_xboole_0(A_66, B_67) | ~r1_xboole_0(A_66, k2_xboole_0(B_67, C_68)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.21/4.44  tff(c_2568, plain, (![A_121, B_122, C_123]: (r1_xboole_0(A_121, B_122) | k3_xboole_0(A_121, k2_xboole_0(B_122, C_123))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_658])).
% 11.21/4.44  tff(c_2674, plain, (![B_125, A_126]: (r1_xboole_0(B_125, A_126) | k1_xboole_0!=B_125)), inference(superposition, [status(thm), theory('equality')], [c_2132, c_2568])).
% 11.21/4.44  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.21/4.44  tff(c_2738, plain, (![A_128, B_129]: (r1_xboole_0(A_128, B_129) | k1_xboole_0!=B_129)), inference(resolution, [status(thm)], [c_2674, c_8])).
% 11.21/4.44  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.21/4.44  tff(c_3110, plain, (![A_138, B_139]: (k3_xboole_0(A_138, B_139)=k1_xboole_0 | k1_xboole_0!=B_139)), inference(resolution, [status(thm)], [c_2738, c_4])).
% 11.21/4.44  tff(c_3847, plain, (![A_151, B_152]: (k1_xboole_0=A_151 | k2_xboole_0(A_151, B_152)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2062, c_3110])).
% 11.21/4.44  tff(c_3977, plain, (![A_154, B_155]: (k4_xboole_0(A_154, B_155)=k1_xboole_0 | k1_xboole_0!=A_154)), inference(superposition, [status(thm), theory('equality')], [c_2444, c_3847])).
% 11.21/4.44  tff(c_4038, plain, (![B_155, A_154]: (k2_xboole_0(B_155, k1_xboole_0)=k2_xboole_0(B_155, A_154) | k1_xboole_0!=A_154)), inference(superposition, [status(thm), theory('equality')], [c_3977, c_18])).
% 11.21/4.44  tff(c_4480, plain, (![B_155]: (k2_xboole_0(B_155, k1_xboole_0)=B_155)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_4038])).
% 11.21/4.44  tff(c_40, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.21/4.44  tff(c_55, plain, (![B_33, A_34]: (r1_xboole_0(B_33, A_34) | ~r1_xboole_0(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.21/4.44  tff(c_60, plain, (r1_xboole_0('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_55])).
% 11.21/4.44  tff(c_190, plain, (![A_41, B_42]: (k3_xboole_0(A_41, B_42)=k1_xboole_0 | ~r1_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.21/4.44  tff(c_204, plain, (k3_xboole_0('#skF_2', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_60, c_190])).
% 11.21/4.44  tff(c_822, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_2', '#skF_4'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_204, c_771])).
% 11.21/4.44  tff(c_116, plain, (![A_39]: (k2_xboole_0(k1_xboole_0, A_39)=A_39)), inference(superposition, [status(thm), theory('equality')], [c_94, c_16])).
% 11.21/4.44  tff(c_1426, plain, (k4_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_822, c_116])).
% 11.21/4.44  tff(c_44, plain, (k2_xboole_0('#skF_3', '#skF_4')=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.21/4.44  tff(c_45, plain, (k2_xboole_0('#skF_1', '#skF_2')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_44])).
% 11.21/4.44  tff(c_246, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k2_xboole_0(B_45, A_44))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_94, c_22])).
% 11.21/4.44  tff(c_271, plain, (k4_xboole_0('#skF_2', k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_45, c_246])).
% 11.21/4.44  tff(c_1126, plain, (![A_82, B_83, C_84]: (k4_xboole_0(k4_xboole_0(A_82, B_83), C_84)=k4_xboole_0(A_82, k2_xboole_0(B_83, C_84)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.21/4.44  tff(c_20587, plain, (![C_298, A_299, B_300]: (k2_xboole_0(C_298, k4_xboole_0(A_299, k2_xboole_0(B_300, C_298)))=k2_xboole_0(C_298, k4_xboole_0(A_299, B_300)))), inference(superposition, [status(thm), theory('equality')], [c_1126, c_18])).
% 11.21/4.44  tff(c_20984, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_2', '#skF_4'))=k2_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_271, c_20587])).
% 11.21/4.44  tff(c_21096, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4480, c_1426, c_20984])).
% 11.21/4.44  tff(c_42, plain, (r1_xboole_0('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.21/4.44  tff(c_206, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_190])).
% 11.21/4.44  tff(c_825, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_1'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_206, c_771])).
% 11.21/4.44  tff(c_983, plain, (k4_xboole_0('#skF_3', '#skF_1')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_825, c_116])).
% 11.21/4.44  tff(c_22615, plain, (![A_305]: (k2_xboole_0('#skF_2', k4_xboole_0(A_305, k2_xboole_0('#skF_4', '#skF_3')))=k2_xboole_0('#skF_2', k4_xboole_0(A_305, '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_45, c_20587])).
% 11.21/4.44  tff(c_22845, plain, (k2_xboole_0('#skF_2', k4_xboole_0('#skF_3', '#skF_1'))=k2_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_109, c_22615])).
% 11.21/4.44  tff(c_22896, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4480, c_21096, c_2, c_983, c_22845])).
% 11.21/4.44  tff(c_22898, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_22896])).
% 11.21/4.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.21/4.44  
% 11.21/4.44  Inference rules
% 11.21/4.44  ----------------------
% 11.21/4.44  #Ref     : 2
% 11.21/4.44  #Sup     : 6004
% 11.21/4.44  #Fact    : 0
% 11.21/4.44  #Define  : 0
% 11.21/4.44  #Split   : 4
% 11.21/4.44  #Chain   : 0
% 11.21/4.44  #Close   : 0
% 11.21/4.44  
% 11.21/4.44  Ordering : KBO
% 11.21/4.44  
% 11.21/4.44  Simplification rules
% 11.21/4.44  ----------------------
% 11.21/4.44  #Subsume      : 1036
% 11.21/4.44  #Demod        : 4796
% 11.21/4.44  #Tautology    : 2761
% 11.21/4.44  #SimpNegUnit  : 112
% 11.21/4.44  #BackRed      : 12
% 11.21/4.44  
% 11.21/4.44  #Partial instantiations: 0
% 11.21/4.44  #Strategies tried      : 1
% 11.21/4.44  
% 11.21/4.44  Timing (in seconds)
% 11.21/4.44  ----------------------
% 11.21/4.45  Preprocessing        : 0.32
% 11.21/4.45  Parsing              : 0.17
% 11.21/4.45  CNF conversion       : 0.02
% 11.21/4.45  Main loop            : 3.35
% 11.21/4.45  Inferencing          : 0.60
% 11.21/4.45  Reduction            : 1.97
% 11.21/4.45  Demodulation         : 1.73
% 11.21/4.45  BG Simplification    : 0.08
% 11.21/4.45  Subsumption          : 0.53
% 11.21/4.45  Abstraction          : 0.11
% 11.21/4.45  MUC search           : 0.00
% 11.21/4.45  Cooper               : 0.00
% 11.21/4.45  Total                : 3.70
% 11.21/4.45  Index Insertion      : 0.00
% 11.21/4.45  Index Deletion       : 0.00
% 11.21/4.45  Index Matching       : 0.00
% 11.21/4.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
