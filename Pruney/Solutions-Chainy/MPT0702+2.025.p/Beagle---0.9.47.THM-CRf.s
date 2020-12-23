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
% DateTime   : Thu Dec  3 10:05:05 EST 2020

% Result     : Theorem 3.51s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :   71 (  91 expanded)
%              Number of leaves         :   30 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :  114 ( 183 expanded)
%              Number of equality atoms :   37 (  48 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
            & r1_tarski(A,k1_relat_1(C))
            & v2_funct_1(C) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D)
        & r1_xboole_0(B,D) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_150,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(A_39,B_40)
      | k4_xboole_0(A_39,B_40) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_36,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_158,plain,(
    k4_xboole_0('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_150,c_36])).

tff(c_20,plain,(
    ! [A_12,B_13] : r1_tarski(k4_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_60,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(A_32,B_33) = k1_xboole_0
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_70,plain,(
    ! [A_12,B_13] : k4_xboole_0(k4_xboole_0(A_12,B_13),A_12) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_60])).

tff(c_46,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_44,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_38,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_28,plain,(
    ! [A_20,B_21] : k6_subset_1(A_20,B_21) = k4_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_34,plain,(
    ! [C_26,A_24,B_25] :
      ( k6_subset_1(k9_relat_1(C_26,A_24),k9_relat_1(C_26,B_25)) = k9_relat_1(C_26,k6_subset_1(A_24,B_25))
      | ~ v2_funct_1(C_26)
      | ~ v1_funct_1(C_26)
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_458,plain,(
    ! [C_79,A_80,B_81] :
      ( k4_xboole_0(k9_relat_1(C_79,A_80),k9_relat_1(C_79,B_81)) = k9_relat_1(C_79,k4_xboole_0(A_80,B_81))
      | ~ v2_funct_1(C_79)
      | ~ v1_funct_1(C_79)
      | ~ v1_relat_1(C_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_34])).

tff(c_42,plain,(
    r1_tarski(k9_relat_1('#skF_4','#skF_2'),k9_relat_1('#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = k1_xboole_0
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_76,plain,(
    k4_xboole_0(k9_relat_1('#skF_4','#skF_2'),k9_relat_1('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_16])).

tff(c_475,plain,
    ( k9_relat_1('#skF_4',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_458,c_76])).

tff(c_500,plain,(
    k9_relat_1('#skF_4',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_38,c_475])).

tff(c_334,plain,(
    ! [B_64,A_65] :
      ( r1_xboole_0(k1_relat_1(B_64),A_65)
      | k9_relat_1(B_64,A_65) != k1_xboole_0
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_24,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(A_18,B_19) = A_18
      | ~ r1_xboole_0(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_345,plain,(
    ! [B_64,A_65] :
      ( k4_xboole_0(k1_relat_1(B_64),A_65) = k1_relat_1(B_64)
      | k9_relat_1(B_64,A_65) != k1_xboole_0
      | ~ v1_relat_1(B_64) ) ),
    inference(resolution,[status(thm)],[c_334,c_24])).

tff(c_40,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [A_18,B_19] :
      ( r1_xboole_0(A_18,B_19)
      | k4_xboole_0(A_18,B_19) != A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_381,plain,(
    ! [A_71,C_72,B_73,D_74] :
      ( r1_xboole_0(A_71,C_72)
      | ~ r1_xboole_0(B_73,D_74)
      | ~ r1_tarski(C_72,D_74)
      | ~ r1_tarski(A_71,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_903,plain,(
    ! [A_99,C_100,B_101,A_102] :
      ( r1_xboole_0(A_99,C_100)
      | ~ r1_tarski(C_100,B_101)
      | ~ r1_tarski(A_99,A_102)
      | k4_xboole_0(A_102,B_101) != A_102 ) ),
    inference(resolution,[status(thm)],[c_26,c_381])).

tff(c_1708,plain,(
    ! [A_137,B_138,A_139] :
      ( r1_xboole_0(A_137,B_138)
      | ~ r1_tarski(A_137,A_139)
      | k4_xboole_0(A_139,B_138) != A_139 ) ),
    inference(resolution,[status(thm)],[c_12,c_903])).

tff(c_1772,plain,(
    ! [B_142] :
      ( r1_xboole_0('#skF_2',B_142)
      | k4_xboole_0(k1_relat_1('#skF_4'),B_142) != k1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_1708])).

tff(c_1788,plain,(
    ! [A_65] :
      ( r1_xboole_0('#skF_2',A_65)
      | k9_relat_1('#skF_4',A_65) != k1_xboole_0
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_1772])).

tff(c_1819,plain,(
    ! [A_146] :
      ( r1_xboole_0('#skF_2',A_146)
      | k9_relat_1('#skF_4',A_146) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1788])).

tff(c_1854,plain,(
    ! [A_151] :
      ( k4_xboole_0('#skF_2',A_151) = '#skF_2'
      | k9_relat_1('#skF_4',A_151) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1819,c_24])).

tff(c_1874,plain,(
    k4_xboole_0('#skF_2',k4_xboole_0('#skF_2','#skF_3')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_500,c_1854])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_263,plain,(
    ! [A_55,B_56,C_57] :
      ( ~ r1_xboole_0(A_55,B_56)
      | ~ r2_hidden(C_57,B_56)
      | ~ r2_hidden(C_57,A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_346,plain,(
    ! [C_66,B_67,A_68] :
      ( ~ r2_hidden(C_66,B_67)
      | ~ r2_hidden(C_66,A_68)
      | k4_xboole_0(A_68,B_67) != A_68 ) ),
    inference(resolution,[status(thm)],[c_26,c_263])).

tff(c_2348,plain,(
    ! [A_165,B_166,A_167] :
      ( ~ r2_hidden('#skF_1'(A_165,B_166),A_167)
      | k4_xboole_0(A_167,A_165) != A_167
      | r1_xboole_0(A_165,B_166) ) ),
    inference(resolution,[status(thm)],[c_6,c_346])).

tff(c_2376,plain,(
    ! [B_170,A_171] :
      ( k4_xboole_0(B_170,A_171) != B_170
      | r1_xboole_0(A_171,B_170) ) ),
    inference(resolution,[status(thm)],[c_4,c_2348])).

tff(c_2415,plain,(
    ! [A_176,B_177] :
      ( k4_xboole_0(A_176,B_177) = A_176
      | k4_xboole_0(B_177,A_176) != B_177 ) ),
    inference(resolution,[status(thm)],[c_2376,c_24])).

tff(c_2421,plain,(
    k4_xboole_0(k4_xboole_0('#skF_2','#skF_3'),'#skF_2') = k4_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1874,c_2415])).

tff(c_2443,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2421])).

tff(c_2445,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_158,c_2443])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:48:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.51/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.51/1.63  
% 3.51/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.85/1.64  %$ r2_hidden > r1_xboole_0 > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.85/1.64  
% 3.85/1.64  %Foreground sorts:
% 3.85/1.64  
% 3.85/1.64  
% 3.85/1.64  %Background operators:
% 3.85/1.64  
% 3.85/1.64  
% 3.85/1.64  %Foreground operators:
% 3.85/1.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.85/1.64  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.85/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.85/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.85/1.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.85/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.85/1.64  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.85/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.85/1.64  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.85/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.85/1.64  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.85/1.64  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.85/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.85/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.85/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.85/1.64  tff('#skF_4', type, '#skF_4': $i).
% 3.85/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.85/1.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.85/1.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.85/1.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.85/1.64  
% 3.85/1.65  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.85/1.65  tff(f_98, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_funct_1)).
% 3.85/1.65  tff(f_57, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.85/1.65  tff(f_71, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.85/1.65  tff(f_85, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_funct_1)).
% 3.85/1.65  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 3.85/1.65  tff(f_69, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.85/1.65  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.85/1.65  tff(f_65, axiom, (![A, B, C, D]: (((r1_tarski(A, B) & r1_tarski(C, D)) & r1_xboole_0(B, D)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_xboole_1)).
% 3.85/1.65  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.85/1.65  tff(c_150, plain, (![A_39, B_40]: (r1_tarski(A_39, B_40) | k4_xboole_0(A_39, B_40)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.85/1.65  tff(c_36, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.85/1.65  tff(c_158, plain, (k4_xboole_0('#skF_2', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_150, c_36])).
% 3.85/1.65  tff(c_20, plain, (![A_12, B_13]: (r1_tarski(k4_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.85/1.65  tff(c_60, plain, (![A_32, B_33]: (k4_xboole_0(A_32, B_33)=k1_xboole_0 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.85/1.65  tff(c_70, plain, (![A_12, B_13]: (k4_xboole_0(k4_xboole_0(A_12, B_13), A_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_60])).
% 3.85/1.65  tff(c_46, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.85/1.65  tff(c_44, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.85/1.65  tff(c_38, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.85/1.65  tff(c_28, plain, (![A_20, B_21]: (k6_subset_1(A_20, B_21)=k4_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.85/1.65  tff(c_34, plain, (![C_26, A_24, B_25]: (k6_subset_1(k9_relat_1(C_26, A_24), k9_relat_1(C_26, B_25))=k9_relat_1(C_26, k6_subset_1(A_24, B_25)) | ~v2_funct_1(C_26) | ~v1_funct_1(C_26) | ~v1_relat_1(C_26))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.85/1.65  tff(c_458, plain, (![C_79, A_80, B_81]: (k4_xboole_0(k9_relat_1(C_79, A_80), k9_relat_1(C_79, B_81))=k9_relat_1(C_79, k4_xboole_0(A_80, B_81)) | ~v2_funct_1(C_79) | ~v1_funct_1(C_79) | ~v1_relat_1(C_79))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_34])).
% 3.85/1.65  tff(c_42, plain, (r1_tarski(k9_relat_1('#skF_4', '#skF_2'), k9_relat_1('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.85/1.65  tff(c_16, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=k1_xboole_0 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.85/1.65  tff(c_76, plain, (k4_xboole_0(k9_relat_1('#skF_4', '#skF_2'), k9_relat_1('#skF_4', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_16])).
% 3.85/1.65  tff(c_475, plain, (k9_relat_1('#skF_4', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0 | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_458, c_76])).
% 3.85/1.65  tff(c_500, plain, (k9_relat_1('#skF_4', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_38, c_475])).
% 3.85/1.65  tff(c_334, plain, (![B_64, A_65]: (r1_xboole_0(k1_relat_1(B_64), A_65) | k9_relat_1(B_64, A_65)!=k1_xboole_0 | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.85/1.65  tff(c_24, plain, (![A_18, B_19]: (k4_xboole_0(A_18, B_19)=A_18 | ~r1_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.85/1.65  tff(c_345, plain, (![B_64, A_65]: (k4_xboole_0(k1_relat_1(B_64), A_65)=k1_relat_1(B_64) | k9_relat_1(B_64, A_65)!=k1_xboole_0 | ~v1_relat_1(B_64))), inference(resolution, [status(thm)], [c_334, c_24])).
% 3.85/1.65  tff(c_40, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.85/1.65  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.85/1.65  tff(c_26, plain, (![A_18, B_19]: (r1_xboole_0(A_18, B_19) | k4_xboole_0(A_18, B_19)!=A_18)), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.85/1.65  tff(c_381, plain, (![A_71, C_72, B_73, D_74]: (r1_xboole_0(A_71, C_72) | ~r1_xboole_0(B_73, D_74) | ~r1_tarski(C_72, D_74) | ~r1_tarski(A_71, B_73))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.85/1.65  tff(c_903, plain, (![A_99, C_100, B_101, A_102]: (r1_xboole_0(A_99, C_100) | ~r1_tarski(C_100, B_101) | ~r1_tarski(A_99, A_102) | k4_xboole_0(A_102, B_101)!=A_102)), inference(resolution, [status(thm)], [c_26, c_381])).
% 3.85/1.65  tff(c_1708, plain, (![A_137, B_138, A_139]: (r1_xboole_0(A_137, B_138) | ~r1_tarski(A_137, A_139) | k4_xboole_0(A_139, B_138)!=A_139)), inference(resolution, [status(thm)], [c_12, c_903])).
% 3.85/1.65  tff(c_1772, plain, (![B_142]: (r1_xboole_0('#skF_2', B_142) | k4_xboole_0(k1_relat_1('#skF_4'), B_142)!=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_1708])).
% 3.85/1.65  tff(c_1788, plain, (![A_65]: (r1_xboole_0('#skF_2', A_65) | k9_relat_1('#skF_4', A_65)!=k1_xboole_0 | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_345, c_1772])).
% 3.85/1.65  tff(c_1819, plain, (![A_146]: (r1_xboole_0('#skF_2', A_146) | k9_relat_1('#skF_4', A_146)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1788])).
% 3.85/1.65  tff(c_1854, plain, (![A_151]: (k4_xboole_0('#skF_2', A_151)='#skF_2' | k9_relat_1('#skF_4', A_151)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_1819, c_24])).
% 3.85/1.65  tff(c_1874, plain, (k4_xboole_0('#skF_2', k4_xboole_0('#skF_2', '#skF_3'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_500, c_1854])).
% 3.85/1.65  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.85/1.65  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.85/1.65  tff(c_263, plain, (![A_55, B_56, C_57]: (~r1_xboole_0(A_55, B_56) | ~r2_hidden(C_57, B_56) | ~r2_hidden(C_57, A_55))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.85/1.65  tff(c_346, plain, (![C_66, B_67, A_68]: (~r2_hidden(C_66, B_67) | ~r2_hidden(C_66, A_68) | k4_xboole_0(A_68, B_67)!=A_68)), inference(resolution, [status(thm)], [c_26, c_263])).
% 3.85/1.65  tff(c_2348, plain, (![A_165, B_166, A_167]: (~r2_hidden('#skF_1'(A_165, B_166), A_167) | k4_xboole_0(A_167, A_165)!=A_167 | r1_xboole_0(A_165, B_166))), inference(resolution, [status(thm)], [c_6, c_346])).
% 3.85/1.65  tff(c_2376, plain, (![B_170, A_171]: (k4_xboole_0(B_170, A_171)!=B_170 | r1_xboole_0(A_171, B_170))), inference(resolution, [status(thm)], [c_4, c_2348])).
% 3.85/1.65  tff(c_2415, plain, (![A_176, B_177]: (k4_xboole_0(A_176, B_177)=A_176 | k4_xboole_0(B_177, A_176)!=B_177)), inference(resolution, [status(thm)], [c_2376, c_24])).
% 3.85/1.65  tff(c_2421, plain, (k4_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), '#skF_2')=k4_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1874, c_2415])).
% 3.85/1.65  tff(c_2443, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2421])).
% 3.85/1.65  tff(c_2445, plain, $false, inference(negUnitSimplification, [status(thm)], [c_158, c_2443])).
% 3.85/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.85/1.65  
% 3.85/1.65  Inference rules
% 3.85/1.65  ----------------------
% 3.85/1.65  #Ref     : 1
% 3.85/1.65  #Sup     : 596
% 3.85/1.65  #Fact    : 0
% 3.85/1.65  #Define  : 0
% 3.85/1.65  #Split   : 6
% 3.85/1.65  #Chain   : 0
% 3.85/1.65  #Close   : 0
% 3.85/1.65  
% 3.85/1.65  Ordering : KBO
% 3.85/1.65  
% 3.85/1.65  Simplification rules
% 3.85/1.65  ----------------------
% 3.85/1.65  #Subsume      : 216
% 3.85/1.65  #Demod        : 322
% 3.85/1.65  #Tautology    : 221
% 3.85/1.65  #SimpNegUnit  : 43
% 3.85/1.65  #BackRed      : 13
% 3.85/1.65  
% 3.85/1.65  #Partial instantiations: 0
% 3.85/1.65  #Strategies tried      : 1
% 3.85/1.65  
% 3.85/1.65  Timing (in seconds)
% 3.85/1.65  ----------------------
% 3.85/1.65  Preprocessing        : 0.31
% 3.85/1.65  Parsing              : 0.17
% 3.85/1.65  CNF conversion       : 0.02
% 3.85/1.66  Main loop            : 0.58
% 3.85/1.66  Inferencing          : 0.19
% 3.85/1.66  Reduction            : 0.21
% 3.85/1.66  Demodulation         : 0.15
% 3.85/1.66  BG Simplification    : 0.02
% 3.85/1.66  Subsumption          : 0.11
% 3.85/1.66  Abstraction          : 0.03
% 3.85/1.66  MUC search           : 0.00
% 3.85/1.66  Cooper               : 0.00
% 3.85/1.66  Total                : 0.92
% 3.85/1.66  Index Insertion      : 0.00
% 3.85/1.66  Index Deletion       : 0.00
% 3.85/1.66  Index Matching       : 0.00
% 3.85/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
