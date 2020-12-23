%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:08 EST 2020

% Result     : Theorem 8.42s
% Output     : CNFRefutation 8.55s
% Verified   : 
% Statistics : Number of formulae       :   49 (  59 expanded)
%              Number of leaves         :   24 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   69 ( 110 expanded)
%              Number of equality atoms :   23 (  26 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
            & r1_tarski(A,k1_relat_1(C))
            & v2_funct_1(C) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_41,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( A != k1_xboole_0
          & r1_tarski(A,k1_relat_1(B))
          & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

tff(c_231,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | k4_xboole_0(A_33,B_34) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_243,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_231,c_18])).

tff(c_22,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_20,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12,plain,(
    ! [A_10,B_11] : k6_subset_1(A_10,B_11) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [C_16,A_14,B_15] :
      ( k6_subset_1(k9_relat_1(C_16,A_14),k9_relat_1(C_16,B_15)) = k9_relat_1(C_16,k6_subset_1(A_14,B_15))
      | ~ v2_funct_1(C_16)
      | ~ v1_funct_1(C_16)
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_533,plain,(
    ! [C_52,A_53,B_54] :
      ( k4_xboole_0(k9_relat_1(C_52,A_53),k9_relat_1(C_52,B_54)) = k9_relat_1(C_52,k4_xboole_0(A_53,B_54))
      | ~ v2_funct_1(C_52)
      | ~ v1_funct_1(C_52)
      | ~ v1_relat_1(C_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_16])).

tff(c_24,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_40,plain,(
    ! [A_21,B_22] :
      ( k4_xboole_0(A_21,B_22) = k1_xboole_0
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_50,plain,(
    k4_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_40])).

tff(c_548,plain,
    ( k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_533,c_50])).

tff(c_570,plain,(
    k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_20,c_548])).

tff(c_10,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_111,plain,(
    ! [A_25,B_26] :
      ( k2_xboole_0(A_25,B_26) = B_26
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_130,plain,(
    ! [A_8,B_9] : k2_xboole_0(k4_xboole_0(A_8,B_9),A_8) = A_8 ),
    inference(resolution,[status(thm)],[c_10,c_111])).

tff(c_244,plain,(
    ! [A_35,C_36,B_37] :
      ( r1_tarski(A_35,C_36)
      | ~ r1_tarski(k2_xboole_0(A_35,B_37),C_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_495,plain,(
    ! [A_49,B_50,C_51] :
      ( r1_tarski(k4_xboole_0(A_49,B_50),C_51)
      | ~ r1_tarski(A_49,C_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_244])).

tff(c_14,plain,(
    ! [B_13,A_12] :
      ( k9_relat_1(B_13,A_12) != k1_xboole_0
      | ~ r1_tarski(A_12,k1_relat_1(B_13))
      | k1_xboole_0 = A_12
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16835,plain,(
    ! [B_356,A_357,B_358] :
      ( k9_relat_1(B_356,k4_xboole_0(A_357,B_358)) != k1_xboole_0
      | k4_xboole_0(A_357,B_358) = k1_xboole_0
      | ~ v1_relat_1(B_356)
      | ~ r1_tarski(A_357,k1_relat_1(B_356)) ) ),
    inference(resolution,[status(thm)],[c_495,c_14])).

tff(c_16891,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_3')
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_570,c_16835])).

tff(c_16925,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_28,c_16891])).

tff(c_16927,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_243,c_16925])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:45:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.42/2.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.42/2.99  
% 8.42/2.99  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.42/3.00  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 8.42/3.00  
% 8.42/3.00  %Foreground sorts:
% 8.42/3.00  
% 8.42/3.00  
% 8.42/3.00  %Background operators:
% 8.42/3.00  
% 8.42/3.00  
% 8.42/3.00  %Foreground operators:
% 8.42/3.00  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.42/3.00  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.42/3.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.42/3.00  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.42/3.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.42/3.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.42/3.00  tff('#skF_2', type, '#skF_2': $i).
% 8.42/3.00  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.42/3.00  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 8.42/3.00  tff('#skF_3', type, '#skF_3': $i).
% 8.42/3.00  tff('#skF_1', type, '#skF_1': $i).
% 8.42/3.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.42/3.00  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.42/3.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.42/3.00  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.42/3.00  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.42/3.00  
% 8.55/3.01  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 8.55/3.01  tff(f_72, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_funct_1)).
% 8.55/3.01  tff(f_41, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 8.55/3.01  tff(f_59, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_funct_1)).
% 8.55/3.01  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 8.55/3.01  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 8.55/3.01  tff(f_33, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 8.55/3.01  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_relat_1)).
% 8.55/3.01  tff(c_231, plain, (![A_33, B_34]: (r1_tarski(A_33, B_34) | k4_xboole_0(A_33, B_34)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.55/3.01  tff(c_18, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.55/3.01  tff(c_243, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_231, c_18])).
% 8.55/3.01  tff(c_22, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.55/3.01  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.55/3.01  tff(c_26, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.55/3.01  tff(c_20, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.55/3.01  tff(c_12, plain, (![A_10, B_11]: (k6_subset_1(A_10, B_11)=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.55/3.01  tff(c_16, plain, (![C_16, A_14, B_15]: (k6_subset_1(k9_relat_1(C_16, A_14), k9_relat_1(C_16, B_15))=k9_relat_1(C_16, k6_subset_1(A_14, B_15)) | ~v2_funct_1(C_16) | ~v1_funct_1(C_16) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.55/3.01  tff(c_533, plain, (![C_52, A_53, B_54]: (k4_xboole_0(k9_relat_1(C_52, A_53), k9_relat_1(C_52, B_54))=k9_relat_1(C_52, k4_xboole_0(A_53, B_54)) | ~v2_funct_1(C_52) | ~v1_funct_1(C_52) | ~v1_relat_1(C_52))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_16])).
% 8.55/3.01  tff(c_24, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.55/3.01  tff(c_40, plain, (![A_21, B_22]: (k4_xboole_0(A_21, B_22)=k1_xboole_0 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.55/3.01  tff(c_50, plain, (k4_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_40])).
% 8.55/3.01  tff(c_548, plain, (k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0 | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_533, c_50])).
% 8.55/3.01  tff(c_570, plain, (k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_20, c_548])).
% 8.55/3.01  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.55/3.01  tff(c_111, plain, (![A_25, B_26]: (k2_xboole_0(A_25, B_26)=B_26 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.55/3.01  tff(c_130, plain, (![A_8, B_9]: (k2_xboole_0(k4_xboole_0(A_8, B_9), A_8)=A_8)), inference(resolution, [status(thm)], [c_10, c_111])).
% 8.55/3.01  tff(c_244, plain, (![A_35, C_36, B_37]: (r1_tarski(A_35, C_36) | ~r1_tarski(k2_xboole_0(A_35, B_37), C_36))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.55/3.01  tff(c_495, plain, (![A_49, B_50, C_51]: (r1_tarski(k4_xboole_0(A_49, B_50), C_51) | ~r1_tarski(A_49, C_51))), inference(superposition, [status(thm), theory('equality')], [c_130, c_244])).
% 8.55/3.01  tff(c_14, plain, (![B_13, A_12]: (k9_relat_1(B_13, A_12)!=k1_xboole_0 | ~r1_tarski(A_12, k1_relat_1(B_13)) | k1_xboole_0=A_12 | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.55/3.01  tff(c_16835, plain, (![B_356, A_357, B_358]: (k9_relat_1(B_356, k4_xboole_0(A_357, B_358))!=k1_xboole_0 | k4_xboole_0(A_357, B_358)=k1_xboole_0 | ~v1_relat_1(B_356) | ~r1_tarski(A_357, k1_relat_1(B_356)))), inference(resolution, [status(thm)], [c_495, c_14])).
% 8.55/3.01  tff(c_16891, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_3') | ~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_570, c_16835])).
% 8.55/3.01  tff(c_16925, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_22, c_28, c_16891])).
% 8.55/3.01  tff(c_16927, plain, $false, inference(negUnitSimplification, [status(thm)], [c_243, c_16925])).
% 8.55/3.01  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.55/3.01  
% 8.55/3.01  Inference rules
% 8.55/3.01  ----------------------
% 8.55/3.01  #Ref     : 0
% 8.55/3.01  #Sup     : 4204
% 8.55/3.01  #Fact    : 0
% 8.55/3.01  #Define  : 0
% 8.55/3.01  #Split   : 2
% 8.55/3.01  #Chain   : 0
% 8.55/3.01  #Close   : 0
% 8.55/3.01  
% 8.55/3.01  Ordering : KBO
% 8.55/3.01  
% 8.55/3.01  Simplification rules
% 8.55/3.01  ----------------------
% 8.55/3.01  #Subsume      : 385
% 8.55/3.01  #Demod        : 4708
% 8.55/3.01  #Tautology    : 3146
% 8.55/3.01  #SimpNegUnit  : 2
% 8.55/3.01  #BackRed      : 6
% 8.55/3.01  
% 8.55/3.01  #Partial instantiations: 0
% 8.55/3.01  #Strategies tried      : 1
% 8.55/3.01  
% 8.55/3.01  Timing (in seconds)
% 8.55/3.01  ----------------------
% 8.55/3.01  Preprocessing        : 0.29
% 8.55/3.01  Parsing              : 0.16
% 8.55/3.01  CNF conversion       : 0.02
% 8.55/3.01  Main loop            : 1.96
% 8.55/3.01  Inferencing          : 0.54
% 8.55/3.01  Reduction            : 0.77
% 8.55/3.01  Demodulation         : 0.60
% 8.55/3.01  BG Simplification    : 0.06
% 8.55/3.01  Subsumption          : 0.47
% 8.55/3.01  Abstraction          : 0.09
% 8.55/3.01  MUC search           : 0.00
% 8.55/3.01  Cooper               : 0.00
% 8.55/3.01  Total                : 2.28
% 8.55/3.01  Index Insertion      : 0.00
% 8.55/3.01  Index Deletion       : 0.00
% 8.55/3.01  Index Matching       : 0.00
% 8.55/3.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
