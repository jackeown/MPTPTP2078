%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:17 EST 2020

% Result     : Theorem 3.96s
% Output     : CNFRefutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :   47 (  66 expanded)
%              Number of leaves         :   21 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :   82 ( 140 expanded)
%              Number of equality atoms :   10 (  13 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k8_relat_1(A,C),k8_relat_1(B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k8_relat_1(A,B),k8_relat_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_22,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_154,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(k8_relat_1(A_32,B_33),B_33)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_201,plain,(
    ! [A_44,B_45] :
      ( k2_xboole_0(k8_relat_1(A_44,B_45),B_45) = B_45
      | ~ v1_relat_1(B_45) ) ),
    inference(resolution,[status(thm)],[c_154,c_6])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_207,plain,(
    ! [A_44,B_45,C_5] :
      ( r1_tarski(k8_relat_1(A_44,B_45),C_5)
      | ~ r1_tarski(B_45,C_5)
      | ~ v1_relat_1(B_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_4])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_24,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_253,plain,(
    ! [A_53,B_54,C_55] :
      ( r1_tarski(k8_relat_1(A_53,B_54),C_55)
      | ~ r1_tarski(B_54,C_55)
      | ~ v1_relat_1(B_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_4])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_387,plain,(
    ! [A_65,B_66,C_67] :
      ( k3_xboole_0(k8_relat_1(A_65,B_66),C_67) = k8_relat_1(A_65,B_66)
      | ~ r1_tarski(B_66,C_67)
      | ~ v1_relat_1(B_66) ) ),
    inference(resolution,[status(thm)],[c_253,c_8])).

tff(c_28,plain,(
    ! [B_24,A_25] : k3_xboole_0(B_24,A_25) = k3_xboole_0(A_25,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( v1_relat_1(k3_xboole_0(A_10,B_11))
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_43,plain,(
    ! [B_24,A_25] :
      ( v1_relat_1(k3_xboole_0(B_24,A_25))
      | ~ v1_relat_1(A_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_10])).

tff(c_427,plain,(
    ! [A_68,B_69,C_70] :
      ( v1_relat_1(k8_relat_1(A_68,B_69))
      | ~ v1_relat_1(C_70)
      | ~ r1_tarski(B_69,C_70)
      | ~ v1_relat_1(B_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_387,c_43])).

tff(c_441,plain,(
    ! [A_68] :
      ( v1_relat_1(k8_relat_1(A_68,'#skF_3'))
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_427])).

tff(c_454,plain,(
    ! [A_68] : v1_relat_1(k8_relat_1(A_68,'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_441])).

tff(c_14,plain,(
    ! [B_15,A_14,C_16] :
      ( k8_relat_1(B_15,k8_relat_1(A_14,C_16)) = k8_relat_1(A_14,C_16)
      | ~ r1_tarski(A_14,B_15)
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_216,plain,(
    ! [A_46,B_47,C_48] :
      ( r1_tarski(k8_relat_1(A_46,B_47),k8_relat_1(A_46,C_48))
      | ~ r1_tarski(B_47,C_48)
      | ~ v1_relat_1(C_48)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1983,plain,(
    ! [A_146,C_147,B_148,C_149] :
      ( r1_tarski(k8_relat_1(A_146,C_147),k8_relat_1(B_148,C_149))
      | ~ r1_tarski(k8_relat_1(A_146,C_147),C_149)
      | ~ v1_relat_1(C_149)
      | ~ v1_relat_1(k8_relat_1(A_146,C_147))
      | ~ r1_tarski(A_146,B_148)
      | ~ v1_relat_1(C_147) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_216])).

tff(c_18,plain,(
    ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),k8_relat_1('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2006,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_3'))
    | ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1983,c_18])).

tff(c_2042,plain,(
    ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_20,c_454,c_24,c_2006])).

tff(c_2062,plain,
    ( ~ r1_tarski('#skF_3','#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_207,c_2042])).

tff(c_2075,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_2062])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:56:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.96/1.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.96/1.67  
% 3.96/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.96/1.67  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.96/1.67  
% 3.96/1.67  %Foreground sorts:
% 3.96/1.67  
% 3.96/1.67  
% 3.96/1.67  %Background operators:
% 3.96/1.67  
% 3.96/1.67  
% 3.96/1.67  %Foreground operators:
% 3.96/1.67  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.96/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.96/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.96/1.67  tff('#skF_2', type, '#skF_2': $i).
% 3.96/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.96/1.67  tff('#skF_1', type, '#skF_1': $i).
% 3.96/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.96/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.96/1.67  tff('#skF_4', type, '#skF_4': $i).
% 3.96/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.96/1.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.96/1.67  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.96/1.67  
% 3.96/1.68  tff(f_74, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k8_relat_1(A, C), k8_relat_1(B, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t133_relat_1)).
% 3.96/1.68  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_relat_1)).
% 3.96/1.68  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.96/1.68  tff(f_31, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 3.96/1.68  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.96/1.68  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.96/1.68  tff(f_43, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 3.96/1.68  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_relat_1)).
% 3.96/1.68  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k8_relat_1(A, B), k8_relat_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_relat_1)).
% 3.96/1.68  tff(c_26, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.96/1.68  tff(c_22, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.96/1.68  tff(c_154, plain, (![A_32, B_33]: (r1_tarski(k8_relat_1(A_32, B_33), B_33) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.96/1.68  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.96/1.68  tff(c_201, plain, (![A_44, B_45]: (k2_xboole_0(k8_relat_1(A_44, B_45), B_45)=B_45 | ~v1_relat_1(B_45))), inference(resolution, [status(thm)], [c_154, c_6])).
% 3.96/1.68  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.96/1.68  tff(c_207, plain, (![A_44, B_45, C_5]: (r1_tarski(k8_relat_1(A_44, B_45), C_5) | ~r1_tarski(B_45, C_5) | ~v1_relat_1(B_45))), inference(superposition, [status(thm), theory('equality')], [c_201, c_4])).
% 3.96/1.68  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.96/1.68  tff(c_24, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.96/1.68  tff(c_253, plain, (![A_53, B_54, C_55]: (r1_tarski(k8_relat_1(A_53, B_54), C_55) | ~r1_tarski(B_54, C_55) | ~v1_relat_1(B_54))), inference(superposition, [status(thm), theory('equality')], [c_201, c_4])).
% 3.96/1.68  tff(c_8, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.96/1.68  tff(c_387, plain, (![A_65, B_66, C_67]: (k3_xboole_0(k8_relat_1(A_65, B_66), C_67)=k8_relat_1(A_65, B_66) | ~r1_tarski(B_66, C_67) | ~v1_relat_1(B_66))), inference(resolution, [status(thm)], [c_253, c_8])).
% 3.96/1.68  tff(c_28, plain, (![B_24, A_25]: (k3_xboole_0(B_24, A_25)=k3_xboole_0(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.96/1.68  tff(c_10, plain, (![A_10, B_11]: (v1_relat_1(k3_xboole_0(A_10, B_11)) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.96/1.68  tff(c_43, plain, (![B_24, A_25]: (v1_relat_1(k3_xboole_0(B_24, A_25)) | ~v1_relat_1(A_25))), inference(superposition, [status(thm), theory('equality')], [c_28, c_10])).
% 3.96/1.68  tff(c_427, plain, (![A_68, B_69, C_70]: (v1_relat_1(k8_relat_1(A_68, B_69)) | ~v1_relat_1(C_70) | ~r1_tarski(B_69, C_70) | ~v1_relat_1(B_69))), inference(superposition, [status(thm), theory('equality')], [c_387, c_43])).
% 3.96/1.68  tff(c_441, plain, (![A_68]: (v1_relat_1(k8_relat_1(A_68, '#skF_3')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_427])).
% 3.96/1.68  tff(c_454, plain, (![A_68]: (v1_relat_1(k8_relat_1(A_68, '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_441])).
% 3.96/1.68  tff(c_14, plain, (![B_15, A_14, C_16]: (k8_relat_1(B_15, k8_relat_1(A_14, C_16))=k8_relat_1(A_14, C_16) | ~r1_tarski(A_14, B_15) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.96/1.68  tff(c_216, plain, (![A_46, B_47, C_48]: (r1_tarski(k8_relat_1(A_46, B_47), k8_relat_1(A_46, C_48)) | ~r1_tarski(B_47, C_48) | ~v1_relat_1(C_48) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.96/1.68  tff(c_1983, plain, (![A_146, C_147, B_148, C_149]: (r1_tarski(k8_relat_1(A_146, C_147), k8_relat_1(B_148, C_149)) | ~r1_tarski(k8_relat_1(A_146, C_147), C_149) | ~v1_relat_1(C_149) | ~v1_relat_1(k8_relat_1(A_146, C_147)) | ~r1_tarski(A_146, B_148) | ~v1_relat_1(C_147))), inference(superposition, [status(thm), theory('equality')], [c_14, c_216])).
% 3.96/1.68  tff(c_18, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), k8_relat_1('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.96/1.68  tff(c_2006, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_3')) | ~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1983, c_18])).
% 3.96/1.68  tff(c_2042, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_20, c_454, c_24, c_2006])).
% 3.96/1.68  tff(c_2062, plain, (~r1_tarski('#skF_3', '#skF_4') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_207, c_2042])).
% 3.96/1.68  tff(c_2075, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_2062])).
% 3.96/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.96/1.68  
% 3.96/1.68  Inference rules
% 3.96/1.68  ----------------------
% 3.96/1.68  #Ref     : 0
% 3.96/1.68  #Sup     : 508
% 3.96/1.68  #Fact    : 0
% 3.96/1.68  #Define  : 0
% 3.96/1.68  #Split   : 5
% 3.96/1.68  #Chain   : 0
% 3.96/1.68  #Close   : 0
% 3.96/1.68  
% 3.96/1.68  Ordering : KBO
% 3.96/1.68  
% 3.96/1.68  Simplification rules
% 3.96/1.68  ----------------------
% 3.96/1.68  #Subsume      : 97
% 3.96/1.68  #Demod        : 161
% 3.96/1.68  #Tautology    : 117
% 3.96/1.68  #SimpNegUnit  : 0
% 3.96/1.68  #BackRed      : 0
% 3.96/1.68  
% 3.96/1.68  #Partial instantiations: 0
% 3.96/1.68  #Strategies tried      : 1
% 3.96/1.68  
% 3.96/1.68  Timing (in seconds)
% 3.96/1.68  ----------------------
% 3.96/1.69  Preprocessing        : 0.27
% 3.96/1.69  Parsing              : 0.15
% 3.96/1.69  CNF conversion       : 0.02
% 3.96/1.69  Main loop            : 0.66
% 3.96/1.69  Inferencing          : 0.23
% 3.96/1.69  Reduction            : 0.18
% 3.96/1.69  Demodulation         : 0.12
% 3.96/1.69  BG Simplification    : 0.03
% 3.96/1.69  Subsumption          : 0.16
% 3.96/1.69  Abstraction          : 0.03
% 3.96/1.69  MUC search           : 0.00
% 3.96/1.69  Cooper               : 0.00
% 3.96/1.69  Total                : 0.96
% 3.96/1.69  Index Insertion      : 0.00
% 3.96/1.69  Index Deletion       : 0.00
% 3.96/1.69  Index Matching       : 0.00
% 3.96/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
