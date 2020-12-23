%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:49 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   43 (  76 expanded)
%              Number of leaves         :   20 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   56 ( 134 expanded)
%              Number of equality atoms :    8 (  20 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_subset_1 > k5_relat_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_62,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => r1_tarski(k6_subset_1(k5_relat_1(A,B),k5_relat_1(A,C)),k5_relat_1(A,k6_subset_1(B,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(A,k2_xboole_0(B,C)) = k2_xboole_0(k5_relat_1(A,B),k5_relat_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_206,plain,(
    ! [A_58,B_59,C_60] :
      ( k2_xboole_0(k5_relat_1(A_58,B_59),k5_relat_1(A_58,C_60)) = k5_relat_1(A_58,k2_xboole_0(B_59,C_60))
      | ~ v1_relat_1(C_60)
      | ~ v1_relat_1(B_59)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_318,plain,(
    ! [A_67,B_68,C_69] :
      ( r1_tarski(k5_relat_1(A_67,B_68),k5_relat_1(A_67,k2_xboole_0(B_68,C_69)))
      | ~ v1_relat_1(C_69)
      | ~ v1_relat_1(B_68)
      | ~ v1_relat_1(A_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_8])).

tff(c_516,plain,(
    ! [A_85,B_86,A_87] :
      ( r1_tarski(k5_relat_1(A_85,B_86),k5_relat_1(A_85,k2_xboole_0(A_87,B_86)))
      | ~ v1_relat_1(A_87)
      | ~ v1_relat_1(B_86)
      | ~ v1_relat_1(A_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_318])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k4_xboole_0(A_12,B_13))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_133,plain,(
    ! [A_43,B_44,C_45] :
      ( r1_tarski(k4_xboole_0(A_43,B_44),C_45)
      | ~ r1_tarski(A_43,k2_xboole_0(B_44,C_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_10,B_11] : k6_subset_1(A_10,B_11) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ~ r1_tarski(k6_subset_1(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1','#skF_3')),k5_relat_1('#skF_1',k6_subset_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_23,plain,(
    ~ r1_tarski(k4_xboole_0(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1','#skF_3')),k5_relat_1('#skF_1',k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_16])).

tff(c_137,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1','#skF_2'),k2_xboole_0(k5_relat_1('#skF_1','#skF_3'),k5_relat_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')))) ),
    inference(resolution,[status(thm)],[c_133,c_23])).

tff(c_224,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1',k2_xboole_0('#skF_3',k4_xboole_0('#skF_2','#skF_3'))))
    | ~ v1_relat_1(k4_xboole_0('#skF_2','#skF_3'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_137])).

tff(c_263,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1',k2_xboole_0('#skF_3','#skF_2')))
    | ~ v1_relat_1(k4_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_4,c_224])).

tff(c_282,plain,(
    ~ v1_relat_1(k4_xboole_0('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_263])).

tff(c_285,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_282])).

tff(c_289,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_285])).

tff(c_290,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_263])).

tff(c_519,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_516,c_290])).

tff(c_538,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_18,c_519])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n023.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 12:03:51 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.36  
% 2.51/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.36  %$ r1_tarski > v1_relat_1 > k6_subset_1 > k5_relat_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.51/1.36  
% 2.51/1.36  %Foreground sorts:
% 2.51/1.36  
% 2.51/1.36  
% 2.51/1.36  %Background operators:
% 2.51/1.36  
% 2.51/1.36  
% 2.51/1.36  %Foreground operators:
% 2.51/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.51/1.36  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.51/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.51/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.51/1.36  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.51/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.51/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.51/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.51/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.51/1.36  
% 2.51/1.37  tff(f_62, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k6_subset_1(k5_relat_1(A, B), k5_relat_1(A, C)), k5_relat_1(A, k6_subset_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_relat_1)).
% 2.51/1.37  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.51/1.37  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(A, k2_xboole_0(B, C)) = k2_xboole_0(k5_relat_1(A, B), k5_relat_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_relat_1)).
% 2.51/1.37  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.51/1.37  tff(f_41, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_relat_1)).
% 2.51/1.37  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.51/1.37  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 2.51/1.37  tff(f_37, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.51/1.37  tff(c_22, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.51/1.37  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.51/1.37  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.51/1.37  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.51/1.37  tff(c_206, plain, (![A_58, B_59, C_60]: (k2_xboole_0(k5_relat_1(A_58, B_59), k5_relat_1(A_58, C_60))=k5_relat_1(A_58, k2_xboole_0(B_59, C_60)) | ~v1_relat_1(C_60) | ~v1_relat_1(B_59) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.51/1.37  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.51/1.37  tff(c_318, plain, (![A_67, B_68, C_69]: (r1_tarski(k5_relat_1(A_67, B_68), k5_relat_1(A_67, k2_xboole_0(B_68, C_69))) | ~v1_relat_1(C_69) | ~v1_relat_1(B_68) | ~v1_relat_1(A_67))), inference(superposition, [status(thm), theory('equality')], [c_206, c_8])).
% 2.51/1.37  tff(c_516, plain, (![A_85, B_86, A_87]: (r1_tarski(k5_relat_1(A_85, B_86), k5_relat_1(A_85, k2_xboole_0(A_87, B_86))) | ~v1_relat_1(A_87) | ~v1_relat_1(B_86) | ~v1_relat_1(A_85))), inference(superposition, [status(thm), theory('equality')], [c_2, c_318])).
% 2.51/1.37  tff(c_12, plain, (![A_12, B_13]: (v1_relat_1(k4_xboole_0(A_12, B_13)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.51/1.37  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.51/1.37  tff(c_133, plain, (![A_43, B_44, C_45]: (r1_tarski(k4_xboole_0(A_43, B_44), C_45) | ~r1_tarski(A_43, k2_xboole_0(B_44, C_45)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.51/1.37  tff(c_10, plain, (![A_10, B_11]: (k6_subset_1(A_10, B_11)=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.51/1.37  tff(c_16, plain, (~r1_tarski(k6_subset_1(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', '#skF_3')), k5_relat_1('#skF_1', k6_subset_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.51/1.37  tff(c_23, plain, (~r1_tarski(k4_xboole_0(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', '#skF_3')), k5_relat_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_16])).
% 2.51/1.37  tff(c_137, plain, (~r1_tarski(k5_relat_1('#skF_1', '#skF_2'), k2_xboole_0(k5_relat_1('#skF_1', '#skF_3'), k5_relat_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_133, c_23])).
% 2.51/1.37  tff(c_224, plain, (~r1_tarski(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', k2_xboole_0('#skF_3', k4_xboole_0('#skF_2', '#skF_3')))) | ~v1_relat_1(k4_xboole_0('#skF_2', '#skF_3')) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_206, c_137])).
% 2.51/1.37  tff(c_263, plain, (~r1_tarski(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))) | ~v1_relat_1(k4_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_4, c_224])).
% 2.51/1.37  tff(c_282, plain, (~v1_relat_1(k4_xboole_0('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_263])).
% 2.51/1.37  tff(c_285, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_12, c_282])).
% 2.51/1.37  tff(c_289, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_285])).
% 2.51/1.37  tff(c_290, plain, (~r1_tarski(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_263])).
% 2.51/1.37  tff(c_519, plain, (~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_516, c_290])).
% 2.51/1.37  tff(c_538, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_18, c_519])).
% 2.51/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.37  
% 2.51/1.37  Inference rules
% 2.51/1.37  ----------------------
% 2.51/1.37  #Ref     : 0
% 2.51/1.37  #Sup     : 141
% 2.51/1.37  #Fact    : 0
% 2.51/1.37  #Define  : 0
% 2.51/1.37  #Split   : 1
% 2.51/1.37  #Chain   : 0
% 2.51/1.37  #Close   : 0
% 2.51/1.37  
% 2.51/1.37  Ordering : KBO
% 2.51/1.37  
% 2.51/1.37  Simplification rules
% 2.51/1.37  ----------------------
% 2.51/1.37  #Subsume      : 6
% 2.51/1.37  #Demod        : 45
% 2.51/1.37  #Tautology    : 47
% 2.51/1.37  #SimpNegUnit  : 0
% 2.51/1.37  #BackRed      : 0
% 2.51/1.37  
% 2.51/1.37  #Partial instantiations: 0
% 2.51/1.37  #Strategies tried      : 1
% 2.51/1.37  
% 2.51/1.37  Timing (in seconds)
% 2.51/1.37  ----------------------
% 2.51/1.37  Preprocessing        : 0.27
% 2.51/1.37  Parsing              : 0.14
% 2.65/1.37  CNF conversion       : 0.02
% 2.65/1.37  Main loop            : 0.31
% 2.65/1.37  Inferencing          : 0.10
% 2.65/1.37  Reduction            : 0.11
% 2.65/1.37  Demodulation         : 0.09
% 2.65/1.37  BG Simplification    : 0.01
% 2.65/1.37  Subsumption          : 0.07
% 2.65/1.37  Abstraction          : 0.01
% 2.65/1.37  MUC search           : 0.00
% 2.65/1.37  Cooper               : 0.00
% 2.65/1.37  Total                : 0.61
% 2.65/1.37  Index Insertion      : 0.00
% 2.65/1.37  Index Deletion       : 0.00
% 2.65/1.37  Index Matching       : 0.00
% 2.65/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
