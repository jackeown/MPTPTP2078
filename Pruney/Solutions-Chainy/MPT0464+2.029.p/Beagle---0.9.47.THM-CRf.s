%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:47 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 122 expanded)
%              Number of leaves         :   21 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :   70 ( 185 expanded)
%              Number of equality atoms :    9 (  58 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => r1_tarski(k5_relat_1(A,k3_xboole_0(B,C)),k3_xboole_0(k5_relat_1(A,B),k5_relat_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_45,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ! [D] :
                  ( v1_relat_1(D)
                 => ( ( r1_tarski(A,B)
                      & r1_tarski(C,D) )
                   => r1_tarski(k5_relat_1(A,C),k5_relat_1(B,D)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_75,plain,(
    ! [A_44,B_45] : k1_setfam_1(k2_tarski(A_44,B_45)) = k3_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_90,plain,(
    ! [B_46,A_47] : k1_setfam_1(k2_tarski(B_46,A_47)) = k3_xboole_0(A_47,B_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_75])).

tff(c_16,plain,(
    ! [A_12,B_13] : k1_setfam_1(k2_tarski(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_114,plain,(
    ! [B_48,A_49] : k3_xboole_0(B_48,A_49) = k3_xboole_0(A_49,B_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_16])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( v1_relat_1(k3_xboole_0(A_14,B_15))
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_132,plain,(
    ! [A_49,B_48] :
      ( v1_relat_1(k3_xboole_0(A_49,B_48))
      | ~ v1_relat_1(B_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_18])).

tff(c_28,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_135,plain,(
    ! [B_48,A_49] : r1_tarski(k3_xboole_0(B_48,A_49),A_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_8])).

tff(c_20,plain,(
    ! [A_16,C_28,B_24,D_30] :
      ( r1_tarski(k5_relat_1(A_16,C_28),k5_relat_1(B_24,D_30))
      | ~ r1_tarski(C_28,D_30)
      | ~ r1_tarski(A_16,B_24)
      | ~ v1_relat_1(D_30)
      | ~ v1_relat_1(C_28)
      | ~ v1_relat_1(B_24)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_218,plain,(
    ! [A_64,B_65,C_66] :
      ( r1_tarski(A_64,k3_xboole_0(B_65,C_66))
      | ~ r1_tarski(A_64,C_66)
      | ~ r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_96,plain,(
    ! [B_46,A_47] : k3_xboole_0(B_46,A_47) = k3_xboole_0(A_47,B_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_16])).

tff(c_22,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k3_xboole_0(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_113,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k3_xboole_0(k5_relat_1('#skF_1','#skF_3'),k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_96,c_22])).

tff(c_258,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_2'))
    | ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_218,c_113])).

tff(c_323,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_258])).

tff(c_605,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_3')
    | ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_323])).

tff(c_608,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_6,c_8,c_605])).

tff(c_611,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_132,c_608])).

tff(c_618,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_611])).

tff(c_619,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_258])).

tff(c_1273,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_2')
    | ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_619])).

tff(c_1276,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_6,c_135,c_1273])).

tff(c_1279,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_132,c_1276])).

tff(c_1286,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1279])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:21:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.40/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.59  
% 3.40/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.60  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 3.40/1.60  
% 3.40/1.60  %Foreground sorts:
% 3.40/1.60  
% 3.40/1.60  
% 3.40/1.60  %Background operators:
% 3.40/1.60  
% 3.40/1.60  
% 3.40/1.60  %Foreground operators:
% 3.40/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.40/1.60  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.40/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.40/1.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.40/1.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.40/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.40/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.40/1.60  tff('#skF_1', type, '#skF_1': $i).
% 3.40/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.40/1.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.40/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.40/1.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.40/1.60  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.40/1.60  
% 3.40/1.61  tff(f_77, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(A, k3_xboole_0(B, C)), k3_xboole_0(k5_relat_1(A, B), k5_relat_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relat_1)).
% 3.40/1.61  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.40/1.61  tff(f_45, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.40/1.61  tff(f_49, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 3.40/1.61  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.40/1.61  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.40/1.61  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k5_relat_1(A, C), k5_relat_1(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relat_1)).
% 3.40/1.61  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 3.40/1.61  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.40/1.61  tff(c_12, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.40/1.61  tff(c_75, plain, (![A_44, B_45]: (k1_setfam_1(k2_tarski(A_44, B_45))=k3_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.40/1.61  tff(c_90, plain, (![B_46, A_47]: (k1_setfam_1(k2_tarski(B_46, A_47))=k3_xboole_0(A_47, B_46))), inference(superposition, [status(thm), theory('equality')], [c_12, c_75])).
% 3.40/1.61  tff(c_16, plain, (![A_12, B_13]: (k1_setfam_1(k2_tarski(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.40/1.61  tff(c_114, plain, (![B_48, A_49]: (k3_xboole_0(B_48, A_49)=k3_xboole_0(A_49, B_48))), inference(superposition, [status(thm), theory('equality')], [c_90, c_16])).
% 3.40/1.61  tff(c_18, plain, (![A_14, B_15]: (v1_relat_1(k3_xboole_0(A_14, B_15)) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.40/1.61  tff(c_132, plain, (![A_49, B_48]: (v1_relat_1(k3_xboole_0(A_49, B_48)) | ~v1_relat_1(B_48))), inference(superposition, [status(thm), theory('equality')], [c_114, c_18])).
% 3.40/1.61  tff(c_28, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.40/1.61  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.40/1.61  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.40/1.61  tff(c_135, plain, (![B_48, A_49]: (r1_tarski(k3_xboole_0(B_48, A_49), A_49))), inference(superposition, [status(thm), theory('equality')], [c_114, c_8])).
% 3.40/1.61  tff(c_20, plain, (![A_16, C_28, B_24, D_30]: (r1_tarski(k5_relat_1(A_16, C_28), k5_relat_1(B_24, D_30)) | ~r1_tarski(C_28, D_30) | ~r1_tarski(A_16, B_24) | ~v1_relat_1(D_30) | ~v1_relat_1(C_28) | ~v1_relat_1(B_24) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.40/1.61  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.40/1.61  tff(c_218, plain, (![A_64, B_65, C_66]: (r1_tarski(A_64, k3_xboole_0(B_65, C_66)) | ~r1_tarski(A_64, C_66) | ~r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.40/1.61  tff(c_96, plain, (![B_46, A_47]: (k3_xboole_0(B_46, A_47)=k3_xboole_0(A_47, B_46))), inference(superposition, [status(thm), theory('equality')], [c_90, c_16])).
% 3.40/1.61  tff(c_22, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k3_xboole_0(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.40/1.61  tff(c_113, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k3_xboole_0(k5_relat_1('#skF_1', '#skF_3'), k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_96, c_22])).
% 3.40/1.61  tff(c_258, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_2')) | ~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_218, c_113])).
% 3.40/1.61  tff(c_323, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_258])).
% 3.40/1.61  tff(c_605, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_3') | ~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_20, c_323])).
% 3.40/1.61  tff(c_608, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_6, c_8, c_605])).
% 3.40/1.61  tff(c_611, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_132, c_608])).
% 3.40/1.61  tff(c_618, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_611])).
% 3.40/1.61  tff(c_619, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_258])).
% 3.40/1.61  tff(c_1273, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_2') | ~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_20, c_619])).
% 3.40/1.61  tff(c_1276, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_6, c_135, c_1273])).
% 3.40/1.61  tff(c_1279, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_132, c_1276])).
% 3.40/1.61  tff(c_1286, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_1279])).
% 3.40/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.61  
% 3.40/1.61  Inference rules
% 3.40/1.61  ----------------------
% 3.40/1.61  #Ref     : 0
% 3.40/1.61  #Sup     : 309
% 3.40/1.61  #Fact    : 0
% 3.40/1.61  #Define  : 0
% 3.40/1.61  #Split   : 1
% 3.40/1.61  #Chain   : 0
% 3.40/1.61  #Close   : 0
% 3.40/1.61  
% 3.40/1.61  Ordering : KBO
% 3.40/1.61  
% 3.40/1.61  Simplification rules
% 3.40/1.61  ----------------------
% 3.40/1.61  #Subsume      : 47
% 3.40/1.61  #Demod        : 256
% 3.40/1.61  #Tautology    : 159
% 3.40/1.61  #SimpNegUnit  : 0
% 3.40/1.61  #BackRed      : 1
% 3.40/1.61  
% 3.40/1.61  #Partial instantiations: 0
% 3.40/1.61  #Strategies tried      : 1
% 3.40/1.61  
% 3.40/1.61  Timing (in seconds)
% 3.40/1.61  ----------------------
% 3.40/1.61  Preprocessing        : 0.31
% 3.40/1.61  Parsing              : 0.15
% 3.40/1.61  CNF conversion       : 0.02
% 3.40/1.61  Main loop            : 0.47
% 3.40/1.61  Inferencing          : 0.14
% 3.40/1.61  Reduction            : 0.20
% 3.40/1.61  Demodulation         : 0.17
% 3.40/1.61  BG Simplification    : 0.02
% 3.40/1.61  Subsumption          : 0.08
% 3.40/1.61  Abstraction          : 0.03
% 3.40/1.61  MUC search           : 0.00
% 3.40/1.61  Cooper               : 0.00
% 3.40/1.61  Total                : 0.82
% 3.40/1.61  Index Insertion      : 0.00
% 3.40/1.61  Index Deletion       : 0.00
% 3.40/1.61  Index Matching       : 0.00
% 3.40/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
