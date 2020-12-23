%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:48 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   45 (  65 expanded)
%              Number of leaves         :   20 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   57 ( 113 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => r1_tarski(k5_relat_1(A,k3_xboole_0(B,C)),k3_xboole_0(k5_relat_1(A,B),k5_relat_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(C,A),k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_14,plain,(
    ! [A_16,B_17] :
      ( v1_relat_1(k3_xboole_0(A_16,B_17))
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_6,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k3_xboole_0(A_6,B_7)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] : k2_xboole_0(k3_xboole_0(A_8,B_9),k3_xboole_0(A_8,C_10)) = k3_xboole_0(A_8,k2_xboole_0(B_9,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_11,B_12,C_13] : r1_tarski(k2_xboole_0(k3_xboole_0(A_11,B_12),k3_xboole_0(A_11,C_13)),k2_xboole_0(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_52,plain,(
    ! [A_37,B_38,C_39] : r1_tarski(k3_xboole_0(A_37,k2_xboole_0(B_38,C_39)),k2_xboole_0(B_38,C_39)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_55,plain,(
    ! [A_37,A_6,B_7] : r1_tarski(k3_xboole_0(A_37,A_6),k2_xboole_0(A_6,k3_xboole_0(A_6,B_7))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_52])).

tff(c_59,plain,(
    ! [A_37,A_6] : r1_tarski(k3_xboole_0(A_37,A_6),A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_55])).

tff(c_16,plain,(
    ! [C_24,A_18,B_22] :
      ( r1_tarski(k5_relat_1(C_24,A_18),k5_relat_1(C_24,B_22))
      | ~ r1_tarski(A_18,B_22)
      | ~ v1_relat_1(C_24)
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_77,plain,(
    ! [A_44,B_45,C_46] :
      ( r1_tarski(A_44,k3_xboole_0(B_45,C_46))
      | ~ r1_tarski(A_44,C_46)
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k3_xboole_0(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_81,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k5_relat_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k5_relat_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_77,c_18])).

tff(c_150,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_153,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_2')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_150])).

tff(c_156,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24,c_2,c_153])).

tff(c_159,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_156])).

tff(c_163,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_159])).

tff(c_164,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k5_relat_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_168,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_164])).

tff(c_171,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_24,c_59,c_168])).

tff(c_174,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_171])).

tff(c_178,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_174])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:44:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.20  
% 1.95/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.20  %$ r1_tarski > v1_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.95/1.20  
% 1.95/1.20  %Foreground sorts:
% 1.95/1.20  
% 1.95/1.20  
% 1.95/1.20  %Background operators:
% 1.95/1.20  
% 1.95/1.20  
% 1.95/1.20  %Foreground operators:
% 1.95/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.95/1.20  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.95/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.95/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.95/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.95/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.95/1.20  
% 1.95/1.22  tff(f_68, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(A, k3_xboole_0(B, C)), k3_xboole_0(k5_relat_1(A, B), k5_relat_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relat_1)).
% 1.95/1.22  tff(f_45, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 1.95/1.22  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 1.95/1.22  tff(f_37, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_xboole_1)).
% 1.95/1.22  tff(f_39, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 1.95/1.22  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(C, A), k5_relat_1(C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relat_1)).
% 1.95/1.22  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.95/1.22  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 1.95/1.22  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.95/1.22  tff(c_14, plain, (![A_16, B_17]: (v1_relat_1(k3_xboole_0(A_16, B_17)) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.95/1.22  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.95/1.22  tff(c_24, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.95/1.22  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k3_xboole_0(A_6, B_7))=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.95/1.22  tff(c_8, plain, (![A_8, B_9, C_10]: (k2_xboole_0(k3_xboole_0(A_8, B_9), k3_xboole_0(A_8, C_10))=k3_xboole_0(A_8, k2_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.95/1.22  tff(c_10, plain, (![A_11, B_12, C_13]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_11, B_12), k3_xboole_0(A_11, C_13)), k2_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.95/1.22  tff(c_52, plain, (![A_37, B_38, C_39]: (r1_tarski(k3_xboole_0(A_37, k2_xboole_0(B_38, C_39)), k2_xboole_0(B_38, C_39)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 1.95/1.22  tff(c_55, plain, (![A_37, A_6, B_7]: (r1_tarski(k3_xboole_0(A_37, A_6), k2_xboole_0(A_6, k3_xboole_0(A_6, B_7))))), inference(superposition, [status(thm), theory('equality')], [c_6, c_52])).
% 1.95/1.22  tff(c_59, plain, (![A_37, A_6]: (r1_tarski(k3_xboole_0(A_37, A_6), A_6))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_55])).
% 1.95/1.22  tff(c_16, plain, (![C_24, A_18, B_22]: (r1_tarski(k5_relat_1(C_24, A_18), k5_relat_1(C_24, B_22)) | ~r1_tarski(A_18, B_22) | ~v1_relat_1(C_24) | ~v1_relat_1(B_22) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.95/1.22  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.95/1.22  tff(c_77, plain, (![A_44, B_45, C_46]: (r1_tarski(A_44, k3_xboole_0(B_45, C_46)) | ~r1_tarski(A_44, C_46) | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.95/1.22  tff(c_18, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k3_xboole_0(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.95/1.22  tff(c_81, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k5_relat_1('#skF_1', '#skF_3')) | ~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k5_relat_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_77, c_18])).
% 1.95/1.22  tff(c_150, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k5_relat_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_81])).
% 1.95/1.22  tff(c_153, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_2') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_150])).
% 1.95/1.22  tff(c_156, plain, (~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24, c_2, c_153])).
% 1.95/1.22  tff(c_159, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_14, c_156])).
% 1.95/1.22  tff(c_163, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_159])).
% 1.95/1.22  tff(c_164, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k5_relat_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_81])).
% 1.95/1.22  tff(c_168, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_3') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_164])).
% 1.95/1.22  tff(c_171, plain, (~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_24, c_59, c_168])).
% 1.95/1.22  tff(c_174, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_14, c_171])).
% 1.95/1.22  tff(c_178, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_174])).
% 1.95/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.22  
% 1.95/1.22  Inference rules
% 1.95/1.22  ----------------------
% 1.95/1.22  #Ref     : 0
% 1.95/1.22  #Sup     : 33
% 1.95/1.22  #Fact    : 0
% 1.95/1.22  #Define  : 0
% 1.95/1.22  #Split   : 1
% 1.95/1.22  #Chain   : 0
% 1.95/1.22  #Close   : 0
% 1.95/1.22  
% 1.95/1.22  Ordering : KBO
% 1.95/1.22  
% 1.95/1.22  Simplification rules
% 1.95/1.22  ----------------------
% 1.95/1.22  #Subsume      : 0
% 1.95/1.22  #Demod        : 19
% 1.95/1.22  #Tautology    : 20
% 1.95/1.22  #SimpNegUnit  : 0
% 1.95/1.22  #BackRed      : 0
% 1.95/1.22  
% 1.95/1.22  #Partial instantiations: 0
% 1.95/1.22  #Strategies tried      : 1
% 1.95/1.22  
% 1.95/1.22  Timing (in seconds)
% 1.95/1.22  ----------------------
% 1.95/1.22  Preprocessing        : 0.29
% 1.95/1.22  Parsing              : 0.16
% 1.95/1.22  CNF conversion       : 0.02
% 1.95/1.22  Main loop            : 0.17
% 1.95/1.22  Inferencing          : 0.07
% 1.95/1.22  Reduction            : 0.05
% 1.95/1.22  Demodulation         : 0.04
% 1.95/1.22  BG Simplification    : 0.01
% 1.95/1.22  Subsumption          : 0.03
% 1.95/1.22  Abstraction          : 0.01
% 1.95/1.22  MUC search           : 0.00
% 1.95/1.22  Cooper               : 0.00
% 1.95/1.22  Total                : 0.49
% 1.95/1.22  Index Insertion      : 0.00
% 1.95/1.22  Index Deletion       : 0.00
% 1.95/1.22  Index Matching       : 0.00
% 1.95/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
