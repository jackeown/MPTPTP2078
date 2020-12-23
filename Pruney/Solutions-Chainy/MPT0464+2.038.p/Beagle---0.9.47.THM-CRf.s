%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:48 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 101 expanded)
%              Number of leaves         :   20 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :   81 ( 179 expanded)
%              Number of equality atoms :   10 (  27 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k5_relat_1 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_77,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => r1_tarski(k5_relat_1(A,k3_xboole_0(B,C)),k3_xboole_0(k5_relat_1(A,B),k5_relat_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] : k2_xboole_0(k3_xboole_0(A_10,B_11),k3_xboole_0(A_10,C_12)) = k3_xboole_0(A_10,k2_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_13,B_14,C_15] : r1_tarski(k2_xboole_0(k3_xboole_0(A_13,B_14),k3_xboole_0(A_13,C_15)),k2_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_53,plain,(
    ! [A_46,B_47,C_48] : r1_tarski(k3_xboole_0(A_46,k2_xboole_0(B_47,C_48)),k2_xboole_0(B_47,C_48)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16])).

tff(c_58,plain,(
    ! [A_46,A_8,B_9] : r1_tarski(k3_xboole_0(A_46,A_8),k2_xboole_0(A_8,k3_xboole_0(A_8,B_9))) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_53])).

tff(c_63,plain,(
    ! [A_46,A_8] : r1_tarski(k3_xboole_0(A_46,A_8),A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_58])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_73,plain,(
    ! [A_55,B_56,C_57] :
      ( r1_tarski(A_55,k3_xboole_0(B_56,C_57))
      | ~ r1_tarski(A_55,C_57)
      | ~ r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_66,plain,(
    ! [A_49,A_50] : r1_tarski(k3_xboole_0(A_49,A_50),A_50) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_58])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_69,plain,(
    ! [A_49,A_50] :
      ( k3_xboole_0(A_49,A_50) = A_50
      | ~ r1_tarski(A_50,k3_xboole_0(A_49,A_50)) ) ),
    inference(resolution,[status(thm)],[c_66,c_2])).

tff(c_77,plain,(
    ! [B_56,C_57] :
      ( k3_xboole_0(B_56,C_57) = C_57
      | ~ r1_tarski(C_57,C_57)
      | ~ r1_tarski(C_57,B_56) ) ),
    inference(resolution,[status(thm)],[c_73,c_69])).

tff(c_662,plain,(
    ! [B_89,C_90] :
      ( k3_xboole_0(B_89,C_90) = C_90
      | ~ r1_tarski(C_90,B_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_77])).

tff(c_993,plain,(
    ! [A_105,A_106] : k3_xboole_0(A_105,k3_xboole_0(A_106,A_105)) = k3_xboole_0(A_106,A_105) ),
    inference(resolution,[status(thm)],[c_63,c_662])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( v1_relat_1(k3_xboole_0(A_16,B_17))
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1033,plain,(
    ! [A_106,A_105] :
      ( v1_relat_1(k3_xboole_0(A_106,A_105))
      | ~ v1_relat_1(A_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_993,c_18])).

tff(c_28,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_20,plain,(
    ! [A_18,C_30,B_26,D_32] :
      ( r1_tarski(k5_relat_1(A_18,C_30),k5_relat_1(B_26,D_32))
      | ~ r1_tarski(C_30,D_32)
      | ~ r1_tarski(A_18,B_26)
      | ~ v1_relat_1(D_32)
      | ~ v1_relat_1(C_30)
      | ~ v1_relat_1(B_26)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k3_xboole_0(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_93,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k5_relat_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k5_relat_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_73,c_22])).

tff(c_183,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_576,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_2')
    | ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_183])).

tff(c_579,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_6,c_8,c_576])).

tff(c_582,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_579])).

tff(c_586,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_582])).

tff(c_587,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k5_relat_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_1277,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_3')
    | ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_587])).

tff(c_1280,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_6,c_63,c_1277])).

tff(c_1283,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1033,c_1280])).

tff(c_1290,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1283])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:01:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.46  
% 2.54/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.46  %$ r1_tarski > v1_relat_1 > k5_relat_1 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.94/1.46  
% 2.94/1.46  %Foreground sorts:
% 2.94/1.46  
% 2.94/1.46  
% 2.94/1.46  %Background operators:
% 2.94/1.46  
% 2.94/1.46  
% 2.94/1.46  %Foreground operators:
% 2.94/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.94/1.46  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.94/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.94/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.94/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.94/1.46  tff('#skF_1', type, '#skF_1': $i).
% 2.94/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.94/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.94/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.94/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.94/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.94/1.46  
% 2.94/1.48  tff(f_77, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(A, k3_xboole_0(B, C)), k3_xboole_0(k5_relat_1(A, B), k5_relat_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relat_1)).
% 2.94/1.48  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.94/1.48  tff(f_43, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_xboole_1)).
% 2.94/1.48  tff(f_45, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 2.94/1.48  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.94/1.48  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.94/1.48  tff(f_49, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 2.94/1.48  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k5_relat_1(A, C), k5_relat_1(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relat_1)).
% 2.94/1.48  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.94/1.48  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.94/1.48  tff(c_12, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k3_xboole_0(A_8, B_9))=A_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.94/1.48  tff(c_14, plain, (![A_10, B_11, C_12]: (k2_xboole_0(k3_xboole_0(A_10, B_11), k3_xboole_0(A_10, C_12))=k3_xboole_0(A_10, k2_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.94/1.48  tff(c_16, plain, (![A_13, B_14, C_15]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_13, B_14), k3_xboole_0(A_13, C_15)), k2_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.94/1.48  tff(c_53, plain, (![A_46, B_47, C_48]: (r1_tarski(k3_xboole_0(A_46, k2_xboole_0(B_47, C_48)), k2_xboole_0(B_47, C_48)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16])).
% 2.94/1.48  tff(c_58, plain, (![A_46, A_8, B_9]: (r1_tarski(k3_xboole_0(A_46, A_8), k2_xboole_0(A_8, k3_xboole_0(A_8, B_9))))), inference(superposition, [status(thm), theory('equality')], [c_12, c_53])).
% 2.94/1.48  tff(c_63, plain, (![A_46, A_8]: (r1_tarski(k3_xboole_0(A_46, A_8), A_8))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_58])).
% 2.94/1.48  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.94/1.48  tff(c_73, plain, (![A_55, B_56, C_57]: (r1_tarski(A_55, k3_xboole_0(B_56, C_57)) | ~r1_tarski(A_55, C_57) | ~r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.94/1.48  tff(c_66, plain, (![A_49, A_50]: (r1_tarski(k3_xboole_0(A_49, A_50), A_50))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_58])).
% 2.94/1.48  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.94/1.48  tff(c_69, plain, (![A_49, A_50]: (k3_xboole_0(A_49, A_50)=A_50 | ~r1_tarski(A_50, k3_xboole_0(A_49, A_50)))), inference(resolution, [status(thm)], [c_66, c_2])).
% 2.94/1.48  tff(c_77, plain, (![B_56, C_57]: (k3_xboole_0(B_56, C_57)=C_57 | ~r1_tarski(C_57, C_57) | ~r1_tarski(C_57, B_56))), inference(resolution, [status(thm)], [c_73, c_69])).
% 2.94/1.48  tff(c_662, plain, (![B_89, C_90]: (k3_xboole_0(B_89, C_90)=C_90 | ~r1_tarski(C_90, B_89))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_77])).
% 2.94/1.48  tff(c_993, plain, (![A_105, A_106]: (k3_xboole_0(A_105, k3_xboole_0(A_106, A_105))=k3_xboole_0(A_106, A_105))), inference(resolution, [status(thm)], [c_63, c_662])).
% 2.94/1.48  tff(c_18, plain, (![A_16, B_17]: (v1_relat_1(k3_xboole_0(A_16, B_17)) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.94/1.48  tff(c_1033, plain, (![A_106, A_105]: (v1_relat_1(k3_xboole_0(A_106, A_105)) | ~v1_relat_1(A_105))), inference(superposition, [status(thm), theory('equality')], [c_993, c_18])).
% 2.94/1.48  tff(c_28, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.94/1.48  tff(c_20, plain, (![A_18, C_30, B_26, D_32]: (r1_tarski(k5_relat_1(A_18, C_30), k5_relat_1(B_26, D_32)) | ~r1_tarski(C_30, D_32) | ~r1_tarski(A_18, B_26) | ~v1_relat_1(D_32) | ~v1_relat_1(C_30) | ~v1_relat_1(B_26) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.94/1.48  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.94/1.48  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.94/1.48  tff(c_22, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k3_xboole_0(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.94/1.48  tff(c_93, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k5_relat_1('#skF_1', '#skF_3')) | ~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k5_relat_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_73, c_22])).
% 2.94/1.48  tff(c_183, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k5_relat_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_93])).
% 2.94/1.48  tff(c_576, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_2') | ~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_20, c_183])).
% 2.94/1.48  tff(c_579, plain, (~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_6, c_8, c_576])).
% 2.94/1.48  tff(c_582, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_18, c_579])).
% 2.94/1.48  tff(c_586, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_582])).
% 2.94/1.48  tff(c_587, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k5_relat_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_93])).
% 2.94/1.48  tff(c_1277, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_3') | ~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_20, c_587])).
% 2.94/1.48  tff(c_1280, plain, (~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_6, c_63, c_1277])).
% 2.94/1.48  tff(c_1283, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1033, c_1280])).
% 2.94/1.48  tff(c_1290, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_1283])).
% 2.94/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.48  
% 2.94/1.48  Inference rules
% 2.94/1.48  ----------------------
% 2.94/1.48  #Ref     : 0
% 2.94/1.48  #Sup     : 313
% 2.94/1.48  #Fact    : 0
% 2.94/1.48  #Define  : 0
% 2.94/1.48  #Split   : 1
% 2.94/1.48  #Chain   : 0
% 2.94/1.48  #Close   : 0
% 2.94/1.48  
% 2.94/1.48  Ordering : KBO
% 2.94/1.48  
% 2.94/1.48  Simplification rules
% 2.94/1.48  ----------------------
% 2.94/1.48  #Subsume      : 11
% 2.94/1.48  #Demod        : 259
% 2.94/1.48  #Tautology    : 211
% 2.94/1.48  #SimpNegUnit  : 0
% 2.94/1.48  #BackRed      : 0
% 2.94/1.48  
% 2.94/1.48  #Partial instantiations: 0
% 2.94/1.48  #Strategies tried      : 1
% 2.94/1.48  
% 2.94/1.48  Timing (in seconds)
% 2.94/1.48  ----------------------
% 2.94/1.48  Preprocessing        : 0.27
% 2.94/1.48  Parsing              : 0.15
% 2.94/1.48  CNF conversion       : 0.02
% 2.94/1.48  Main loop            : 0.42
% 2.94/1.48  Inferencing          : 0.16
% 2.94/1.48  Reduction            : 0.14
% 2.94/1.48  Demodulation         : 0.11
% 2.94/1.48  BG Simplification    : 0.02
% 2.94/1.48  Subsumption          : 0.07
% 2.94/1.48  Abstraction          : 0.03
% 2.94/1.48  MUC search           : 0.00
% 2.94/1.48  Cooper               : 0.00
% 2.94/1.48  Total                : 0.73
% 2.94/1.48  Index Insertion      : 0.00
% 2.94/1.48  Index Deletion       : 0.00
% 2.94/1.48  Index Matching       : 0.00
% 2.94/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
