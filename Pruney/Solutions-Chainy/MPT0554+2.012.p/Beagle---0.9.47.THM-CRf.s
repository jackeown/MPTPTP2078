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
% DateTime   : Thu Dec  3 10:01:04 EST 2020

% Result     : Theorem 5.01s
% Output     : CNFRefutation 5.25s
% Verified   : 
% Statistics : Number of formulae       :   44 (  72 expanded)
%              Number of leaves         :   16 (  31 expanded)
%              Depth                    :   15
%              Number of atoms          :   68 ( 128 expanded)
%              Number of equality atoms :   14 (  25 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k9_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_relat_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_18,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_tarski(k2_xboole_0(A_8,C_10),B_9)
      | ~ r1_tarski(C_10,B_9)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    ! [B_17,A_18] :
      ( B_17 = A_18
      | ~ r1_tarski(B_17,A_18)
      | ~ r1_tarski(A_18,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    ! [A_25,B_26] :
      ( k2_xboole_0(A_25,B_26) = A_25
      | ~ r1_tarski(k2_xboole_0(A_25,B_26),A_25) ) ),
    inference(resolution,[status(thm)],[c_10,c_24])).

tff(c_50,plain,(
    ! [B_9,C_10] :
      ( k2_xboole_0(B_9,C_10) = B_9
      | ~ r1_tarski(C_10,B_9)
      | ~ r1_tarski(B_9,B_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_46])).

tff(c_59,plain,(
    ! [B_27,C_28] :
      ( k2_xboole_0(B_27,C_28) = B_27
      | ~ r1_tarski(C_28,B_27) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_50])).

tff(c_78,plain,(
    ! [B_2] : k2_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_59])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_306,plain,(
    ! [C_45,B_46,A_47] :
      ( k2_xboole_0(k2_xboole_0(C_45,B_46),A_47) = k2_xboole_0(C_45,B_46)
      | ~ r1_tarski(A_47,B_46) ) ),
    inference(resolution,[status(thm)],[c_8,c_59])).

tff(c_381,plain,(
    ! [A_48,C_49,B_50,A_51] :
      ( r1_tarski(A_48,k2_xboole_0(C_49,B_50))
      | ~ r1_tarski(A_48,A_51)
      | ~ r1_tarski(A_51,B_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_8])).

tff(c_679,plain,(
    ! [A_65,C_66,B_67,B_68] :
      ( r1_tarski(A_65,k2_xboole_0(C_66,B_67))
      | ~ r1_tarski(k2_xboole_0(A_65,B_68),B_67) ) ),
    inference(resolution,[status(thm)],[c_10,c_381])).

tff(c_771,plain,(
    ! [A_73,C_74,B_75] : r1_tarski(A_73,k2_xboole_0(C_74,k2_xboole_0(A_73,B_75))) ),
    inference(resolution,[status(thm)],[c_6,c_679])).

tff(c_818,plain,(
    ! [B_2,C_74] : r1_tarski(B_2,k2_xboole_0(C_74,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_771])).

tff(c_42,plain,(
    ! [A_22,C_23,B_24] :
      ( r1_tarski(k2_xboole_0(A_22,C_23),B_24)
      | ~ r1_tarski(C_23,B_24)
      | ~ r1_tarski(A_22,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1220,plain,(
    ! [A_88,C_89,B_90] :
      ( k2_xboole_0(A_88,C_89) = B_90
      | ~ r1_tarski(B_90,k2_xboole_0(A_88,C_89))
      | ~ r1_tarski(C_89,B_90)
      | ~ r1_tarski(A_88,B_90) ) ),
    inference(resolution,[status(thm)],[c_42,c_2])).

tff(c_1235,plain,(
    ! [C_74,B_2] :
      ( k2_xboole_0(C_74,B_2) = B_2
      | ~ r1_tarski(B_2,B_2)
      | ~ r1_tarski(C_74,B_2) ) ),
    inference(resolution,[status(thm)],[c_818,c_1220])).

tff(c_1358,plain,(
    ! [C_93,B_94] :
      ( k2_xboole_0(C_93,B_94) = B_94
      | ~ r1_tarski(C_93,B_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1235])).

tff(c_1435,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_18,c_1358])).

tff(c_136,plain,(
    ! [C_31,A_32,B_33] :
      ( k2_xboole_0(k9_relat_1(C_31,A_32),k9_relat_1(C_31,B_33)) = k9_relat_1(C_31,k2_xboole_0(A_32,B_33))
      | ~ v1_relat_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_155,plain,(
    ! [C_31,A_32,B_33] :
      ( r1_tarski(k9_relat_1(C_31,A_32),k9_relat_1(C_31,k2_xboole_0(A_32,B_33)))
      | ~ v1_relat_1(C_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_10])).

tff(c_2285,plain,(
    ! [C_109] :
      ( r1_tarski(k9_relat_1(C_109,'#skF_1'),k9_relat_1(C_109,'#skF_2'))
      | ~ v1_relat_1(C_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1435,c_155])).

tff(c_16,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2298,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2285,c_16])).

tff(c_2306,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2298])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:17:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.01/2.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.01/2.28  
% 5.01/2.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.01/2.28  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 5.01/2.28  
% 5.01/2.28  %Foreground sorts:
% 5.01/2.28  
% 5.01/2.28  
% 5.01/2.28  %Background operators:
% 5.01/2.28  
% 5.01/2.28  
% 5.01/2.28  %Foreground operators:
% 5.01/2.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.01/2.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.01/2.28  tff('#skF_2', type, '#skF_2': $i).
% 5.01/2.28  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.01/2.28  tff('#skF_3', type, '#skF_3': $i).
% 5.01/2.28  tff('#skF_1', type, '#skF_1': $i).
% 5.01/2.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.01/2.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.01/2.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.01/2.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.01/2.28  
% 5.25/2.30  tff(f_54, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 5.25/2.30  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.25/2.30  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 5.25/2.30  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.25/2.30  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 5.25/2.30  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (k9_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t153_relat_1)).
% 5.25/2.30  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.25/2.30  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.25/2.30  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.25/2.30  tff(c_12, plain, (![A_8, C_10, B_9]: (r1_tarski(k2_xboole_0(A_8, C_10), B_9) | ~r1_tarski(C_10, B_9) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.25/2.30  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.25/2.30  tff(c_24, plain, (![B_17, A_18]: (B_17=A_18 | ~r1_tarski(B_17, A_18) | ~r1_tarski(A_18, B_17))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.25/2.30  tff(c_46, plain, (![A_25, B_26]: (k2_xboole_0(A_25, B_26)=A_25 | ~r1_tarski(k2_xboole_0(A_25, B_26), A_25))), inference(resolution, [status(thm)], [c_10, c_24])).
% 5.25/2.30  tff(c_50, plain, (![B_9, C_10]: (k2_xboole_0(B_9, C_10)=B_9 | ~r1_tarski(C_10, B_9) | ~r1_tarski(B_9, B_9))), inference(resolution, [status(thm)], [c_12, c_46])).
% 5.25/2.30  tff(c_59, plain, (![B_27, C_28]: (k2_xboole_0(B_27, C_28)=B_27 | ~r1_tarski(C_28, B_27))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_50])).
% 5.25/2.30  tff(c_78, plain, (![B_2]: (k2_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_59])).
% 5.25/2.30  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.25/2.30  tff(c_306, plain, (![C_45, B_46, A_47]: (k2_xboole_0(k2_xboole_0(C_45, B_46), A_47)=k2_xboole_0(C_45, B_46) | ~r1_tarski(A_47, B_46))), inference(resolution, [status(thm)], [c_8, c_59])).
% 5.25/2.30  tff(c_381, plain, (![A_48, C_49, B_50, A_51]: (r1_tarski(A_48, k2_xboole_0(C_49, B_50)) | ~r1_tarski(A_48, A_51) | ~r1_tarski(A_51, B_50))), inference(superposition, [status(thm), theory('equality')], [c_306, c_8])).
% 5.25/2.30  tff(c_679, plain, (![A_65, C_66, B_67, B_68]: (r1_tarski(A_65, k2_xboole_0(C_66, B_67)) | ~r1_tarski(k2_xboole_0(A_65, B_68), B_67))), inference(resolution, [status(thm)], [c_10, c_381])).
% 5.25/2.30  tff(c_771, plain, (![A_73, C_74, B_75]: (r1_tarski(A_73, k2_xboole_0(C_74, k2_xboole_0(A_73, B_75))))), inference(resolution, [status(thm)], [c_6, c_679])).
% 5.25/2.30  tff(c_818, plain, (![B_2, C_74]: (r1_tarski(B_2, k2_xboole_0(C_74, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_78, c_771])).
% 5.25/2.30  tff(c_42, plain, (![A_22, C_23, B_24]: (r1_tarski(k2_xboole_0(A_22, C_23), B_24) | ~r1_tarski(C_23, B_24) | ~r1_tarski(A_22, B_24))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.25/2.30  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.25/2.30  tff(c_1220, plain, (![A_88, C_89, B_90]: (k2_xboole_0(A_88, C_89)=B_90 | ~r1_tarski(B_90, k2_xboole_0(A_88, C_89)) | ~r1_tarski(C_89, B_90) | ~r1_tarski(A_88, B_90))), inference(resolution, [status(thm)], [c_42, c_2])).
% 5.25/2.30  tff(c_1235, plain, (![C_74, B_2]: (k2_xboole_0(C_74, B_2)=B_2 | ~r1_tarski(B_2, B_2) | ~r1_tarski(C_74, B_2))), inference(resolution, [status(thm)], [c_818, c_1220])).
% 5.25/2.30  tff(c_1358, plain, (![C_93, B_94]: (k2_xboole_0(C_93, B_94)=B_94 | ~r1_tarski(C_93, B_94))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1235])).
% 5.25/2.30  tff(c_1435, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_18, c_1358])).
% 5.25/2.30  tff(c_136, plain, (![C_31, A_32, B_33]: (k2_xboole_0(k9_relat_1(C_31, A_32), k9_relat_1(C_31, B_33))=k9_relat_1(C_31, k2_xboole_0(A_32, B_33)) | ~v1_relat_1(C_31))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.25/2.30  tff(c_155, plain, (![C_31, A_32, B_33]: (r1_tarski(k9_relat_1(C_31, A_32), k9_relat_1(C_31, k2_xboole_0(A_32, B_33))) | ~v1_relat_1(C_31))), inference(superposition, [status(thm), theory('equality')], [c_136, c_10])).
% 5.25/2.30  tff(c_2285, plain, (![C_109]: (r1_tarski(k9_relat_1(C_109, '#skF_1'), k9_relat_1(C_109, '#skF_2')) | ~v1_relat_1(C_109))), inference(superposition, [status(thm), theory('equality')], [c_1435, c_155])).
% 5.25/2.30  tff(c_16, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.25/2.30  tff(c_2298, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2285, c_16])).
% 5.25/2.30  tff(c_2306, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_2298])).
% 5.25/2.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.25/2.30  
% 5.25/2.30  Inference rules
% 5.25/2.30  ----------------------
% 5.25/2.30  #Ref     : 0
% 5.25/2.30  #Sup     : 565
% 5.25/2.30  #Fact    : 0
% 5.25/2.30  #Define  : 0
% 5.25/2.30  #Split   : 1
% 5.25/2.30  #Chain   : 0
% 5.25/2.30  #Close   : 0
% 5.25/2.30  
% 5.25/2.30  Ordering : KBO
% 5.25/2.30  
% 5.25/2.30  Simplification rules
% 5.25/2.30  ----------------------
% 5.25/2.30  #Subsume      : 90
% 5.25/2.30  #Demod        : 301
% 5.25/2.30  #Tautology    : 251
% 5.25/2.30  #SimpNegUnit  : 0
% 5.25/2.30  #BackRed      : 0
% 5.25/2.30  
% 5.25/2.30  #Partial instantiations: 0
% 5.25/2.30  #Strategies tried      : 1
% 5.25/2.30  
% 5.25/2.30  Timing (in seconds)
% 5.25/2.30  ----------------------
% 5.25/2.30  Preprocessing        : 0.42
% 5.25/2.30  Parsing              : 0.22
% 5.25/2.30  CNF conversion       : 0.03
% 5.25/2.30  Main loop            : 0.98
% 5.25/2.30  Inferencing          : 0.32
% 5.25/2.30  Reduction            : 0.31
% 5.25/2.30  Demodulation         : 0.24
% 5.25/2.30  BG Simplification    : 0.04
% 5.25/2.30  Subsumption          : 0.23
% 5.25/2.30  Abstraction          : 0.05
% 5.25/2.30  MUC search           : 0.00
% 5.25/2.30  Cooper               : 0.00
% 5.25/2.30  Total                : 1.44
% 5.25/2.30  Index Insertion      : 0.00
% 5.25/2.30  Index Deletion       : 0.00
% 5.25/2.30  Index Matching       : 0.00
% 5.25/2.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
