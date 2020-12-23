%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:36 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   45 (  56 expanded)
%              Number of leaves         :   25 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   64 (  93 expanded)
%              Number of equality atoms :   22 (  30 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r2_hidden(A,k1_relat_1(B))
         => k2_relat_1(k7_relat_1(B,k1_tarski(A))) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_funct_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_40,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k1_relat_1(C)) )
       => k9_relat_1(C,k2_tarski(A,B)) = k2_tarski(k1_funct_1(C,A),k1_funct_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_funct_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( k5_relat_1(k6_relat_1(A_8),B_9) = k7_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_14,plain,(
    ! [A_10] : v1_relat_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10,plain,(
    ! [A_7] : k2_relat_1(k6_relat_1(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_74,plain,(
    ! [B_23,A_24] :
      ( k9_relat_1(B_23,k2_relat_1(A_24)) = k2_relat_1(k5_relat_1(A_24,B_23))
      | ~ v1_relat_1(B_23)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_83,plain,(
    ! [A_7,B_23] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_7),B_23)) = k9_relat_1(B_23,A_7)
      | ~ v1_relat_1(B_23)
      | ~ v1_relat_1(k6_relat_1(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_74])).

tff(c_88,plain,(
    ! [A_25,B_26] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_25),B_26)) = k9_relat_1(B_26,A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_83])).

tff(c_103,plain,(
    ! [B_27,A_28] :
      ( k2_relat_1(k7_relat_1(B_27,A_28)) = k9_relat_1(B_27,A_28)
      | ~ v1_relat_1(B_27)
      | ~ v1_relat_1(B_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_88])).

tff(c_20,plain,(
    k2_relat_1(k7_relat_1('#skF_2',k1_tarski('#skF_1'))) != k1_tarski(k1_funct_1('#skF_2','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_112,plain,
    ( k9_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_tarski(k1_funct_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_20])).

tff(c_118,plain,(
    k9_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_tarski(k1_funct_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_112])).

tff(c_24,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_22,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_120,plain,(
    ! [C_29,A_30,B_31] :
      ( k2_tarski(k1_funct_1(C_29,A_30),k1_funct_1(C_29,B_31)) = k9_relat_1(C_29,k2_tarski(A_30,B_31))
      | ~ r2_hidden(B_31,k1_relat_1(C_29))
      | ~ r2_hidden(A_30,k1_relat_1(C_29))
      | ~ v1_funct_1(C_29)
      | ~ v1_relat_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_127,plain,(
    ! [C_29,B_31] :
      ( k9_relat_1(C_29,k2_tarski(B_31,B_31)) = k1_tarski(k1_funct_1(C_29,B_31))
      | ~ r2_hidden(B_31,k1_relat_1(C_29))
      | ~ r2_hidden(B_31,k1_relat_1(C_29))
      | ~ v1_funct_1(C_29)
      | ~ v1_relat_1(C_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_4])).

tff(c_139,plain,(
    ! [C_32,B_33] :
      ( k9_relat_1(C_32,k1_tarski(B_33)) = k1_tarski(k1_funct_1(C_32,B_33))
      | ~ r2_hidden(B_33,k1_relat_1(C_32))
      | ~ r2_hidden(B_33,k1_relat_1(C_32))
      | ~ v1_funct_1(C_32)
      | ~ v1_relat_1(C_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_127])).

tff(c_141,plain,
    ( k9_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_tarski(k1_funct_1('#skF_2','#skF_1'))
    | ~ r2_hidden('#skF_1',k1_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_139])).

tff(c_146,plain,(
    k9_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_tarski(k1_funct_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_141])).

tff(c_148,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_146])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:34:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.18  
% 1.71/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.18  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_1
% 1.71/1.18  
% 1.71/1.18  %Foreground sorts:
% 1.71/1.18  
% 1.71/1.18  
% 1.71/1.18  %Background operators:
% 1.71/1.18  
% 1.71/1.18  
% 1.71/1.18  %Foreground operators:
% 1.71/1.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.71/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.71/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.71/1.18  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.71/1.18  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.71/1.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.71/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.71/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.71/1.18  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.71/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.71/1.18  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.71/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.71/1.18  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.71/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.71/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.71/1.18  
% 1.94/1.19  tff(f_67, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k2_relat_1(k7_relat_1(B, k1_tarski(A))) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_funct_1)).
% 1.94/1.19  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 1.94/1.19  tff(f_48, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.94/1.19  tff(f_40, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 1.94/1.19  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 1.94/1.19  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.94/1.19  tff(f_58, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k1_relat_1(C))) => (k9_relat_1(C, k2_tarski(A, B)) = k2_tarski(k1_funct_1(C, A), k1_funct_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_funct_1)).
% 1.94/1.19  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.94/1.19  tff(c_12, plain, (![A_8, B_9]: (k5_relat_1(k6_relat_1(A_8), B_9)=k7_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.94/1.19  tff(c_14, plain, (![A_10]: (v1_relat_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.94/1.19  tff(c_10, plain, (![A_7]: (k2_relat_1(k6_relat_1(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.94/1.19  tff(c_74, plain, (![B_23, A_24]: (k9_relat_1(B_23, k2_relat_1(A_24))=k2_relat_1(k5_relat_1(A_24, B_23)) | ~v1_relat_1(B_23) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.94/1.19  tff(c_83, plain, (![A_7, B_23]: (k2_relat_1(k5_relat_1(k6_relat_1(A_7), B_23))=k9_relat_1(B_23, A_7) | ~v1_relat_1(B_23) | ~v1_relat_1(k6_relat_1(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_74])).
% 1.94/1.19  tff(c_88, plain, (![A_25, B_26]: (k2_relat_1(k5_relat_1(k6_relat_1(A_25), B_26))=k9_relat_1(B_26, A_25) | ~v1_relat_1(B_26))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_83])).
% 1.94/1.19  tff(c_103, plain, (![B_27, A_28]: (k2_relat_1(k7_relat_1(B_27, A_28))=k9_relat_1(B_27, A_28) | ~v1_relat_1(B_27) | ~v1_relat_1(B_27))), inference(superposition, [status(thm), theory('equality')], [c_12, c_88])).
% 1.94/1.19  tff(c_20, plain, (k2_relat_1(k7_relat_1('#skF_2', k1_tarski('#skF_1')))!=k1_tarski(k1_funct_1('#skF_2', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.94/1.19  tff(c_112, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_tarski(k1_funct_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_103, c_20])).
% 1.94/1.19  tff(c_118, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_tarski(k1_funct_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_112])).
% 1.94/1.19  tff(c_24, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.94/1.19  tff(c_22, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.94/1.19  tff(c_4, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.94/1.19  tff(c_120, plain, (![C_29, A_30, B_31]: (k2_tarski(k1_funct_1(C_29, A_30), k1_funct_1(C_29, B_31))=k9_relat_1(C_29, k2_tarski(A_30, B_31)) | ~r2_hidden(B_31, k1_relat_1(C_29)) | ~r2_hidden(A_30, k1_relat_1(C_29)) | ~v1_funct_1(C_29) | ~v1_relat_1(C_29))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.94/1.19  tff(c_127, plain, (![C_29, B_31]: (k9_relat_1(C_29, k2_tarski(B_31, B_31))=k1_tarski(k1_funct_1(C_29, B_31)) | ~r2_hidden(B_31, k1_relat_1(C_29)) | ~r2_hidden(B_31, k1_relat_1(C_29)) | ~v1_funct_1(C_29) | ~v1_relat_1(C_29))), inference(superposition, [status(thm), theory('equality')], [c_120, c_4])).
% 1.94/1.19  tff(c_139, plain, (![C_32, B_33]: (k9_relat_1(C_32, k1_tarski(B_33))=k1_tarski(k1_funct_1(C_32, B_33)) | ~r2_hidden(B_33, k1_relat_1(C_32)) | ~r2_hidden(B_33, k1_relat_1(C_32)) | ~v1_funct_1(C_32) | ~v1_relat_1(C_32))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_127])).
% 1.94/1.19  tff(c_141, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_tarski(k1_funct_1('#skF_2', '#skF_1')) | ~r2_hidden('#skF_1', k1_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_22, c_139])).
% 1.94/1.19  tff(c_146, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_tarski(k1_funct_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_141])).
% 1.94/1.19  tff(c_148, plain, $false, inference(negUnitSimplification, [status(thm)], [c_118, c_146])).
% 1.94/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.19  
% 1.94/1.19  Inference rules
% 1.94/1.19  ----------------------
% 1.94/1.19  #Ref     : 0
% 1.94/1.19  #Sup     : 27
% 1.94/1.19  #Fact    : 0
% 1.94/1.19  #Define  : 0
% 1.94/1.19  #Split   : 0
% 1.94/1.19  #Chain   : 0
% 1.94/1.19  #Close   : 0
% 1.94/1.19  
% 1.94/1.19  Ordering : KBO
% 1.94/1.19  
% 1.94/1.19  Simplification rules
% 1.94/1.19  ----------------------
% 1.94/1.19  #Subsume      : 0
% 1.94/1.19  #Demod        : 8
% 1.94/1.19  #Tautology    : 18
% 1.94/1.19  #SimpNegUnit  : 1
% 1.94/1.19  #BackRed      : 0
% 1.94/1.19  
% 1.94/1.19  #Partial instantiations: 0
% 1.94/1.19  #Strategies tried      : 1
% 1.94/1.19  
% 1.94/1.19  Timing (in seconds)
% 1.94/1.19  ----------------------
% 1.94/1.19  Preprocessing        : 0.29
% 1.94/1.19  Parsing              : 0.16
% 1.94/1.19  CNF conversion       : 0.02
% 1.94/1.19  Main loop            : 0.13
% 1.94/1.19  Inferencing          : 0.06
% 1.94/1.19  Reduction            : 0.04
% 1.94/1.19  Demodulation         : 0.03
% 1.99/1.19  BG Simplification    : 0.01
% 1.99/1.19  Subsumption          : 0.01
% 1.99/1.19  Abstraction          : 0.01
% 1.99/1.19  MUC search           : 0.00
% 1.99/1.19  Cooper               : 0.00
% 1.99/1.19  Total                : 0.45
% 1.99/1.20  Index Insertion      : 0.00
% 1.99/1.20  Index Deletion       : 0.00
% 1.99/1.20  Index Matching       : 0.00
% 1.99/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
