%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:22 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :   54 (  65 expanded)
%              Number of leaves         :   32 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :   48 (  74 expanded)
%              Number of equality atoms :   21 (  29 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_66,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_58,plain,(
    k10_relat_1(k7_relat_1('#skF_4','#skF_5'),'#skF_6') != k10_relat_1('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_64,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1045,plain,(
    ! [A_119,C_120,B_121] :
      ( k3_xboole_0(A_119,k10_relat_1(C_120,B_121)) = k10_relat_1(k7_relat_1(C_120,A_119),B_121)
      | ~ v1_relat_1(C_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_24,plain,(
    ! [B_18,A_17] : k2_tarski(B_18,A_17) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_132,plain,(
    ! [A_62,B_63] : k1_setfam_1(k2_tarski(A_62,B_63)) = k3_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_230,plain,(
    ! [A_76,B_77] : k1_setfam_1(k2_tarski(A_76,B_77)) = k3_xboole_0(B_77,A_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_132])).

tff(c_32,plain,(
    ! [A_28,B_29] : k1_setfam_1(k2_tarski(A_28,B_29)) = k3_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_236,plain,(
    ! [B_77,A_76] : k3_xboole_0(B_77,A_76) = k3_xboole_0(A_76,B_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_32])).

tff(c_60,plain,(
    r1_tarski(k10_relat_1('#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_559,plain,(
    ! [A_107,B_108,C_109] :
      ( r1_tarski(A_107,k3_xboole_0(B_108,C_109))
      | ~ r1_tarski(A_107,C_109)
      | ~ r1_tarski(A_107,B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_16,plain,(
    ! [A_10,B_11] : r1_tarski(k3_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_355,plain,(
    ! [B_81,A_82] :
      ( B_81 = A_82
      | ~ r1_tarski(B_81,A_82)
      | ~ r1_tarski(A_82,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_364,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,k3_xboole_0(A_10,B_11)) ) ),
    inference(resolution,[status(thm)],[c_16,c_355])).

tff(c_575,plain,(
    ! [B_108,C_109] :
      ( k3_xboole_0(B_108,C_109) = B_108
      | ~ r1_tarski(B_108,C_109)
      | ~ r1_tarski(B_108,B_108) ) ),
    inference(resolution,[status(thm)],[c_559,c_364])).

tff(c_607,plain,(
    ! [B_110,C_111] :
      ( k3_xboole_0(B_110,C_111) = B_110
      | ~ r1_tarski(B_110,C_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_575])).

tff(c_629,plain,(
    k3_xboole_0(k10_relat_1('#skF_4','#skF_6'),'#skF_5') = k10_relat_1('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_607])).

tff(c_716,plain,
    ( k3_xboole_0(k10_relat_1('#skF_4','#skF_6'),'#skF_5') = k10_relat_1('#skF_4','#skF_6')
    | ~ r1_tarski(k10_relat_1('#skF_4','#skF_6'),k10_relat_1('#skF_4','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_629,c_364])).

tff(c_747,plain,(
    k3_xboole_0('#skF_5',k10_relat_1('#skF_4','#skF_6')) = k10_relat_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_236,c_716])).

tff(c_1051,plain,
    ( k10_relat_1(k7_relat_1('#skF_4','#skF_5'),'#skF_6') = k10_relat_1('#skF_4','#skF_6')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1045,c_747])).

tff(c_1139,plain,(
    k10_relat_1(k7_relat_1('#skF_4','#skF_5'),'#skF_6') = k10_relat_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1051])).

tff(c_1141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1139])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:26:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.98/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.48  
% 2.98/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.49  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.98/1.49  
% 2.98/1.49  %Foreground sorts:
% 2.98/1.49  
% 2.98/1.49  
% 2.98/1.49  %Background operators:
% 2.98/1.49  
% 2.98/1.49  
% 2.98/1.49  %Foreground operators:
% 2.98/1.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.98/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.98/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.98/1.49  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.98/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.98/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.98/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.98/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.98/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.98/1.49  tff('#skF_5', type, '#skF_5': $i).
% 2.98/1.49  tff('#skF_6', type, '#skF_6': $i).
% 2.98/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.98/1.49  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.98/1.49  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.98/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.98/1.49  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.98/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.98/1.49  tff('#skF_4', type, '#skF_4': $i).
% 2.98/1.49  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.98/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.98/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.98/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.98/1.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.98/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.98/1.49  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.98/1.49  
% 2.98/1.50  tff(f_103, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 2.98/1.50  tff(f_88, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 2.98/1.50  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.98/1.50  tff(f_58, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.98/1.50  tff(f_66, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.98/1.50  tff(f_50, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.98/1.50  tff(f_44, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.98/1.50  tff(c_58, plain, (k10_relat_1(k7_relat_1('#skF_4', '#skF_5'), '#skF_6')!=k10_relat_1('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.98/1.50  tff(c_64, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.98/1.50  tff(c_1045, plain, (![A_119, C_120, B_121]: (k3_xboole_0(A_119, k10_relat_1(C_120, B_121))=k10_relat_1(k7_relat_1(C_120, A_119), B_121) | ~v1_relat_1(C_120))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.98/1.50  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.98/1.50  tff(c_24, plain, (![B_18, A_17]: (k2_tarski(B_18, A_17)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.98/1.50  tff(c_132, plain, (![A_62, B_63]: (k1_setfam_1(k2_tarski(A_62, B_63))=k3_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.98/1.50  tff(c_230, plain, (![A_76, B_77]: (k1_setfam_1(k2_tarski(A_76, B_77))=k3_xboole_0(B_77, A_76))), inference(superposition, [status(thm), theory('equality')], [c_24, c_132])).
% 2.98/1.50  tff(c_32, plain, (![A_28, B_29]: (k1_setfam_1(k2_tarski(A_28, B_29))=k3_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.98/1.50  tff(c_236, plain, (![B_77, A_76]: (k3_xboole_0(B_77, A_76)=k3_xboole_0(A_76, B_77))), inference(superposition, [status(thm), theory('equality')], [c_230, c_32])).
% 2.98/1.50  tff(c_60, plain, (r1_tarski(k10_relat_1('#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.98/1.50  tff(c_559, plain, (![A_107, B_108, C_109]: (r1_tarski(A_107, k3_xboole_0(B_108, C_109)) | ~r1_tarski(A_107, C_109) | ~r1_tarski(A_107, B_108))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.98/1.50  tff(c_16, plain, (![A_10, B_11]: (r1_tarski(k3_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.98/1.50  tff(c_355, plain, (![B_81, A_82]: (B_81=A_82 | ~r1_tarski(B_81, A_82) | ~r1_tarski(A_82, B_81))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.98/1.50  tff(c_364, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, k3_xboole_0(A_10, B_11)))), inference(resolution, [status(thm)], [c_16, c_355])).
% 2.98/1.50  tff(c_575, plain, (![B_108, C_109]: (k3_xboole_0(B_108, C_109)=B_108 | ~r1_tarski(B_108, C_109) | ~r1_tarski(B_108, B_108))), inference(resolution, [status(thm)], [c_559, c_364])).
% 2.98/1.50  tff(c_607, plain, (![B_110, C_111]: (k3_xboole_0(B_110, C_111)=B_110 | ~r1_tarski(B_110, C_111))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_575])).
% 2.98/1.50  tff(c_629, plain, (k3_xboole_0(k10_relat_1('#skF_4', '#skF_6'), '#skF_5')=k10_relat_1('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_60, c_607])).
% 2.98/1.50  tff(c_716, plain, (k3_xboole_0(k10_relat_1('#skF_4', '#skF_6'), '#skF_5')=k10_relat_1('#skF_4', '#skF_6') | ~r1_tarski(k10_relat_1('#skF_4', '#skF_6'), k10_relat_1('#skF_4', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_629, c_364])).
% 2.98/1.50  tff(c_747, plain, (k3_xboole_0('#skF_5', k10_relat_1('#skF_4', '#skF_6'))=k10_relat_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_236, c_716])).
% 2.98/1.50  tff(c_1051, plain, (k10_relat_1(k7_relat_1('#skF_4', '#skF_5'), '#skF_6')=k10_relat_1('#skF_4', '#skF_6') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1045, c_747])).
% 2.98/1.50  tff(c_1139, plain, (k10_relat_1(k7_relat_1('#skF_4', '#skF_5'), '#skF_6')=k10_relat_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1051])).
% 2.98/1.50  tff(c_1141, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1139])).
% 2.98/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.50  
% 2.98/1.50  Inference rules
% 2.98/1.50  ----------------------
% 2.98/1.50  #Ref     : 0
% 2.98/1.50  #Sup     : 260
% 2.98/1.50  #Fact    : 0
% 2.98/1.50  #Define  : 0
% 2.98/1.50  #Split   : 1
% 2.98/1.50  #Chain   : 0
% 2.98/1.50  #Close   : 0
% 2.98/1.50  
% 2.98/1.50  Ordering : KBO
% 2.98/1.50  
% 2.98/1.50  Simplification rules
% 2.98/1.50  ----------------------
% 2.98/1.50  #Subsume      : 23
% 2.98/1.50  #Demod        : 141
% 2.98/1.50  #Tautology    : 155
% 2.98/1.50  #SimpNegUnit  : 1
% 2.98/1.50  #BackRed      : 0
% 2.98/1.50  
% 2.98/1.50  #Partial instantiations: 0
% 2.98/1.50  #Strategies tried      : 1
% 2.98/1.50  
% 2.98/1.50  Timing (in seconds)
% 2.98/1.50  ----------------------
% 2.98/1.50  Preprocessing        : 0.36
% 2.98/1.50  Parsing              : 0.19
% 2.98/1.50  CNF conversion       : 0.03
% 2.98/1.50  Main loop            : 0.32
% 2.98/1.50  Inferencing          : 0.11
% 2.98/1.50  Reduction            : 0.12
% 2.98/1.50  Demodulation         : 0.09
% 2.98/1.50  BG Simplification    : 0.02
% 2.98/1.50  Subsumption          : 0.06
% 2.98/1.50  Abstraction          : 0.02
% 2.98/1.50  MUC search           : 0.00
% 2.98/1.50  Cooper               : 0.00
% 2.98/1.50  Total                : 0.71
% 2.98/1.50  Index Insertion      : 0.00
% 2.98/1.50  Index Deletion       : 0.00
% 2.98/1.50  Index Matching       : 0.00
% 2.98/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
