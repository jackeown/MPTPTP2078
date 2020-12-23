%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:48 EST 2020

% Result     : Theorem 4.42s
% Output     : CNFRefutation 4.67s
% Verified   : 
% Statistics : Number of formulae       :   52 (  71 expanded)
%              Number of leaves         :   25 (  35 expanded)
%              Depth                    :    5
%              Number of atoms          :   58 (  93 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_49,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_55,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k10_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_16,plain,(
    ! [B_14,A_13] : k2_tarski(B_14,A_13) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_65,plain,(
    ! [A_30,B_31] : k1_setfam_1(k2_tarski(A_30,B_31)) = k3_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_89,plain,(
    ! [A_34,B_35] : k1_setfam_1(k2_tarski(A_34,B_35)) = k3_xboole_0(B_35,A_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_65])).

tff(c_22,plain,(
    ! [A_20,B_21] : k1_setfam_1(k2_tarski(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_95,plain,(
    ! [B_35,A_34] : k3_xboole_0(B_35,A_34) = k3_xboole_0(A_34,B_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_22])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_146,plain,(
    ! [A_38,B_39,C_40] :
      ( r1_tarski(A_38,B_39)
      | ~ r1_tarski(A_38,k3_xboole_0(B_39,C_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_158,plain,(
    ! [B_41,C_42] : r1_tarski(k3_xboole_0(B_41,C_42),B_41) ),
    inference(resolution,[status(thm)],[c_6,c_146])).

tff(c_165,plain,(
    ! [B_35,A_34] : r1_tarski(k3_xboole_0(B_35,A_34),A_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_158])).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,k4_xboole_0(B_10,A_9)) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_522,plain,(
    ! [C_77,A_78,B_79] :
      ( k2_xboole_0(k10_relat_1(C_77,A_78),k10_relat_1(C_77,B_79)) = k10_relat_1(C_77,k2_xboole_0(A_78,B_79))
      | ~ v1_relat_1(C_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_14,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3584,plain,(
    ! [C_158,A_159,B_160] :
      ( r1_tarski(k10_relat_1(C_158,A_159),k10_relat_1(C_158,k2_xboole_0(A_159,B_160)))
      | ~ v1_relat_1(C_158) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_522,c_14])).

tff(c_4599,plain,(
    ! [C_177,A_178,B_179] :
      ( r1_tarski(k10_relat_1(C_177,A_178),k10_relat_1(C_177,B_179))
      | ~ v1_relat_1(C_177)
      | ~ r1_tarski(A_178,B_179) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_3584])).

tff(c_157,plain,(
    ! [B_39,C_40] : r1_tarski(k3_xboole_0(B_39,C_40),B_39) ),
    inference(resolution,[status(thm)],[c_6,c_146])).

tff(c_1649,plain,(
    ! [C_111,A_112,B_113] :
      ( r1_tarski(k10_relat_1(C_111,A_112),k10_relat_1(C_111,k2_xboole_0(A_112,B_113)))
      | ~ v1_relat_1(C_111) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_522,c_14])).

tff(c_2527,plain,(
    ! [C_133,A_134,B_135] :
      ( r1_tarski(k10_relat_1(C_133,A_134),k10_relat_1(C_133,B_135))
      | ~ v1_relat_1(C_133)
      | ~ r1_tarski(A_134,B_135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1649])).

tff(c_373,plain,(
    ! [A_67,B_68,C_69] :
      ( r1_tarski(A_67,k3_xboole_0(B_68,C_69))
      | ~ r1_tarski(A_67,C_69)
      | ~ r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_394,plain,
    ( ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_373,c_26])).

tff(c_655,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_394])).

tff(c_2533,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_2527,c_655])).

tff(c_2543,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_28,c_2533])).

tff(c_2544,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_394])).

tff(c_4608,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_4599,c_2544])).

tff(c_4621,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_28,c_4608])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:14:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.42/1.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.42/1.90  
% 4.42/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.42/1.90  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 4.42/1.90  
% 4.42/1.90  %Foreground sorts:
% 4.42/1.90  
% 4.42/1.90  
% 4.42/1.90  %Background operators:
% 4.42/1.90  
% 4.42/1.90  
% 4.42/1.90  %Foreground operators:
% 4.42/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.42/1.90  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.42/1.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.42/1.90  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.42/1.90  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.42/1.90  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.42/1.90  tff('#skF_2', type, '#skF_2': $i).
% 4.42/1.90  tff('#skF_3', type, '#skF_3': $i).
% 4.42/1.90  tff('#skF_1', type, '#skF_1': $i).
% 4.42/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.42/1.90  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.42/1.90  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.42/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.42/1.90  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.42/1.90  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.42/1.90  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.42/1.90  
% 4.67/1.91  tff(f_49, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.67/1.91  tff(f_55, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.67/1.91  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.67/1.91  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 4.67/1.91  tff(f_64, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k10_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_relat_1)).
% 4.67/1.91  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 4.67/1.91  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 4.67/1.91  tff(f_47, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.67/1.91  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 4.67/1.91  tff(c_16, plain, (![B_14, A_13]: (k2_tarski(B_14, A_13)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.67/1.91  tff(c_65, plain, (![A_30, B_31]: (k1_setfam_1(k2_tarski(A_30, B_31))=k3_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.67/1.91  tff(c_89, plain, (![A_34, B_35]: (k1_setfam_1(k2_tarski(A_34, B_35))=k3_xboole_0(B_35, A_34))), inference(superposition, [status(thm), theory('equality')], [c_16, c_65])).
% 4.67/1.91  tff(c_22, plain, (![A_20, B_21]: (k1_setfam_1(k2_tarski(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.67/1.91  tff(c_95, plain, (![B_35, A_34]: (k3_xboole_0(B_35, A_34)=k3_xboole_0(A_34, B_35))), inference(superposition, [status(thm), theory('equality')], [c_89, c_22])).
% 4.67/1.91  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.67/1.91  tff(c_146, plain, (![A_38, B_39, C_40]: (r1_tarski(A_38, B_39) | ~r1_tarski(A_38, k3_xboole_0(B_39, C_40)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.67/1.91  tff(c_158, plain, (![B_41, C_42]: (r1_tarski(k3_xboole_0(B_41, C_42), B_41))), inference(resolution, [status(thm)], [c_6, c_146])).
% 4.67/1.91  tff(c_165, plain, (![B_35, A_34]: (r1_tarski(k3_xboole_0(B_35, A_34), A_34))), inference(superposition, [status(thm), theory('equality')], [c_95, c_158])).
% 4.67/1.91  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.67/1.91  tff(c_12, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k4_xboole_0(B_10, A_9))=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.67/1.91  tff(c_522, plain, (![C_77, A_78, B_79]: (k2_xboole_0(k10_relat_1(C_77, A_78), k10_relat_1(C_77, B_79))=k10_relat_1(C_77, k2_xboole_0(A_78, B_79)) | ~v1_relat_1(C_77))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.67/1.91  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.67/1.91  tff(c_3584, plain, (![C_158, A_159, B_160]: (r1_tarski(k10_relat_1(C_158, A_159), k10_relat_1(C_158, k2_xboole_0(A_159, B_160))) | ~v1_relat_1(C_158))), inference(superposition, [status(thm), theory('equality')], [c_522, c_14])).
% 4.67/1.91  tff(c_4599, plain, (![C_177, A_178, B_179]: (r1_tarski(k10_relat_1(C_177, A_178), k10_relat_1(C_177, B_179)) | ~v1_relat_1(C_177) | ~r1_tarski(A_178, B_179))), inference(superposition, [status(thm), theory('equality')], [c_12, c_3584])).
% 4.67/1.91  tff(c_157, plain, (![B_39, C_40]: (r1_tarski(k3_xboole_0(B_39, C_40), B_39))), inference(resolution, [status(thm)], [c_6, c_146])).
% 4.67/1.91  tff(c_1649, plain, (![C_111, A_112, B_113]: (r1_tarski(k10_relat_1(C_111, A_112), k10_relat_1(C_111, k2_xboole_0(A_112, B_113))) | ~v1_relat_1(C_111))), inference(superposition, [status(thm), theory('equality')], [c_522, c_14])).
% 4.67/1.91  tff(c_2527, plain, (![C_133, A_134, B_135]: (r1_tarski(k10_relat_1(C_133, A_134), k10_relat_1(C_133, B_135)) | ~v1_relat_1(C_133) | ~r1_tarski(A_134, B_135))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1649])).
% 4.67/1.91  tff(c_373, plain, (![A_67, B_68, C_69]: (r1_tarski(A_67, k3_xboole_0(B_68, C_69)) | ~r1_tarski(A_67, C_69) | ~r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.67/1.91  tff(c_26, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.67/1.91  tff(c_394, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_373, c_26])).
% 4.67/1.91  tff(c_655, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_394])).
% 4.67/1.91  tff(c_2533, plain, (~v1_relat_1('#skF_3') | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_2527, c_655])).
% 4.67/1.91  tff(c_2543, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_157, c_28, c_2533])).
% 4.67/1.91  tff(c_2544, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_394])).
% 4.67/1.91  tff(c_4608, plain, (~v1_relat_1('#skF_3') | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_4599, c_2544])).
% 4.67/1.91  tff(c_4621, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_165, c_28, c_4608])).
% 4.67/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.67/1.91  
% 4.67/1.91  Inference rules
% 4.67/1.91  ----------------------
% 4.67/1.91  #Ref     : 0
% 4.67/1.91  #Sup     : 1144
% 4.67/1.91  #Fact    : 0
% 4.67/1.91  #Define  : 0
% 4.67/1.91  #Split   : 2
% 4.67/1.91  #Chain   : 0
% 4.67/1.91  #Close   : 0
% 4.67/1.91  
% 4.67/1.91  Ordering : KBO
% 4.67/1.91  
% 4.67/1.91  Simplification rules
% 4.67/1.91  ----------------------
% 4.67/1.91  #Subsume      : 123
% 4.67/1.91  #Demod        : 1000
% 4.67/1.91  #Tautology    : 682
% 4.67/1.91  #SimpNegUnit  : 0
% 4.67/1.91  #BackRed      : 0
% 4.67/1.91  
% 4.67/1.91  #Partial instantiations: 0
% 4.67/1.91  #Strategies tried      : 1
% 4.67/1.91  
% 4.67/1.91  Timing (in seconds)
% 4.67/1.91  ----------------------
% 4.67/1.91  Preprocessing        : 0.32
% 4.67/1.91  Parsing              : 0.17
% 4.67/1.91  CNF conversion       : 0.02
% 4.67/1.91  Main loop            : 0.78
% 4.67/1.91  Inferencing          : 0.23
% 4.67/1.91  Reduction            : 0.35
% 4.67/1.91  Demodulation         : 0.30
% 4.67/1.91  BG Simplification    : 0.03
% 4.67/1.91  Subsumption          : 0.12
% 4.67/1.91  Abstraction          : 0.04
% 4.67/1.91  MUC search           : 0.00
% 4.67/1.91  Cooper               : 0.00
% 4.67/1.91  Total                : 1.13
% 4.67/1.92  Index Insertion      : 0.00
% 4.67/1.92  Index Deletion       : 0.00
% 4.67/1.92  Index Matching       : 0.00
% 4.67/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
