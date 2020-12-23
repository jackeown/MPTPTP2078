%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:03 EST 2020

% Result     : Theorem 4.52s
% Output     : CNFRefutation 4.52s
% Verified   : 
% Statistics : Number of formulae       :   56 (  64 expanded)
%              Number of leaves         :   26 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :   66 (  82 expanded)
%              Number of equality atoms :   15 (  17 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_36,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_44,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_28,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_46,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k9_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_relat_1)).

tff(f_58,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_16,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_388,plain,(
    ! [A_57,C_58,B_59] :
      ( r1_tarski(A_57,C_58)
      | ~ r1_tarski(B_59,C_58)
      | ~ r1_tarski(A_57,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_511,plain,(
    ! [A_69,A_70,B_71] :
      ( r1_tarski(A_69,A_70)
      | ~ r1_tarski(A_69,k4_xboole_0(A_70,B_71)) ) ),
    inference(resolution,[status(thm)],[c_16,c_388])).

tff(c_532,plain,(
    ! [A_70,B_71,B_10] : r1_tarski(k4_xboole_0(k4_xboole_0(A_70,B_71),B_10),A_70) ),
    inference(resolution,[status(thm)],[c_16,c_511])).

tff(c_32,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_409,plain,(
    ! [A_57] :
      ( r1_tarski(A_57,'#skF_2')
      | ~ r1_tarski(A_57,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_388])).

tff(c_22,plain,(
    ! [A_15,B_16] : r1_xboole_0(k4_xboole_0(A_15,B_16),B_16) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_253,plain,(
    ! [B_48,A_49] :
      ( ~ r1_xboole_0(B_48,A_49)
      | ~ r1_tarski(B_48,A_49)
      | v1_xboole_0(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_794,plain,(
    ! [A_93,B_94] :
      ( ~ r1_tarski(k4_xboole_0(A_93,B_94),B_94)
      | v1_xboole_0(k4_xboole_0(A_93,B_94)) ) ),
    inference(resolution,[status(thm)],[c_22,c_253])).

tff(c_1351,plain,(
    ! [A_110] :
      ( v1_xboole_0(k4_xboole_0(A_110,'#skF_2'))
      | ~ r1_tarski(k4_xboole_0(A_110,'#skF_2'),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_409,c_794])).

tff(c_1427,plain,(
    ! [B_111] : v1_xboole_0(k4_xboole_0(k4_xboole_0('#skF_1',B_111),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_532,c_1351])).

tff(c_4,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_150,plain,(
    ! [B_36,A_37] :
      ( ~ v1_xboole_0(B_36)
      | B_36 = A_37
      | ~ v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_153,plain,(
    ! [A_37] :
      ( k1_xboole_0 = A_37
      | ~ v1_xboole_0(A_37) ) ),
    inference(resolution,[status(thm)],[c_4,c_150])).

tff(c_1449,plain,(
    ! [B_112] : k4_xboole_0(k4_xboole_0('#skF_1',B_112),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1427,c_153])).

tff(c_18,plain,(
    ! [A_11,B_12] : k2_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1490,plain,(
    ! [B_112] : k2_xboole_0('#skF_2',k4_xboole_0('#skF_1',B_112)) = k2_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1449,c_18])).

tff(c_1531,plain,(
    ! [B_113] : k2_xboole_0('#skF_2',k4_xboole_0('#skF_1',B_113)) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1490])).

tff(c_1564,plain,(
    k2_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1531,c_18])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_603,plain,(
    ! [C_78,A_79,B_80] :
      ( k2_xboole_0(k9_relat_1(C_78,A_79),k9_relat_1(C_78,B_80)) = k9_relat_1(C_78,k2_xboole_0(A_79,B_80))
      | ~ v1_relat_1(C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_24,plain,(
    ! [A_17,B_18] : r1_tarski(A_17,k2_xboole_0(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1210,plain,(
    ! [C_105,A_106,B_107] :
      ( r1_tarski(k9_relat_1(C_105,A_106),k9_relat_1(C_105,k2_xboole_0(A_106,B_107)))
      | ~ v1_relat_1(C_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_603,c_24])).

tff(c_3531,plain,(
    ! [C_170,B_171,A_172] :
      ( r1_tarski(k9_relat_1(C_170,B_171),k9_relat_1(C_170,k2_xboole_0(A_172,B_171)))
      | ~ v1_relat_1(C_170) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1210])).

tff(c_4025,plain,(
    ! [C_188] :
      ( r1_tarski(k9_relat_1(C_188,'#skF_1'),k9_relat_1(C_188,'#skF_2'))
      | ~ v1_relat_1(C_188) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1564,c_3531])).

tff(c_30,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4036,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4025,c_30])).

tff(c_4044,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_4036])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 18:21:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.52/1.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.52/1.79  
% 4.52/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.52/1.79  %$ r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.52/1.79  
% 4.52/1.79  %Foreground sorts:
% 4.52/1.79  
% 4.52/1.79  
% 4.52/1.79  %Background operators:
% 4.52/1.79  
% 4.52/1.79  
% 4.52/1.79  %Foreground operators:
% 4.52/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.52/1.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.52/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.52/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.52/1.79  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.52/1.79  tff('#skF_2', type, '#skF_2': $i).
% 4.52/1.79  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.52/1.79  tff('#skF_3', type, '#skF_3': $i).
% 4.52/1.79  tff('#skF_1', type, '#skF_1': $i).
% 4.52/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.52/1.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.52/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.52/1.79  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.52/1.79  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.52/1.79  
% 4.52/1.81  tff(f_77, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 4.52/1.81  tff(f_36, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.52/1.81  tff(f_44, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.52/1.81  tff(f_42, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.52/1.81  tff(f_56, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.52/1.81  tff(f_54, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 4.52/1.81  tff(f_28, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.52/1.81  tff(f_66, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 4.52/1.81  tff(f_46, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.52/1.81  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.52/1.81  tff(f_70, axiom, (![A, B, C]: (v1_relat_1(C) => (k9_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t153_relat_1)).
% 4.52/1.81  tff(f_58, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.52/1.81  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.52/1.81  tff(c_12, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.52/1.81  tff(c_16, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.52/1.81  tff(c_388, plain, (![A_57, C_58, B_59]: (r1_tarski(A_57, C_58) | ~r1_tarski(B_59, C_58) | ~r1_tarski(A_57, B_59))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.52/1.81  tff(c_511, plain, (![A_69, A_70, B_71]: (r1_tarski(A_69, A_70) | ~r1_tarski(A_69, k4_xboole_0(A_70, B_71)))), inference(resolution, [status(thm)], [c_16, c_388])).
% 4.52/1.81  tff(c_532, plain, (![A_70, B_71, B_10]: (r1_tarski(k4_xboole_0(k4_xboole_0(A_70, B_71), B_10), A_70))), inference(resolution, [status(thm)], [c_16, c_511])).
% 4.52/1.81  tff(c_32, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.52/1.81  tff(c_409, plain, (![A_57]: (r1_tarski(A_57, '#skF_2') | ~r1_tarski(A_57, '#skF_1'))), inference(resolution, [status(thm)], [c_32, c_388])).
% 4.52/1.81  tff(c_22, plain, (![A_15, B_16]: (r1_xboole_0(k4_xboole_0(A_15, B_16), B_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.52/1.81  tff(c_253, plain, (![B_48, A_49]: (~r1_xboole_0(B_48, A_49) | ~r1_tarski(B_48, A_49) | v1_xboole_0(B_48))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.52/1.81  tff(c_794, plain, (![A_93, B_94]: (~r1_tarski(k4_xboole_0(A_93, B_94), B_94) | v1_xboole_0(k4_xboole_0(A_93, B_94)))), inference(resolution, [status(thm)], [c_22, c_253])).
% 4.52/1.81  tff(c_1351, plain, (![A_110]: (v1_xboole_0(k4_xboole_0(A_110, '#skF_2')) | ~r1_tarski(k4_xboole_0(A_110, '#skF_2'), '#skF_1'))), inference(resolution, [status(thm)], [c_409, c_794])).
% 4.52/1.81  tff(c_1427, plain, (![B_111]: (v1_xboole_0(k4_xboole_0(k4_xboole_0('#skF_1', B_111), '#skF_2')))), inference(resolution, [status(thm)], [c_532, c_1351])).
% 4.52/1.81  tff(c_4, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 4.52/1.81  tff(c_150, plain, (![B_36, A_37]: (~v1_xboole_0(B_36) | B_36=A_37 | ~v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.52/1.81  tff(c_153, plain, (![A_37]: (k1_xboole_0=A_37 | ~v1_xboole_0(A_37))), inference(resolution, [status(thm)], [c_4, c_150])).
% 4.52/1.81  tff(c_1449, plain, (![B_112]: (k4_xboole_0(k4_xboole_0('#skF_1', B_112), '#skF_2')=k1_xboole_0)), inference(resolution, [status(thm)], [c_1427, c_153])).
% 4.52/1.81  tff(c_18, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k4_xboole_0(B_12, A_11))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.52/1.81  tff(c_1490, plain, (![B_112]: (k2_xboole_0('#skF_2', k4_xboole_0('#skF_1', B_112))=k2_xboole_0('#skF_2', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1449, c_18])).
% 4.52/1.81  tff(c_1531, plain, (![B_113]: (k2_xboole_0('#skF_2', k4_xboole_0('#skF_1', B_113))='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1490])).
% 4.52/1.81  tff(c_1564, plain, (k2_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1531, c_18])).
% 4.52/1.81  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.52/1.81  tff(c_603, plain, (![C_78, A_79, B_80]: (k2_xboole_0(k9_relat_1(C_78, A_79), k9_relat_1(C_78, B_80))=k9_relat_1(C_78, k2_xboole_0(A_79, B_80)) | ~v1_relat_1(C_78))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.52/1.81  tff(c_24, plain, (![A_17, B_18]: (r1_tarski(A_17, k2_xboole_0(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.52/1.81  tff(c_1210, plain, (![C_105, A_106, B_107]: (r1_tarski(k9_relat_1(C_105, A_106), k9_relat_1(C_105, k2_xboole_0(A_106, B_107))) | ~v1_relat_1(C_105))), inference(superposition, [status(thm), theory('equality')], [c_603, c_24])).
% 4.52/1.81  tff(c_3531, plain, (![C_170, B_171, A_172]: (r1_tarski(k9_relat_1(C_170, B_171), k9_relat_1(C_170, k2_xboole_0(A_172, B_171))) | ~v1_relat_1(C_170))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1210])).
% 4.52/1.81  tff(c_4025, plain, (![C_188]: (r1_tarski(k9_relat_1(C_188, '#skF_1'), k9_relat_1(C_188, '#skF_2')) | ~v1_relat_1(C_188))), inference(superposition, [status(thm), theory('equality')], [c_1564, c_3531])).
% 4.52/1.81  tff(c_30, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.52/1.81  tff(c_4036, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4025, c_30])).
% 4.52/1.81  tff(c_4044, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_4036])).
% 4.52/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.52/1.81  
% 4.52/1.81  Inference rules
% 4.52/1.81  ----------------------
% 4.52/1.81  #Ref     : 0
% 4.52/1.81  #Sup     : 993
% 4.52/1.81  #Fact    : 0
% 4.52/1.81  #Define  : 0
% 4.52/1.81  #Split   : 2
% 4.52/1.81  #Chain   : 0
% 4.52/1.81  #Close   : 0
% 4.52/1.81  
% 4.52/1.81  Ordering : KBO
% 4.52/1.81  
% 4.52/1.81  Simplification rules
% 4.52/1.81  ----------------------
% 4.52/1.81  #Subsume      : 205
% 4.52/1.81  #Demod        : 819
% 4.52/1.81  #Tautology    : 519
% 4.52/1.81  #SimpNegUnit  : 0
% 4.52/1.81  #BackRed      : 6
% 4.52/1.81  
% 4.52/1.81  #Partial instantiations: 0
% 4.52/1.81  #Strategies tried      : 1
% 4.52/1.81  
% 4.52/1.81  Timing (in seconds)
% 4.52/1.81  ----------------------
% 4.52/1.81  Preprocessing        : 0.28
% 4.52/1.81  Parsing              : 0.16
% 4.52/1.81  CNF conversion       : 0.02
% 4.52/1.81  Main loop            : 0.76
% 4.52/1.81  Inferencing          : 0.23
% 4.52/1.81  Reduction            : 0.31
% 4.52/1.81  Demodulation         : 0.25
% 4.52/1.81  BG Simplification    : 0.02
% 4.52/1.81  Subsumption          : 0.15
% 4.52/1.81  Abstraction          : 0.03
% 4.52/1.81  MUC search           : 0.00
% 4.52/1.81  Cooper               : 0.00
% 4.52/1.81  Total                : 1.07
% 4.52/1.81  Index Insertion      : 0.00
% 4.52/1.81  Index Deletion       : 0.00
% 4.52/1.81  Index Matching       : 0.00
% 4.52/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
