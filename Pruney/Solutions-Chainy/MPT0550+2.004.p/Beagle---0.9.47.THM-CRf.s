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
% DateTime   : Thu Dec  3 10:00:52 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 126 expanded)
%              Number of leaves         :   27 (  54 expanded)
%              Depth                    :    8
%              Number of atoms          :   63 ( 176 expanded)
%              Number of equality atoms :   26 (  85 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k1_relat_1(B))
            & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_53,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_59,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_30,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_24,plain,(
    k9_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_338,plain,(
    ! [B_54,A_55] :
      ( r1_xboole_0(k1_relat_1(B_54),A_55)
      | k9_relat_1(B_54,A_55) != k1_xboole_0
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_12,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_26,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_94,plain,(
    ! [A_27,B_28] :
      ( k4_xboole_0(A_27,B_28) = k1_xboole_0
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_102,plain,(
    k4_xboole_0('#skF_3',k1_relat_1('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_94])).

tff(c_164,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k4_xboole_0(A_33,B_34)) = k3_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_179,plain,(
    k3_xboole_0('#skF_3',k1_relat_1('#skF_4')) = k4_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_164])).

tff(c_185,plain,(
    k3_xboole_0('#skF_3',k1_relat_1('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_179])).

tff(c_16,plain,(
    ! [B_14,A_13] : k2_tarski(B_14,A_13) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_78,plain,(
    ! [A_23,B_24] : k1_setfam_1(k2_tarski(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_107,plain,(
    ! [A_29,B_30] : k1_setfam_1(k2_tarski(A_29,B_30)) = k3_xboole_0(B_30,A_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_78])).

tff(c_18,plain,(
    ! [A_15,B_16] : k1_setfam_1(k2_tarski(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_113,plain,(
    ! [B_30,A_29] : k3_xboole_0(B_30,A_29) = k3_xboole_0(A_29,B_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_18])).

tff(c_214,plain,(
    ! [A_36,B_37,C_38] :
      ( ~ r1_xboole_0(A_36,B_37)
      | ~ r2_hidden(C_38,k3_xboole_0(A_36,B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_277,plain,(
    ! [B_44,A_45,C_46] :
      ( ~ r1_xboole_0(B_44,A_45)
      | ~ r2_hidden(C_46,k3_xboole_0(A_45,B_44)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_214])).

tff(c_286,plain,(
    ! [C_46] :
      ( ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_46,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_277])).

tff(c_300,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_286])).

tff(c_347,plain,
    ( k9_relat_1('#skF_4','#skF_3') != k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_338,c_300])).

tff(c_358,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_24,c_347])).

tff(c_359,plain,(
    ! [C_46] : ~ r2_hidden(C_46,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_286])).

tff(c_220,plain,(
    ! [C_38] :
      ( ~ r1_xboole_0('#skF_3',k1_relat_1('#skF_4'))
      | ~ r2_hidden(C_38,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_214])).

tff(c_235,plain,(
    ~ r1_xboole_0('#skF_3',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_220])).

tff(c_236,plain,(
    ! [A_41,B_42] :
      ( r2_hidden('#skF_1'(A_41,B_42),k3_xboole_0(A_41,B_42))
      | r1_xboole_0(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_245,plain,
    ( r2_hidden('#skF_1'('#skF_3',k1_relat_1('#skF_4')),'#skF_3')
    | r1_xboole_0('#skF_3',k1_relat_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_236])).

tff(c_276,plain,(
    r2_hidden('#skF_1'('#skF_3',k1_relat_1('#skF_4')),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_235,c_245])).

tff(c_362,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_359,c_276])).

tff(c_365,plain,(
    ! [C_56] : ~ r2_hidden(C_56,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_220])).

tff(c_369,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6,c_365])).

tff(c_373,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_369])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:33:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.24  
% 2.10/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.25  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.10/1.25  
% 2.10/1.25  %Foreground sorts:
% 2.10/1.25  
% 2.10/1.25  
% 2.10/1.25  %Background operators:
% 2.10/1.25  
% 2.10/1.25  
% 2.10/1.25  %Foreground operators:
% 2.10/1.25  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.10/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.10/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.10/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.10/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.10/1.25  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.10/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.10/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.10/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.10/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.10/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.10/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.10/1.25  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.10/1.25  
% 2.10/1.26  tff(f_76, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_relat_1)).
% 2.10/1.26  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.10/1.26  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 2.10/1.26  tff(f_53, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.10/1.26  tff(f_51, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.10/1.26  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.10/1.26  tff(f_57, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.10/1.26  tff(f_59, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.10/1.26  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.10/1.26  tff(c_28, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.10/1.26  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.10/1.26  tff(c_30, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.10/1.26  tff(c_24, plain, (k9_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.10/1.26  tff(c_338, plain, (![B_54, A_55]: (r1_xboole_0(k1_relat_1(B_54), A_55) | k9_relat_1(B_54, A_55)!=k1_xboole_0 | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.10/1.26  tff(c_12, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.10/1.26  tff(c_26, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.10/1.26  tff(c_94, plain, (![A_27, B_28]: (k4_xboole_0(A_27, B_28)=k1_xboole_0 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.10/1.26  tff(c_102, plain, (k4_xboole_0('#skF_3', k1_relat_1('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_94])).
% 2.10/1.26  tff(c_164, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k4_xboole_0(A_33, B_34))=k3_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.10/1.26  tff(c_179, plain, (k3_xboole_0('#skF_3', k1_relat_1('#skF_4'))=k4_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_102, c_164])).
% 2.10/1.26  tff(c_185, plain, (k3_xboole_0('#skF_3', k1_relat_1('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_179])).
% 2.10/1.26  tff(c_16, plain, (![B_14, A_13]: (k2_tarski(B_14, A_13)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.10/1.26  tff(c_78, plain, (![A_23, B_24]: (k1_setfam_1(k2_tarski(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.10/1.26  tff(c_107, plain, (![A_29, B_30]: (k1_setfam_1(k2_tarski(A_29, B_30))=k3_xboole_0(B_30, A_29))), inference(superposition, [status(thm), theory('equality')], [c_16, c_78])).
% 2.10/1.26  tff(c_18, plain, (![A_15, B_16]: (k1_setfam_1(k2_tarski(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.10/1.26  tff(c_113, plain, (![B_30, A_29]: (k3_xboole_0(B_30, A_29)=k3_xboole_0(A_29, B_30))), inference(superposition, [status(thm), theory('equality')], [c_107, c_18])).
% 2.10/1.26  tff(c_214, plain, (![A_36, B_37, C_38]: (~r1_xboole_0(A_36, B_37) | ~r2_hidden(C_38, k3_xboole_0(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.10/1.26  tff(c_277, plain, (![B_44, A_45, C_46]: (~r1_xboole_0(B_44, A_45) | ~r2_hidden(C_46, k3_xboole_0(A_45, B_44)))), inference(superposition, [status(thm), theory('equality')], [c_113, c_214])).
% 2.10/1.26  tff(c_286, plain, (![C_46]: (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3') | ~r2_hidden(C_46, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_185, c_277])).
% 2.10/1.26  tff(c_300, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_286])).
% 2.10/1.26  tff(c_347, plain, (k9_relat_1('#skF_4', '#skF_3')!=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_338, c_300])).
% 2.10/1.26  tff(c_358, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_24, c_347])).
% 2.10/1.26  tff(c_359, plain, (![C_46]: (~r2_hidden(C_46, '#skF_3'))), inference(splitRight, [status(thm)], [c_286])).
% 2.10/1.26  tff(c_220, plain, (![C_38]: (~r1_xboole_0('#skF_3', k1_relat_1('#skF_4')) | ~r2_hidden(C_38, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_185, c_214])).
% 2.10/1.26  tff(c_235, plain, (~r1_xboole_0('#skF_3', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_220])).
% 2.10/1.26  tff(c_236, plain, (![A_41, B_42]: (r2_hidden('#skF_1'(A_41, B_42), k3_xboole_0(A_41, B_42)) | r1_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.10/1.26  tff(c_245, plain, (r2_hidden('#skF_1'('#skF_3', k1_relat_1('#skF_4')), '#skF_3') | r1_xboole_0('#skF_3', k1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_185, c_236])).
% 2.10/1.26  tff(c_276, plain, (r2_hidden('#skF_1'('#skF_3', k1_relat_1('#skF_4')), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_235, c_245])).
% 2.10/1.26  tff(c_362, plain, $false, inference(negUnitSimplification, [status(thm)], [c_359, c_276])).
% 2.10/1.26  tff(c_365, plain, (![C_56]: (~r2_hidden(C_56, '#skF_3'))), inference(splitRight, [status(thm)], [c_220])).
% 2.10/1.26  tff(c_369, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_6, c_365])).
% 2.10/1.26  tff(c_373, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_369])).
% 2.10/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.26  
% 2.10/1.26  Inference rules
% 2.10/1.26  ----------------------
% 2.10/1.26  #Ref     : 0
% 2.10/1.26  #Sup     : 85
% 2.10/1.26  #Fact    : 0
% 2.10/1.26  #Define  : 0
% 2.10/1.26  #Split   : 3
% 2.10/1.26  #Chain   : 0
% 2.10/1.26  #Close   : 0
% 2.10/1.26  
% 2.10/1.26  Ordering : KBO
% 2.10/1.26  
% 2.10/1.26  Simplification rules
% 2.10/1.26  ----------------------
% 2.10/1.26  #Subsume      : 9
% 2.10/1.26  #Demod        : 18
% 2.10/1.26  #Tautology    : 48
% 2.10/1.26  #SimpNegUnit  : 4
% 2.10/1.26  #BackRed      : 1
% 2.10/1.26  
% 2.10/1.26  #Partial instantiations: 0
% 2.10/1.26  #Strategies tried      : 1
% 2.10/1.26  
% 2.10/1.26  Timing (in seconds)
% 2.10/1.26  ----------------------
% 2.10/1.26  Preprocessing        : 0.28
% 2.10/1.26  Parsing              : 0.15
% 2.10/1.26  CNF conversion       : 0.02
% 2.10/1.26  Main loop            : 0.21
% 2.10/1.26  Inferencing          : 0.08
% 2.10/1.26  Reduction            : 0.07
% 2.10/1.26  Demodulation         : 0.05
% 2.10/1.26  BG Simplification    : 0.01
% 2.10/1.26  Subsumption          : 0.03
% 2.10/1.26  Abstraction          : 0.01
% 2.10/1.26  MUC search           : 0.00
% 2.10/1.26  Cooper               : 0.00
% 2.10/1.26  Total                : 0.53
% 2.10/1.26  Index Insertion      : 0.00
% 2.10/1.26  Index Deletion       : 0.00
% 2.10/1.26  Index Matching       : 0.00
% 2.10/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
