%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:41 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   57 (  87 expanded)
%              Number of leaves         :   29 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :   59 ( 112 expanded)
%              Number of equality atoms :   26 (  52 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_55,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_61,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_34,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_28,plain,(
    k10_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_282,plain,(
    ! [B_53,A_54] :
      ( r1_xboole_0(k2_relat_1(B_53),A_54)
      | k10_relat_1(B_53,A_54) != k1_xboole_0
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_16,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_30,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_103,plain,(
    ! [A_31,B_32] :
      ( k4_xboole_0(A_31,B_32) = k1_xboole_0
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_107,plain,(
    k4_xboole_0('#skF_3',k2_relat_1('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_103])).

tff(c_197,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k4_xboole_0(A_44,B_45)) = k3_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_212,plain,(
    k3_xboole_0('#skF_3',k2_relat_1('#skF_4')) = k4_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_197])).

tff(c_218,plain,(
    k3_xboole_0('#skF_3',k2_relat_1('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_212])).

tff(c_20,plain,(
    ! [B_17,A_16] : k2_tarski(B_17,A_16) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_88,plain,(
    ! [A_29,B_30] : k1_setfam_1(k2_tarski(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_117,plain,(
    ! [A_35,B_36] : k1_setfam_1(k2_tarski(A_35,B_36)) = k3_xboole_0(B_36,A_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_88])).

tff(c_22,plain,(
    ! [A_18,B_19] : k1_setfam_1(k2_tarski(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_123,plain,(
    ! [B_36,A_35] : k3_xboole_0(B_36,A_35) = k3_xboole_0(A_35,B_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_22])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_173,plain,(
    ! [A_39,B_40,C_41] :
      ( ~ r1_xboole_0(A_39,B_40)
      | ~ r2_hidden(C_41,k3_xboole_0(A_39,B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_185,plain,(
    ! [A_42,B_43] :
      ( ~ r1_xboole_0(A_42,B_43)
      | v1_xboole_0(k3_xboole_0(A_42,B_43)) ) ),
    inference(resolution,[status(thm)],[c_4,c_173])).

tff(c_264,plain,(
    ! [A_51,B_52] :
      ( ~ r1_xboole_0(A_51,B_52)
      | v1_xboole_0(k3_xboole_0(B_52,A_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_185])).

tff(c_273,plain,
    ( ~ r1_xboole_0(k2_relat_1('#skF_4'),'#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_264])).

tff(c_281,plain,(
    ~ r1_xboole_0(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_273])).

tff(c_285,plain,
    ( k10_relat_1('#skF_4','#skF_3') != k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_282,c_281])).

tff(c_295,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_285])).

tff(c_296,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_273])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_300,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_296,c_6])).

tff(c_304,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_300])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:29:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.23  
% 2.11/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.24  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.11/1.24  
% 2.11/1.24  %Foreground sorts:
% 2.11/1.24  
% 2.11/1.24  
% 2.11/1.24  %Background operators:
% 2.11/1.24  
% 2.11/1.24  
% 2.11/1.24  %Foreground operators:
% 2.11/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.11/1.24  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.11/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.11/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.11/1.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.11/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.11/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.11/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.11/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.24  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.11/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.11/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.11/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.24  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.11/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.11/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.11/1.24  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.11/1.24  
% 2.11/1.25  tff(f_78, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_relat_1)).
% 2.11/1.25  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 2.11/1.25  tff(f_55, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.11/1.25  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.11/1.25  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.11/1.25  tff(f_59, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.11/1.25  tff(f_61, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.11/1.25  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.11/1.25  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.11/1.25  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.11/1.25  tff(c_32, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.11/1.25  tff(c_34, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.11/1.25  tff(c_28, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.11/1.25  tff(c_282, plain, (![B_53, A_54]: (r1_xboole_0(k2_relat_1(B_53), A_54) | k10_relat_1(B_53, A_54)!=k1_xboole_0 | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.11/1.25  tff(c_16, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.11/1.25  tff(c_30, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.11/1.25  tff(c_103, plain, (![A_31, B_32]: (k4_xboole_0(A_31, B_32)=k1_xboole_0 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.11/1.25  tff(c_107, plain, (k4_xboole_0('#skF_3', k2_relat_1('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_103])).
% 2.11/1.25  tff(c_197, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k4_xboole_0(A_44, B_45))=k3_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.11/1.25  tff(c_212, plain, (k3_xboole_0('#skF_3', k2_relat_1('#skF_4'))=k4_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_107, c_197])).
% 2.11/1.25  tff(c_218, plain, (k3_xboole_0('#skF_3', k2_relat_1('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_212])).
% 2.11/1.25  tff(c_20, plain, (![B_17, A_16]: (k2_tarski(B_17, A_16)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.11/1.25  tff(c_88, plain, (![A_29, B_30]: (k1_setfam_1(k2_tarski(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.11/1.25  tff(c_117, plain, (![A_35, B_36]: (k1_setfam_1(k2_tarski(A_35, B_36))=k3_xboole_0(B_36, A_35))), inference(superposition, [status(thm), theory('equality')], [c_20, c_88])).
% 2.11/1.25  tff(c_22, plain, (![A_18, B_19]: (k1_setfam_1(k2_tarski(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.11/1.25  tff(c_123, plain, (![B_36, A_35]: (k3_xboole_0(B_36, A_35)=k3_xboole_0(A_35, B_36))), inference(superposition, [status(thm), theory('equality')], [c_117, c_22])).
% 2.11/1.25  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.11/1.25  tff(c_173, plain, (![A_39, B_40, C_41]: (~r1_xboole_0(A_39, B_40) | ~r2_hidden(C_41, k3_xboole_0(A_39, B_40)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.11/1.25  tff(c_185, plain, (![A_42, B_43]: (~r1_xboole_0(A_42, B_43) | v1_xboole_0(k3_xboole_0(A_42, B_43)))), inference(resolution, [status(thm)], [c_4, c_173])).
% 2.11/1.25  tff(c_264, plain, (![A_51, B_52]: (~r1_xboole_0(A_51, B_52) | v1_xboole_0(k3_xboole_0(B_52, A_51)))), inference(superposition, [status(thm), theory('equality')], [c_123, c_185])).
% 2.11/1.25  tff(c_273, plain, (~r1_xboole_0(k2_relat_1('#skF_4'), '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_218, c_264])).
% 2.11/1.25  tff(c_281, plain, (~r1_xboole_0(k2_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_273])).
% 2.11/1.25  tff(c_285, plain, (k10_relat_1('#skF_4', '#skF_3')!=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_282, c_281])).
% 2.11/1.25  tff(c_295, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_285])).
% 2.11/1.25  tff(c_296, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_273])).
% 2.11/1.25  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.11/1.25  tff(c_300, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_296, c_6])).
% 2.11/1.25  tff(c_304, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_300])).
% 2.11/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.25  
% 2.11/1.25  Inference rules
% 2.11/1.25  ----------------------
% 2.11/1.25  #Ref     : 0
% 2.11/1.25  #Sup     : 69
% 2.11/1.25  #Fact    : 0
% 2.11/1.25  #Define  : 0
% 2.11/1.25  #Split   : 3
% 2.11/1.25  #Chain   : 0
% 2.11/1.25  #Close   : 0
% 2.11/1.25  
% 2.11/1.25  Ordering : KBO
% 2.11/1.25  
% 2.11/1.25  Simplification rules
% 2.11/1.25  ----------------------
% 2.11/1.25  #Subsume      : 6
% 2.11/1.25  #Demod        : 7
% 2.11/1.25  #Tautology    : 40
% 2.11/1.25  #SimpNegUnit  : 1
% 2.11/1.25  #BackRed      : 0
% 2.11/1.25  
% 2.11/1.25  #Partial instantiations: 0
% 2.11/1.25  #Strategies tried      : 1
% 2.11/1.25  
% 2.11/1.25  Timing (in seconds)
% 2.11/1.25  ----------------------
% 2.11/1.25  Preprocessing        : 0.30
% 2.11/1.25  Parsing              : 0.17
% 2.11/1.25  CNF conversion       : 0.02
% 2.11/1.25  Main loop            : 0.19
% 2.11/1.25  Inferencing          : 0.07
% 2.11/1.25  Reduction            : 0.06
% 2.11/1.25  Demodulation         : 0.05
% 2.11/1.25  BG Simplification    : 0.01
% 2.11/1.25  Subsumption          : 0.03
% 2.11/1.25  Abstraction          : 0.01
% 2.11/1.25  MUC search           : 0.00
% 2.11/1.25  Cooper               : 0.00
% 2.11/1.25  Total                : 0.52
% 2.11/1.25  Index Insertion      : 0.00
% 2.11/1.25  Index Deletion       : 0.00
% 2.11/1.25  Index Matching       : 0.00
% 2.11/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
