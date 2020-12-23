%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:53 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   45 (  50 expanded)
%              Number of leaves         :   26 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   52 (  64 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_20,plain,(
    ! [A_35,B_36] :
      ( v1_relat_1(k7_relat_1(A_35,B_36))
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_24,plain,(
    ! [B_41,A_40] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_41,A_40)),A_40)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_30,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_86,plain,(
    ! [A_54,C_55,B_56] :
      ( r1_tarski(A_54,C_55)
      | ~ r1_tarski(B_56,C_55)
      | ~ r1_tarski(A_54,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_92,plain,(
    ! [A_54] :
      ( r1_tarski(A_54,'#skF_2')
      | ~ r1_tarski(A_54,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_86])).

tff(c_117,plain,(
    ! [B_63,A_64] :
      ( k7_relat_1(B_63,A_64) = B_63
      | ~ r1_tarski(k1_relat_1(B_63),A_64)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_127,plain,(
    ! [B_65] :
      ( k7_relat_1(B_65,'#skF_2') = B_65
      | ~ v1_relat_1(B_65)
      | ~ r1_tarski(k1_relat_1(B_65),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_92,c_117])).

tff(c_191,plain,(
    ! [B_78] :
      ( k7_relat_1(k7_relat_1(B_78,'#skF_1'),'#skF_2') = k7_relat_1(B_78,'#skF_1')
      | ~ v1_relat_1(k7_relat_1(B_78,'#skF_1'))
      | ~ v1_relat_1(B_78) ) ),
    inference(resolution,[status(thm)],[c_24,c_127])).

tff(c_201,plain,(
    ! [A_79] :
      ( k7_relat_1(k7_relat_1(A_79,'#skF_1'),'#skF_2') = k7_relat_1(A_79,'#skF_1')
      | ~ v1_relat_1(A_79) ) ),
    inference(resolution,[status(thm)],[c_20,c_191])).

tff(c_22,plain,(
    ! [C_39,A_37,B_38] :
      ( k7_relat_1(k7_relat_1(C_39,A_37),B_38) = k7_relat_1(C_39,k3_xboole_0(A_37,B_38))
      | ~ v1_relat_1(C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_236,plain,(
    ! [A_80] :
      ( k7_relat_1(A_80,k3_xboole_0('#skF_1','#skF_2')) = k7_relat_1(A_80,'#skF_1')
      | ~ v1_relat_1(A_80)
      | ~ v1_relat_1(A_80) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_22])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_142,plain,(
    ! [C_70,A_71,B_72] :
      ( k7_relat_1(k7_relat_1(C_70,A_71),B_72) = k7_relat_1(C_70,k3_xboole_0(A_71,B_72))
      | ~ v1_relat_1(C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_2'),'#skF_1') != k7_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_154,plain,
    ( k7_relat_1('#skF_3',k3_xboole_0('#skF_2','#skF_1')) != k7_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_28])).

tff(c_166,plain,(
    k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k7_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2,c_154])).

tff(c_248,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_166])).

tff(c_273,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_248])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:28:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.26  
% 2.14/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.26  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.14/1.26  
% 2.14/1.26  %Foreground sorts:
% 2.14/1.26  
% 2.14/1.26  
% 2.14/1.26  %Background operators:
% 2.14/1.26  
% 2.14/1.26  
% 2.14/1.26  %Foreground operators:
% 2.14/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.26  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.14/1.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.14/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.14/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.14/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.14/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.14/1.26  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.14/1.26  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.14/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.14/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.14/1.26  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.14/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.14/1.26  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.14/1.26  
% 2.14/1.27  tff(f_72, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_relat_1)).
% 2.14/1.27  tff(f_51, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.14/1.27  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.14/1.27  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.14/1.27  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.14/1.27  tff(f_55, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 2.14/1.27  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.14/1.27  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.14/1.27  tff(c_20, plain, (![A_35, B_36]: (v1_relat_1(k7_relat_1(A_35, B_36)) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.14/1.27  tff(c_24, plain, (![B_41, A_40]: (r1_tarski(k1_relat_1(k7_relat_1(B_41, A_40)), A_40) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.14/1.27  tff(c_30, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.14/1.27  tff(c_86, plain, (![A_54, C_55, B_56]: (r1_tarski(A_54, C_55) | ~r1_tarski(B_56, C_55) | ~r1_tarski(A_54, B_56))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.14/1.27  tff(c_92, plain, (![A_54]: (r1_tarski(A_54, '#skF_2') | ~r1_tarski(A_54, '#skF_1'))), inference(resolution, [status(thm)], [c_30, c_86])).
% 2.14/1.27  tff(c_117, plain, (![B_63, A_64]: (k7_relat_1(B_63, A_64)=B_63 | ~r1_tarski(k1_relat_1(B_63), A_64) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.14/1.27  tff(c_127, plain, (![B_65]: (k7_relat_1(B_65, '#skF_2')=B_65 | ~v1_relat_1(B_65) | ~r1_tarski(k1_relat_1(B_65), '#skF_1'))), inference(resolution, [status(thm)], [c_92, c_117])).
% 2.14/1.27  tff(c_191, plain, (![B_78]: (k7_relat_1(k7_relat_1(B_78, '#skF_1'), '#skF_2')=k7_relat_1(B_78, '#skF_1') | ~v1_relat_1(k7_relat_1(B_78, '#skF_1')) | ~v1_relat_1(B_78))), inference(resolution, [status(thm)], [c_24, c_127])).
% 2.14/1.27  tff(c_201, plain, (![A_79]: (k7_relat_1(k7_relat_1(A_79, '#skF_1'), '#skF_2')=k7_relat_1(A_79, '#skF_1') | ~v1_relat_1(A_79))), inference(resolution, [status(thm)], [c_20, c_191])).
% 2.14/1.27  tff(c_22, plain, (![C_39, A_37, B_38]: (k7_relat_1(k7_relat_1(C_39, A_37), B_38)=k7_relat_1(C_39, k3_xboole_0(A_37, B_38)) | ~v1_relat_1(C_39))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.14/1.27  tff(c_236, plain, (![A_80]: (k7_relat_1(A_80, k3_xboole_0('#skF_1', '#skF_2'))=k7_relat_1(A_80, '#skF_1') | ~v1_relat_1(A_80) | ~v1_relat_1(A_80))), inference(superposition, [status(thm), theory('equality')], [c_201, c_22])).
% 2.14/1.27  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.14/1.27  tff(c_142, plain, (![C_70, A_71, B_72]: (k7_relat_1(k7_relat_1(C_70, A_71), B_72)=k7_relat_1(C_70, k3_xboole_0(A_71, B_72)) | ~v1_relat_1(C_70))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.14/1.27  tff(c_28, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_2'), '#skF_1')!=k7_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.14/1.27  tff(c_154, plain, (k7_relat_1('#skF_3', k3_xboole_0('#skF_2', '#skF_1'))!=k7_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_142, c_28])).
% 2.14/1.27  tff(c_166, plain, (k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k7_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2, c_154])).
% 2.14/1.27  tff(c_248, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_236, c_166])).
% 2.14/1.27  tff(c_273, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_248])).
% 2.14/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.27  
% 2.14/1.27  Inference rules
% 2.14/1.27  ----------------------
% 2.14/1.27  #Ref     : 0
% 2.14/1.27  #Sup     : 60
% 2.14/1.27  #Fact    : 0
% 2.14/1.27  #Define  : 0
% 2.14/1.27  #Split   : 0
% 2.14/1.27  #Chain   : 0
% 2.14/1.27  #Close   : 0
% 2.14/1.27  
% 2.14/1.27  Ordering : KBO
% 2.14/1.27  
% 2.14/1.27  Simplification rules
% 2.14/1.27  ----------------------
% 2.14/1.27  #Subsume      : 5
% 2.14/1.27  #Demod        : 4
% 2.14/1.27  #Tautology    : 22
% 2.14/1.27  #SimpNegUnit  : 0
% 2.14/1.27  #BackRed      : 0
% 2.14/1.27  
% 2.14/1.27  #Partial instantiations: 0
% 2.14/1.27  #Strategies tried      : 1
% 2.14/1.27  
% 2.14/1.27  Timing (in seconds)
% 2.14/1.27  ----------------------
% 2.14/1.27  Preprocessing        : 0.32
% 2.14/1.27  Parsing              : 0.17
% 2.14/1.27  CNF conversion       : 0.02
% 2.14/1.27  Main loop            : 0.20
% 2.14/1.27  Inferencing          : 0.08
% 2.14/1.27  Reduction            : 0.06
% 2.14/1.27  Demodulation         : 0.04
% 2.14/1.27  BG Simplification    : 0.02
% 2.14/1.27  Subsumption          : 0.04
% 2.14/1.27  Abstraction          : 0.01
% 2.14/1.27  MUC search           : 0.00
% 2.14/1.27  Cooper               : 0.00
% 2.14/1.27  Total                : 0.54
% 2.14/1.27  Index Insertion      : 0.00
% 2.14/1.27  Index Deletion       : 0.00
% 2.14/1.27  Index Matching       : 0.00
% 2.14/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
