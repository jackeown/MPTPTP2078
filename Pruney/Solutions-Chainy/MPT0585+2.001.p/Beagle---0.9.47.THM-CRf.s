%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:00 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   42 (  50 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :   53 (  70 expanded)
%              Number of equality atoms :   24 (  31 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => k7_relat_1(A,k1_relat_1(B)) = k7_relat_1(A,k1_relat_1(k7_relat_1(B,k1_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_37,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    ! [B_13,A_12] :
      ( k3_xboole_0(k1_relat_1(B_13),A_12) = k1_relat_1(k7_relat_1(B_13,A_12))
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_148,plain,(
    ! [B_30,A_31] :
      ( k7_relat_1(B_30,A_31) = B_30
      | ~ r1_tarski(k1_relat_1(B_30),A_31)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_153,plain,(
    ! [B_30] :
      ( k7_relat_1(B_30,k1_relat_1(B_30)) = B_30
      | ~ v1_relat_1(B_30) ) ),
    inference(resolution,[status(thm)],[c_6,c_148])).

tff(c_186,plain,(
    ! [C_35,A_36,B_37] :
      ( k7_relat_1(k7_relat_1(C_35,A_36),B_37) = k7_relat_1(C_35,k3_xboole_0(A_36,B_37))
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_243,plain,(
    ! [B_40,B_41] :
      ( k7_relat_1(B_40,k3_xboole_0(k1_relat_1(B_40),B_41)) = k7_relat_1(B_40,B_41)
      | ~ v1_relat_1(B_40)
      | ~ v1_relat_1(B_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_186])).

tff(c_515,plain,(
    ! [B_50,A_51] :
      ( k7_relat_1(B_50,k1_relat_1(k7_relat_1(B_50,A_51))) = k7_relat_1(B_50,A_51)
      | ~ v1_relat_1(B_50)
      | ~ v1_relat_1(B_50)
      | ~ v1_relat_1(B_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_243])).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_163,plain,(
    ! [B_33,A_34] :
      ( k3_xboole_0(k1_relat_1(B_33),A_34) = k1_relat_1(k7_relat_1(B_33,A_34))
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_69,plain,(
    ! [A_22,B_23] : k1_setfam_1(k2_tarski(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_84,plain,(
    ! [B_24,A_25] : k1_setfam_1(k2_tarski(B_24,A_25)) = k3_xboole_0(A_25,B_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_69])).

tff(c_12,plain,(
    ! [A_7,B_8] : k1_setfam_1(k2_tarski(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_90,plain,(
    ! [B_24,A_25] : k3_xboole_0(B_24,A_25) = k3_xboole_0(A_25,B_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_12])).

tff(c_212,plain,(
    ! [A_38,B_39] :
      ( k3_xboole_0(A_38,k1_relat_1(B_39)) = k1_relat_1(k7_relat_1(B_39,A_38))
      | ~ v1_relat_1(B_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_90])).

tff(c_323,plain,(
    ! [B_45,B_44] :
      ( k1_relat_1(k7_relat_1(B_45,k1_relat_1(B_44))) = k1_relat_1(k7_relat_1(B_44,k1_relat_1(B_45)))
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(B_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_212])).

tff(c_20,plain,(
    k7_relat_1('#skF_1',k1_relat_1(k7_relat_1('#skF_2',k1_relat_1('#skF_1')))) != k7_relat_1('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_386,plain,
    ( k7_relat_1('#skF_1',k1_relat_1(k7_relat_1('#skF_1',k1_relat_1('#skF_2')))) != k7_relat_1('#skF_1',k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_20])).

tff(c_427,plain,(
    k7_relat_1('#skF_1',k1_relat_1(k7_relat_1('#skF_1',k1_relat_1('#skF_2')))) != k7_relat_1('#skF_1',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_386])).

tff(c_528,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_515,c_427])).

tff(c_576,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_528])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:43:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.31  
% 2.27/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.31  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.27/1.31  
% 2.27/1.31  %Foreground sorts:
% 2.27/1.31  
% 2.27/1.31  
% 2.27/1.31  %Background operators:
% 2.27/1.31  
% 2.27/1.31  
% 2.27/1.31  %Foreground operators:
% 2.27/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.31  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.27/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.27/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.27/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.27/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.27/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.27/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.27/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.27/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.27/1.31  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.27/1.31  
% 2.27/1.32  tff(f_59, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k7_relat_1(A, k1_relat_1(B)) = k7_relat_1(A, k1_relat_1(k7_relat_1(B, k1_relat_1(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t189_relat_1)).
% 2.27/1.32  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.27/1.32  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.27/1.32  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.27/1.32  tff(f_41, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 2.27/1.32  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.27/1.32  tff(f_37, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.27/1.32  tff(c_24, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.27/1.32  tff(c_16, plain, (![B_13, A_12]: (k3_xboole_0(k1_relat_1(B_13), A_12)=k1_relat_1(k7_relat_1(B_13, A_12)) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.27/1.32  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.27/1.32  tff(c_148, plain, (![B_30, A_31]: (k7_relat_1(B_30, A_31)=B_30 | ~r1_tarski(k1_relat_1(B_30), A_31) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.27/1.32  tff(c_153, plain, (![B_30]: (k7_relat_1(B_30, k1_relat_1(B_30))=B_30 | ~v1_relat_1(B_30))), inference(resolution, [status(thm)], [c_6, c_148])).
% 2.27/1.32  tff(c_186, plain, (![C_35, A_36, B_37]: (k7_relat_1(k7_relat_1(C_35, A_36), B_37)=k7_relat_1(C_35, k3_xboole_0(A_36, B_37)) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.27/1.32  tff(c_243, plain, (![B_40, B_41]: (k7_relat_1(B_40, k3_xboole_0(k1_relat_1(B_40), B_41))=k7_relat_1(B_40, B_41) | ~v1_relat_1(B_40) | ~v1_relat_1(B_40))), inference(superposition, [status(thm), theory('equality')], [c_153, c_186])).
% 2.27/1.32  tff(c_515, plain, (![B_50, A_51]: (k7_relat_1(B_50, k1_relat_1(k7_relat_1(B_50, A_51)))=k7_relat_1(B_50, A_51) | ~v1_relat_1(B_50) | ~v1_relat_1(B_50) | ~v1_relat_1(B_50))), inference(superposition, [status(thm), theory('equality')], [c_16, c_243])).
% 2.27/1.32  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.27/1.32  tff(c_163, plain, (![B_33, A_34]: (k3_xboole_0(k1_relat_1(B_33), A_34)=k1_relat_1(k7_relat_1(B_33, A_34)) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.27/1.32  tff(c_8, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.27/1.32  tff(c_69, plain, (![A_22, B_23]: (k1_setfam_1(k2_tarski(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.27/1.32  tff(c_84, plain, (![B_24, A_25]: (k1_setfam_1(k2_tarski(B_24, A_25))=k3_xboole_0(A_25, B_24))), inference(superposition, [status(thm), theory('equality')], [c_8, c_69])).
% 2.27/1.32  tff(c_12, plain, (![A_7, B_8]: (k1_setfam_1(k2_tarski(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.27/1.32  tff(c_90, plain, (![B_24, A_25]: (k3_xboole_0(B_24, A_25)=k3_xboole_0(A_25, B_24))), inference(superposition, [status(thm), theory('equality')], [c_84, c_12])).
% 2.27/1.32  tff(c_212, plain, (![A_38, B_39]: (k3_xboole_0(A_38, k1_relat_1(B_39))=k1_relat_1(k7_relat_1(B_39, A_38)) | ~v1_relat_1(B_39))), inference(superposition, [status(thm), theory('equality')], [c_163, c_90])).
% 2.27/1.32  tff(c_323, plain, (![B_45, B_44]: (k1_relat_1(k7_relat_1(B_45, k1_relat_1(B_44)))=k1_relat_1(k7_relat_1(B_44, k1_relat_1(B_45))) | ~v1_relat_1(B_44) | ~v1_relat_1(B_45))), inference(superposition, [status(thm), theory('equality')], [c_16, c_212])).
% 2.27/1.32  tff(c_20, plain, (k7_relat_1('#skF_1', k1_relat_1(k7_relat_1('#skF_2', k1_relat_1('#skF_1'))))!=k7_relat_1('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.27/1.32  tff(c_386, plain, (k7_relat_1('#skF_1', k1_relat_1(k7_relat_1('#skF_1', k1_relat_1('#skF_2'))))!=k7_relat_1('#skF_1', k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_323, c_20])).
% 2.27/1.32  tff(c_427, plain, (k7_relat_1('#skF_1', k1_relat_1(k7_relat_1('#skF_1', k1_relat_1('#skF_2'))))!=k7_relat_1('#skF_1', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_386])).
% 2.27/1.32  tff(c_528, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_515, c_427])).
% 2.27/1.32  tff(c_576, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_528])).
% 2.27/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.32  
% 2.27/1.32  Inference rules
% 2.27/1.32  ----------------------
% 2.27/1.32  #Ref     : 0
% 2.27/1.32  #Sup     : 144
% 2.27/1.32  #Fact    : 0
% 2.27/1.32  #Define  : 0
% 2.27/1.32  #Split   : 0
% 2.27/1.32  #Chain   : 0
% 2.27/1.32  #Close   : 0
% 2.27/1.32  
% 2.27/1.32  Ordering : KBO
% 2.27/1.32  
% 2.27/1.32  Simplification rules
% 2.27/1.32  ----------------------
% 2.27/1.32  #Subsume      : 13
% 2.27/1.32  #Demod        : 10
% 2.27/1.32  #Tautology    : 53
% 2.27/1.32  #SimpNegUnit  : 0
% 2.27/1.32  #BackRed      : 0
% 2.27/1.32  
% 2.27/1.32  #Partial instantiations: 0
% 2.27/1.32  #Strategies tried      : 1
% 2.27/1.32  
% 2.27/1.32  Timing (in seconds)
% 2.27/1.32  ----------------------
% 2.27/1.32  Preprocessing        : 0.28
% 2.27/1.32  Parsing              : 0.15
% 2.27/1.32  CNF conversion       : 0.02
% 2.27/1.32  Main loop            : 0.27
% 2.27/1.32  Inferencing          : 0.11
% 2.27/1.32  Reduction            : 0.08
% 2.27/1.32  Demodulation         : 0.06
% 2.27/1.32  BG Simplification    : 0.02
% 2.27/1.32  Subsumption          : 0.05
% 2.27/1.32  Abstraction          : 0.02
% 2.27/1.32  MUC search           : 0.00
% 2.27/1.32  Cooper               : 0.00
% 2.27/1.32  Total                : 0.57
% 2.27/1.32  Index Insertion      : 0.00
% 2.27/1.32  Index Deletion       : 0.00
% 2.27/1.32  Index Matching       : 0.00
% 2.27/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
