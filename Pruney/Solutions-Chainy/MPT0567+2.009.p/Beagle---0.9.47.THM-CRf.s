%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:16 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   49 (  60 expanded)
%              Number of leaves         :   26 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   56 (  74 expanded)
%              Number of equality atoms :   18 (  26 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_61,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

tff(f_59,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_14,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( r1_xboole_0(A_15,B_16)
      | k4_xboole_0(A_15,B_16) != A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_40,plain,(
    k10_relat_1('#skF_7',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_42,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_546,plain,(
    ! [A_113,B_114,D_115] :
      ( r2_hidden('#skF_6'(A_113,B_114,k10_relat_1(A_113,B_114),D_115),B_114)
      | ~ r2_hidden(D_115,k10_relat_1(A_113,B_114))
      | ~ v1_relat_1(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_12,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_124,plain,(
    ! [A_69,B_70,C_71] :
      ( ~ r1_xboole_0(A_69,B_70)
      | ~ r2_hidden(C_71,k3_xboole_0(A_69,B_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_130,plain,(
    ! [A_11,C_71] :
      ( ~ r1_xboole_0(A_11,k1_xboole_0)
      | ~ r2_hidden(C_71,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_124])).

tff(c_131,plain,(
    ! [C_71] : ~ r2_hidden(C_71,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_130])).

tff(c_587,plain,(
    ! [D_118,A_119] :
      ( ~ r2_hidden(D_118,k10_relat_1(A_119,k1_xboole_0))
      | ~ v1_relat_1(A_119) ) ),
    inference(resolution,[status(thm)],[c_546,c_131])).

tff(c_603,plain,(
    ! [A_120,A_121] :
      ( ~ v1_relat_1(A_120)
      | r1_xboole_0(A_121,k10_relat_1(A_120,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_4,c_587])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(A_15,B_16) = A_15
      | ~ r1_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_766,plain,(
    ! [A_133,A_134] :
      ( k4_xboole_0(A_133,k10_relat_1(A_134,k1_xboole_0)) = A_133
      | ~ v1_relat_1(A_134) ) ),
    inference(resolution,[status(thm)],[c_603,c_18])).

tff(c_65,plain,(
    ! [A_65,B_66] : k4_xboole_0(A_65,k4_xboole_0(A_65,B_66)) = k3_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_80,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k3_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_65])).

tff(c_83,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_80])).

tff(c_828,plain,(
    ! [A_138] :
      ( k10_relat_1(A_138,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_138) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_766,c_83])).

tff(c_831,plain,(
    k10_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_828])).

tff(c_835,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_831])).

tff(c_837,plain,(
    ! [A_139] : ~ r1_xboole_0(A_139,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_841,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) != A_15 ),
    inference(resolution,[status(thm)],[c_20,c_837])).

tff(c_845,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_841])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:04:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.58/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.49  
% 2.58/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.49  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1
% 2.58/1.49  
% 2.58/1.49  %Foreground sorts:
% 2.58/1.49  
% 2.58/1.49  
% 2.58/1.49  %Background operators:
% 2.58/1.49  
% 2.58/1.49  
% 2.58/1.49  %Foreground operators:
% 2.58/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.58/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.58/1.49  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.58/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.58/1.49  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.58/1.49  tff('#skF_7', type, '#skF_7': $i).
% 2.58/1.49  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.58/1.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.58/1.49  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 2.58/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.49  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.58/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.58/1.49  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.58/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.49  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.58/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.58/1.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.58/1.49  
% 2.77/1.50  tff(f_61, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.77/1.50  tff(f_67, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.77/1.50  tff(f_85, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_relat_1)).
% 2.77/1.50  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.77/1.50  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 2.77/1.50  tff(f_59, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.77/1.50  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.77/1.50  tff(f_63, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.77/1.50  tff(c_14, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.77/1.50  tff(c_20, plain, (![A_15, B_16]: (r1_xboole_0(A_15, B_16) | k4_xboole_0(A_15, B_16)!=A_15)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.77/1.50  tff(c_40, plain, (k10_relat_1('#skF_7', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.77/1.50  tff(c_42, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.77/1.50  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.77/1.51  tff(c_546, plain, (![A_113, B_114, D_115]: (r2_hidden('#skF_6'(A_113, B_114, k10_relat_1(A_113, B_114), D_115), B_114) | ~r2_hidden(D_115, k10_relat_1(A_113, B_114)) | ~v1_relat_1(A_113))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.77/1.51  tff(c_12, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.77/1.51  tff(c_124, plain, (![A_69, B_70, C_71]: (~r1_xboole_0(A_69, B_70) | ~r2_hidden(C_71, k3_xboole_0(A_69, B_70)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.77/1.51  tff(c_130, plain, (![A_11, C_71]: (~r1_xboole_0(A_11, k1_xboole_0) | ~r2_hidden(C_71, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_124])).
% 2.77/1.51  tff(c_131, plain, (![C_71]: (~r2_hidden(C_71, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_130])).
% 2.77/1.51  tff(c_587, plain, (![D_118, A_119]: (~r2_hidden(D_118, k10_relat_1(A_119, k1_xboole_0)) | ~v1_relat_1(A_119))), inference(resolution, [status(thm)], [c_546, c_131])).
% 2.77/1.51  tff(c_603, plain, (![A_120, A_121]: (~v1_relat_1(A_120) | r1_xboole_0(A_121, k10_relat_1(A_120, k1_xboole_0)))), inference(resolution, [status(thm)], [c_4, c_587])).
% 2.77/1.51  tff(c_18, plain, (![A_15, B_16]: (k4_xboole_0(A_15, B_16)=A_15 | ~r1_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.77/1.51  tff(c_766, plain, (![A_133, A_134]: (k4_xboole_0(A_133, k10_relat_1(A_134, k1_xboole_0))=A_133 | ~v1_relat_1(A_134))), inference(resolution, [status(thm)], [c_603, c_18])).
% 2.77/1.51  tff(c_65, plain, (![A_65, B_66]: (k4_xboole_0(A_65, k4_xboole_0(A_65, B_66))=k3_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.77/1.51  tff(c_80, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k3_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_65])).
% 2.77/1.51  tff(c_83, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_80])).
% 2.77/1.51  tff(c_828, plain, (![A_138]: (k10_relat_1(A_138, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_138))), inference(superposition, [status(thm), theory('equality')], [c_766, c_83])).
% 2.77/1.51  tff(c_831, plain, (k10_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_828])).
% 2.77/1.51  tff(c_835, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_831])).
% 2.77/1.51  tff(c_837, plain, (![A_139]: (~r1_xboole_0(A_139, k1_xboole_0))), inference(splitRight, [status(thm)], [c_130])).
% 2.77/1.51  tff(c_841, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)!=A_15)), inference(resolution, [status(thm)], [c_20, c_837])).
% 2.77/1.51  tff(c_845, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_841])).
% 2.77/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.51  
% 2.77/1.51  Inference rules
% 2.77/1.51  ----------------------
% 2.77/1.51  #Ref     : 0
% 2.77/1.51  #Sup     : 185
% 2.77/1.51  #Fact    : 0
% 2.77/1.51  #Define  : 0
% 2.77/1.51  #Split   : 1
% 2.77/1.51  #Chain   : 0
% 2.77/1.51  #Close   : 0
% 2.77/1.51  
% 2.77/1.51  Ordering : KBO
% 2.77/1.51  
% 2.77/1.51  Simplification rules
% 2.77/1.51  ----------------------
% 2.77/1.51  #Subsume      : 50
% 2.77/1.51  #Demod        : 30
% 2.77/1.51  #Tautology    : 82
% 2.77/1.51  #SimpNegUnit  : 5
% 2.77/1.51  #BackRed      : 0
% 2.77/1.51  
% 2.77/1.51  #Partial instantiations: 0
% 2.77/1.51  #Strategies tried      : 1
% 2.77/1.51  
% 2.77/1.51  Timing (in seconds)
% 2.77/1.51  ----------------------
% 2.77/1.51  Preprocessing        : 0.28
% 2.77/1.51  Parsing              : 0.15
% 2.77/1.51  CNF conversion       : 0.03
% 2.77/1.51  Main loop            : 0.37
% 2.77/1.51  Inferencing          : 0.15
% 2.77/1.51  Reduction            : 0.09
% 2.77/1.51  Demodulation         : 0.06
% 2.77/1.51  BG Simplification    : 0.02
% 2.77/1.51  Subsumption          : 0.07
% 2.77/1.51  Abstraction          : 0.02
% 2.77/1.51  MUC search           : 0.00
% 2.77/1.51  Cooper               : 0.00
% 2.77/1.51  Total                : 0.68
% 2.77/1.51  Index Insertion      : 0.00
% 2.77/1.51  Index Deletion       : 0.00
% 2.77/1.51  Index Matching       : 0.00
% 2.77/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
