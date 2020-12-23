%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:30 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   50 (  59 expanded)
%              Number of leaves         :   28 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   54 (  70 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_49,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_74,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_59,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_73,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_77,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_63,plain,(
    ! [A_29,B_30,C_31] :
      ( ~ r1_xboole_0(A_29,B_30)
      | ~ r2_hidden(C_31,k3_xboole_0(A_29,B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_70,plain,(
    ! [A_10,C_31] :
      ( ~ r1_xboole_0(A_10,k1_xboole_0)
      | ~ r2_hidden(C_31,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_63])).

tff(c_73,plain,(
    ! [C_31] : ~ r2_hidden(C_31,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_70])).

tff(c_30,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_41,plain,(
    ! [A_21] : v1_relat_1(k6_relat_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_43,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_41])).

tff(c_26,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_209,plain,(
    ! [A_50,B_51,C_52] :
      ( r2_hidden('#skF_3'(A_50,B_51,C_52),k2_relat_1(C_52))
      | ~ r2_hidden(A_50,k10_relat_1(C_52,B_51))
      | ~ v1_relat_1(C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_215,plain,(
    ! [A_50,B_51] :
      ( r2_hidden('#skF_3'(A_50,B_51,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_50,k10_relat_1(k1_xboole_0,B_51))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_209])).

tff(c_218,plain,(
    ! [A_50,B_51] :
      ( r2_hidden('#skF_3'(A_50,B_51,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_50,k10_relat_1(k1_xboole_0,B_51)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_215])).

tff(c_220,plain,(
    ! [A_53,B_54] : ~ r2_hidden(A_53,k10_relat_1(k1_xboole_0,B_54)) ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_218])).

tff(c_233,plain,(
    ! [B_55] : v1_xboole_0(k10_relat_1(k1_xboole_0,B_55)) ),
    inference(resolution,[status(thm)],[c_4,c_220])).

tff(c_74,plain,(
    ! [C_32] : ~ r2_hidden(C_32,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_70])).

tff(c_79,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_74])).

tff(c_14,plain,(
    ! [B_13,A_12] :
      ( ~ v1_xboole_0(B_13)
      | B_13 = A_12
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_82,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ v1_xboole_0(A_12) ) ),
    inference(resolution,[status(thm)],[c_79,c_14])).

tff(c_241,plain,(
    ! [B_55] : k10_relat_1(k1_xboole_0,B_55) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_233,c_82])).

tff(c_32,plain,(
    k10_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_250,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:26:10 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.24  
% 1.87/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.24  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2
% 2.09/1.24  
% 2.09/1.24  %Foreground sorts:
% 2.09/1.24  
% 2.09/1.24  
% 2.09/1.24  %Background operators:
% 2.09/1.24  
% 2.09/1.24  
% 2.09/1.24  %Foreground operators:
% 2.09/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.24  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.09/1.24  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.09/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.09/1.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.09/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.09/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.24  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.09/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.09/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.09/1.24  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.09/1.24  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.09/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.24  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.09/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.09/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.09/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.09/1.24  
% 2.09/1.25  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.09/1.25  tff(f_49, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.09/1.25  tff(f_47, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.09/1.25  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.09/1.25  tff(f_74, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 2.09/1.25  tff(f_59, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.09/1.25  tff(f_73, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.09/1.25  tff(f_70, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 2.09/1.25  tff(f_57, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 2.09/1.25  tff(f_77, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 2.09/1.25  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.09/1.25  tff(c_12, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.09/1.25  tff(c_10, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.09/1.25  tff(c_63, plain, (![A_29, B_30, C_31]: (~r1_xboole_0(A_29, B_30) | ~r2_hidden(C_31, k3_xboole_0(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.09/1.25  tff(c_70, plain, (![A_10, C_31]: (~r1_xboole_0(A_10, k1_xboole_0) | ~r2_hidden(C_31, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_63])).
% 2.09/1.25  tff(c_73, plain, (![C_31]: (~r2_hidden(C_31, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_70])).
% 2.09/1.25  tff(c_30, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.09/1.25  tff(c_41, plain, (![A_21]: (v1_relat_1(k6_relat_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.09/1.25  tff(c_43, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30, c_41])).
% 2.09/1.25  tff(c_26, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.09/1.25  tff(c_209, plain, (![A_50, B_51, C_52]: (r2_hidden('#skF_3'(A_50, B_51, C_52), k2_relat_1(C_52)) | ~r2_hidden(A_50, k10_relat_1(C_52, B_51)) | ~v1_relat_1(C_52))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.09/1.25  tff(c_215, plain, (![A_50, B_51]: (r2_hidden('#skF_3'(A_50, B_51, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_50, k10_relat_1(k1_xboole_0, B_51)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_209])).
% 2.09/1.25  tff(c_218, plain, (![A_50, B_51]: (r2_hidden('#skF_3'(A_50, B_51, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_50, k10_relat_1(k1_xboole_0, B_51)))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_215])).
% 2.09/1.25  tff(c_220, plain, (![A_53, B_54]: (~r2_hidden(A_53, k10_relat_1(k1_xboole_0, B_54)))), inference(negUnitSimplification, [status(thm)], [c_73, c_218])).
% 2.09/1.25  tff(c_233, plain, (![B_55]: (v1_xboole_0(k10_relat_1(k1_xboole_0, B_55)))), inference(resolution, [status(thm)], [c_4, c_220])).
% 2.09/1.25  tff(c_74, plain, (![C_32]: (~r2_hidden(C_32, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_70])).
% 2.09/1.25  tff(c_79, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_74])).
% 2.09/1.25  tff(c_14, plain, (![B_13, A_12]: (~v1_xboole_0(B_13) | B_13=A_12 | ~v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.09/1.25  tff(c_82, plain, (![A_12]: (k1_xboole_0=A_12 | ~v1_xboole_0(A_12))), inference(resolution, [status(thm)], [c_79, c_14])).
% 2.09/1.25  tff(c_241, plain, (![B_55]: (k10_relat_1(k1_xboole_0, B_55)=k1_xboole_0)), inference(resolution, [status(thm)], [c_233, c_82])).
% 2.09/1.25  tff(c_32, plain, (k10_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.09/1.25  tff(c_250, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_241, c_32])).
% 2.09/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.25  
% 2.09/1.25  Inference rules
% 2.09/1.25  ----------------------
% 2.09/1.25  #Ref     : 0
% 2.09/1.25  #Sup     : 50
% 2.09/1.25  #Fact    : 0
% 2.09/1.25  #Define  : 0
% 2.09/1.25  #Split   : 0
% 2.09/1.25  #Chain   : 0
% 2.09/1.25  #Close   : 0
% 2.09/1.25  
% 2.09/1.25  Ordering : KBO
% 2.09/1.25  
% 2.09/1.25  Simplification rules
% 2.09/1.25  ----------------------
% 2.09/1.25  #Subsume      : 4
% 2.09/1.25  #Demod        : 21
% 2.09/1.25  #Tautology    : 26
% 2.09/1.25  #SimpNegUnit  : 2
% 2.09/1.25  #BackRed      : 3
% 2.09/1.25  
% 2.09/1.25  #Partial instantiations: 0
% 2.09/1.25  #Strategies tried      : 1
% 2.09/1.25  
% 2.09/1.25  Timing (in seconds)
% 2.09/1.25  ----------------------
% 2.09/1.26  Preprocessing        : 0.27
% 2.09/1.26  Parsing              : 0.15
% 2.09/1.26  CNF conversion       : 0.02
% 2.09/1.26  Main loop            : 0.19
% 2.09/1.26  Inferencing          : 0.08
% 2.09/1.26  Reduction            : 0.05
% 2.09/1.26  Demodulation         : 0.04
% 2.09/1.26  BG Simplification    : 0.01
% 2.09/1.26  Subsumption          : 0.03
% 2.09/1.26  Abstraction          : 0.01
% 2.09/1.26  MUC search           : 0.00
% 2.09/1.26  Cooper               : 0.00
% 2.09/1.26  Total                : 0.49
% 2.09/1.26  Index Insertion      : 0.00
% 2.09/1.26  Index Deletion       : 0.00
% 2.09/1.26  Index Matching       : 0.00
% 2.09/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
