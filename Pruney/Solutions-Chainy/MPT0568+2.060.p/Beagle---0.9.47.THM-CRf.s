%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:28 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   52 (  55 expanded)
%              Number of leaves         :   30 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   59 (  63 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_50,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_48,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_82,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_85,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_80,plain,(
    ! [A_51,B_52,C_53] :
      ( ~ r1_xboole_0(A_51,B_52)
      | ~ r2_hidden(C_53,k3_xboole_0(A_51,B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_91,plain,(
    ! [A_10,C_53] :
      ( ~ r1_xboole_0(A_10,k1_xboole_0)
      | ~ r2_hidden(C_53,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_80])).

tff(c_95,plain,(
    ! [C_53] : ~ r2_hidden(C_53,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_91])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_64,plain,(
    ! [A_45] :
      ( r2_hidden('#skF_3'(A_45),A_45)
      | v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_69,plain,(
    ! [A_46] :
      ( ~ v1_xboole_0(A_46)
      | v1_relat_1(A_46) ) ),
    inference(resolution,[status(thm)],[c_64,c_2])).

tff(c_73,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_69])).

tff(c_32,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_230,plain,(
    ! [A_80,B_81,C_82] :
      ( r2_hidden('#skF_6'(A_80,B_81,C_82),k2_relat_1(C_82))
      | ~ r2_hidden(A_80,k10_relat_1(C_82,B_81))
      | ~ v1_relat_1(C_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_236,plain,(
    ! [A_80,B_81] :
      ( r2_hidden('#skF_6'(A_80,B_81,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_80,k10_relat_1(k1_xboole_0,B_81))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_230])).

tff(c_239,plain,(
    ! [A_80,B_81] :
      ( r2_hidden('#skF_6'(A_80,B_81,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_80,k10_relat_1(k1_xboole_0,B_81)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_236])).

tff(c_241,plain,(
    ! [A_83,B_84] : ~ r2_hidden(A_83,k10_relat_1(k1_xboole_0,B_84)) ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_239])).

tff(c_257,plain,(
    ! [B_85] : v1_xboole_0(k10_relat_1(k1_xboole_0,B_85)) ),
    inference(resolution,[status(thm)],[c_4,c_241])).

tff(c_54,plain,(
    ! [B_42,A_43] :
      ( ~ v1_xboole_0(B_42)
      | B_42 = A_43
      | ~ v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_57,plain,(
    ! [A_43] :
      ( k1_xboole_0 = A_43
      | ~ v1_xboole_0(A_43) ) ),
    inference(resolution,[status(thm)],[c_6,c_54])).

tff(c_270,plain,(
    ! [B_85] : k10_relat_1(k1_xboole_0,B_85) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_257,c_57])).

tff(c_36,plain,(
    k10_relat_1(k1_xboole_0,'#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_281,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:26:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.34  
% 2.17/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.34  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_2 > #skF_5 > #skF_4
% 2.17/1.34  
% 2.17/1.34  %Foreground sorts:
% 2.17/1.34  
% 2.17/1.34  
% 2.17/1.34  %Background operators:
% 2.17/1.34  
% 2.17/1.34  
% 2.17/1.34  %Foreground operators:
% 2.17/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.34  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.17/1.34  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.17/1.34  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.17/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.17/1.34  tff('#skF_7', type, '#skF_7': $i).
% 2.17/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.17/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.17/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.34  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.17/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.17/1.34  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.17/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.17/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.17/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.17/1.34  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.17/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.17/1.34  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.17/1.34  
% 2.17/1.35  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.17/1.35  tff(f_50, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.17/1.35  tff(f_48, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.17/1.35  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.17/1.35  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.17/1.35  tff(f_68, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.17/1.35  tff(f_82, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.17/1.35  tff(f_79, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 2.17/1.35  tff(f_58, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 2.17/1.35  tff(f_85, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 2.17/1.35  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.17/1.35  tff(c_14, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.17/1.35  tff(c_12, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.17/1.35  tff(c_80, plain, (![A_51, B_52, C_53]: (~r1_xboole_0(A_51, B_52) | ~r2_hidden(C_53, k3_xboole_0(A_51, B_52)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.17/1.35  tff(c_91, plain, (![A_10, C_53]: (~r1_xboole_0(A_10, k1_xboole_0) | ~r2_hidden(C_53, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_80])).
% 2.17/1.35  tff(c_95, plain, (![C_53]: (~r2_hidden(C_53, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_91])).
% 2.17/1.35  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.17/1.35  tff(c_64, plain, (![A_45]: (r2_hidden('#skF_3'(A_45), A_45) | v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.17/1.35  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.17/1.35  tff(c_69, plain, (![A_46]: (~v1_xboole_0(A_46) | v1_relat_1(A_46))), inference(resolution, [status(thm)], [c_64, c_2])).
% 2.17/1.35  tff(c_73, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_69])).
% 2.17/1.35  tff(c_32, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.17/1.35  tff(c_230, plain, (![A_80, B_81, C_82]: (r2_hidden('#skF_6'(A_80, B_81, C_82), k2_relat_1(C_82)) | ~r2_hidden(A_80, k10_relat_1(C_82, B_81)) | ~v1_relat_1(C_82))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.17/1.35  tff(c_236, plain, (![A_80, B_81]: (r2_hidden('#skF_6'(A_80, B_81, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_80, k10_relat_1(k1_xboole_0, B_81)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_230])).
% 2.17/1.35  tff(c_239, plain, (![A_80, B_81]: (r2_hidden('#skF_6'(A_80, B_81, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_80, k10_relat_1(k1_xboole_0, B_81)))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_236])).
% 2.17/1.35  tff(c_241, plain, (![A_83, B_84]: (~r2_hidden(A_83, k10_relat_1(k1_xboole_0, B_84)))), inference(negUnitSimplification, [status(thm)], [c_95, c_239])).
% 2.17/1.35  tff(c_257, plain, (![B_85]: (v1_xboole_0(k10_relat_1(k1_xboole_0, B_85)))), inference(resolution, [status(thm)], [c_4, c_241])).
% 2.17/1.35  tff(c_54, plain, (![B_42, A_43]: (~v1_xboole_0(B_42) | B_42=A_43 | ~v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.17/1.35  tff(c_57, plain, (![A_43]: (k1_xboole_0=A_43 | ~v1_xboole_0(A_43))), inference(resolution, [status(thm)], [c_6, c_54])).
% 2.17/1.35  tff(c_270, plain, (![B_85]: (k10_relat_1(k1_xboole_0, B_85)=k1_xboole_0)), inference(resolution, [status(thm)], [c_257, c_57])).
% 2.17/1.35  tff(c_36, plain, (k10_relat_1(k1_xboole_0, '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.17/1.35  tff(c_281, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_270, c_36])).
% 2.17/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.35  
% 2.17/1.35  Inference rules
% 2.17/1.35  ----------------------
% 2.17/1.35  #Ref     : 1
% 2.17/1.35  #Sup     : 51
% 2.17/1.35  #Fact    : 0
% 2.17/1.35  #Define  : 0
% 2.17/1.35  #Split   : 0
% 2.17/1.35  #Chain   : 0
% 2.17/1.35  #Close   : 0
% 2.17/1.35  
% 2.17/1.35  Ordering : KBO
% 2.17/1.35  
% 2.17/1.35  Simplification rules
% 2.17/1.35  ----------------------
% 2.17/1.35  #Subsume      : 3
% 2.17/1.35  #Demod        : 19
% 2.17/1.35  #Tautology    : 22
% 2.17/1.35  #SimpNegUnit  : 1
% 2.17/1.35  #BackRed      : 4
% 2.17/1.35  
% 2.17/1.35  #Partial instantiations: 0
% 2.17/1.35  #Strategies tried      : 1
% 2.17/1.35  
% 2.17/1.35  Timing (in seconds)
% 2.17/1.35  ----------------------
% 2.17/1.35  Preprocessing        : 0.31
% 2.17/1.36  Parsing              : 0.17
% 2.17/1.36  CNF conversion       : 0.03
% 2.17/1.36  Main loop            : 0.20
% 2.17/1.36  Inferencing          : 0.08
% 2.17/1.36  Reduction            : 0.05
% 2.17/1.36  Demodulation         : 0.04
% 2.17/1.36  BG Simplification    : 0.01
% 2.17/1.36  Subsumption          : 0.03
% 2.17/1.36  Abstraction          : 0.01
% 2.17/1.36  MUC search           : 0.00
% 2.17/1.36  Cooper               : 0.00
% 2.17/1.36  Total                : 0.53
% 2.17/1.36  Index Insertion      : 0.00
% 2.17/1.36  Index Deletion       : 0.00
% 2.17/1.36  Index Matching       : 0.00
% 2.17/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
