%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:41 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   56 (  75 expanded)
%              Number of leaves         :   30 (  38 expanded)
%              Depth                    :    7
%              Number of atoms          :   55 (  88 expanded)
%              Number of equality atoms :   26 (  49 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_70,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_49,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k9_relat_1(B,A) = k9_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_relat_1)).

tff(f_77,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_76,plain,(
    ! [A_40] :
      ( k7_relat_1(A_40,k1_relat_1(A_40)) = A_40
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_85,plain,
    ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_76])).

tff(c_89,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_20,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_2'(A_12),A_12)
      | v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_14,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_137,plain,(
    ! [A_47,B_48,C_49] :
      ( ~ r1_xboole_0(A_47,B_48)
      | ~ r2_hidden(C_49,k3_xboole_0(A_47,B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_147,plain,(
    ! [A_6,C_49] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_49,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_137])).

tff(c_151,plain,(
    ! [C_50] : ~ r2_hidden(C_50,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_147])).

tff(c_155,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_151])).

tff(c_159,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_155])).

tff(c_161,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_26,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_160,plain,(
    k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_301,plain,(
    ! [B_62,A_63] :
      ( k2_relat_1(k7_relat_1(B_62,A_63)) = k9_relat_1(B_62,A_63)
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_310,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_301])).

tff(c_317,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_26,c_310])).

tff(c_166,plain,(
    ! [A_51,B_52] : k4_xboole_0(A_51,k4_xboole_0(A_51,B_52)) = k3_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_10] : k4_xboole_0(k1_xboole_0,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_176,plain,(
    ! [B_52] : k3_xboole_0(k1_xboole_0,B_52) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_12])).

tff(c_370,plain,(
    ! [B_70,A_71] :
      ( k9_relat_1(B_70,k3_xboole_0(k1_relat_1(B_70),A_71)) = k9_relat_1(B_70,A_71)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_387,plain,(
    ! [A_71] :
      ( k9_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,A_71)) = k9_relat_1(k1_xboole_0,A_71)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_370])).

tff(c_393,plain,(
    ! [A_71] : k9_relat_1(k1_xboole_0,A_71) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_317,c_176,c_387])).

tff(c_32,plain,(
    k9_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_397,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_393,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 13:33:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.27  
% 1.96/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.27  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4
% 1.96/1.27  
% 1.96/1.27  %Foreground sorts:
% 1.96/1.27  
% 1.96/1.27  
% 1.96/1.27  %Background operators:
% 1.96/1.27  
% 1.96/1.27  
% 1.96/1.27  %Foreground operators:
% 1.96/1.27  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.96/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.96/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.96/1.27  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.96/1.27  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.96/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.96/1.27  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.96/1.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.96/1.27  tff('#skF_5', type, '#skF_5': $i).
% 1.96/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.96/1.27  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.96/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.96/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.96/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.96/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.96/1.27  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.96/1.27  
% 1.96/1.28  tff(f_70, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.96/1.28  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 1.96/1.28  tff(f_59, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 1.96/1.28  tff(f_49, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.96/1.28  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.96/1.28  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.96/1.28  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.96/1.28  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.96/1.28  tff(f_47, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 1.96/1.28  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (k9_relat_1(B, A) = k9_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_relat_1)).
% 1.96/1.28  tff(f_77, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 1.96/1.28  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.96/1.28  tff(c_76, plain, (![A_40]: (k7_relat_1(A_40, k1_relat_1(A_40))=A_40 | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.96/1.28  tff(c_85, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_76])).
% 1.96/1.28  tff(c_89, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_85])).
% 1.96/1.28  tff(c_20, plain, (![A_12]: (r2_hidden('#skF_2'(A_12), A_12) | v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.96/1.28  tff(c_14, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.96/1.28  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.96/1.28  tff(c_137, plain, (![A_47, B_48, C_49]: (~r1_xboole_0(A_47, B_48) | ~r2_hidden(C_49, k3_xboole_0(A_47, B_48)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.96/1.28  tff(c_147, plain, (![A_6, C_49]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_49, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_137])).
% 1.96/1.28  tff(c_151, plain, (![C_50]: (~r2_hidden(C_50, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_147])).
% 1.96/1.28  tff(c_155, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_151])).
% 1.96/1.28  tff(c_159, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89, c_155])).
% 1.96/1.28  tff(c_161, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_85])).
% 1.96/1.28  tff(c_26, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.96/1.28  tff(c_160, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_85])).
% 1.96/1.28  tff(c_301, plain, (![B_62, A_63]: (k2_relat_1(k7_relat_1(B_62, A_63))=k9_relat_1(B_62, A_63) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.96/1.28  tff(c_310, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_160, c_301])).
% 1.96/1.28  tff(c_317, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_161, c_26, c_310])).
% 1.96/1.28  tff(c_166, plain, (![A_51, B_52]: (k4_xboole_0(A_51, k4_xboole_0(A_51, B_52))=k3_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.96/1.28  tff(c_12, plain, (![A_10]: (k4_xboole_0(k1_xboole_0, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.96/1.28  tff(c_176, plain, (![B_52]: (k3_xboole_0(k1_xboole_0, B_52)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_166, c_12])).
% 1.96/1.28  tff(c_370, plain, (![B_70, A_71]: (k9_relat_1(B_70, k3_xboole_0(k1_relat_1(B_70), A_71))=k9_relat_1(B_70, A_71) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.96/1.28  tff(c_387, plain, (![A_71]: (k9_relat_1(k1_xboole_0, k3_xboole_0(k1_xboole_0, A_71))=k9_relat_1(k1_xboole_0, A_71) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_370])).
% 1.96/1.28  tff(c_393, plain, (![A_71]: (k9_relat_1(k1_xboole_0, A_71)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_161, c_317, c_176, c_387])).
% 1.96/1.28  tff(c_32, plain, (k9_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.96/1.28  tff(c_397, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_393, c_32])).
% 1.96/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.28  
% 1.96/1.28  Inference rules
% 1.96/1.28  ----------------------
% 1.96/1.28  #Ref     : 0
% 1.96/1.28  #Sup     : 85
% 1.96/1.28  #Fact    : 0
% 1.96/1.28  #Define  : 0
% 1.96/1.28  #Split   : 1
% 1.96/1.28  #Chain   : 0
% 1.96/1.28  #Close   : 0
% 1.96/1.28  
% 1.96/1.28  Ordering : KBO
% 1.96/1.28  
% 1.96/1.28  Simplification rules
% 1.96/1.28  ----------------------
% 1.96/1.28  #Subsume      : 3
% 1.96/1.28  #Demod        : 24
% 1.96/1.28  #Tautology    : 59
% 1.96/1.28  #SimpNegUnit  : 3
% 1.96/1.28  #BackRed      : 1
% 1.96/1.28  
% 1.96/1.28  #Partial instantiations: 0
% 1.96/1.28  #Strategies tried      : 1
% 1.96/1.28  
% 1.96/1.28  Timing (in seconds)
% 1.96/1.28  ----------------------
% 1.96/1.29  Preprocessing        : 0.28
% 1.96/1.29  Parsing              : 0.16
% 1.96/1.29  CNF conversion       : 0.02
% 1.96/1.29  Main loop            : 0.22
% 1.96/1.29  Inferencing          : 0.09
% 1.96/1.29  Reduction            : 0.06
% 1.96/1.29  Demodulation         : 0.05
% 1.96/1.29  BG Simplification    : 0.01
% 1.96/1.29  Subsumption          : 0.03
% 1.96/1.29  Abstraction          : 0.01
% 1.96/1.29  MUC search           : 0.00
% 1.96/1.29  Cooper               : 0.00
% 1.96/1.29  Total                : 0.53
% 1.96/1.29  Index Insertion      : 0.00
% 1.96/1.29  Index Deletion       : 0.00
% 1.96/1.29  Index Matching       : 0.00
% 1.96/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
