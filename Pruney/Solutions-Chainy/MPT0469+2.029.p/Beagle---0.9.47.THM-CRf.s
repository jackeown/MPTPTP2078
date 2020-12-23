%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:55 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   54 (  64 expanded)
%              Number of leaves         :   28 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   57 (  76 expanded)
%              Number of equality atoms :   13 (  22 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_3 > #skF_7 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_77,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k1_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_52,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_50,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_30,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_44,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_32,plain,(
    ! [A_34] :
      ( v1_relat_1(A_34)
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_36,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_32])).

tff(c_28,plain,(
    ! [A_30,B_31] :
      ( r2_hidden('#skF_7'(A_30,B_31),k2_relat_1(B_31))
      | ~ r2_hidden(A_30,k1_relat_1(B_31))
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_83,plain,(
    ! [A_52,C_53] :
      ( r2_hidden(k4_tarski('#skF_6'(A_52,k2_relat_1(A_52),C_53),C_53),A_52)
      | ~ r2_hidden(C_53,k2_relat_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_46,plain,(
    ! [A_37,B_38,C_39] :
      ( ~ r1_xboole_0(A_37,B_38)
      | ~ r2_hidden(C_39,k3_xboole_0(A_37,B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_53,plain,(
    ! [A_8,C_39] :
      ( ~ r1_xboole_0(A_8,k1_xboole_0)
      | ~ r2_hidden(C_39,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_46])).

tff(c_56,plain,(
    ! [C_39] : ~ r2_hidden(C_39,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_53])).

tff(c_98,plain,(
    ! [C_54] : ~ r2_hidden(C_54,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_83,c_56])).

tff(c_106,plain,(
    ! [A_30] :
      ( ~ r2_hidden(A_30,k1_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_28,c_98])).

tff(c_132,plain,(
    ! [A_55] : ~ r2_hidden(A_55,k1_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_106])).

tff(c_140,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_132])).

tff(c_145,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_140])).

tff(c_146,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_190,plain,(
    ! [A_72,C_73] :
      ( r2_hidden(k4_tarski('#skF_6'(A_72,k2_relat_1(A_72),C_73),C_73),A_72)
      | ~ r2_hidden(C_73,k2_relat_1(A_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_153,plain,(
    ! [A_57,B_58,C_59] :
      ( ~ r1_xboole_0(A_57,B_58)
      | ~ r2_hidden(C_59,k3_xboole_0(A_57,B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_160,plain,(
    ! [A_8,C_59] :
      ( ~ r1_xboole_0(A_8,k1_xboole_0)
      | ~ r2_hidden(C_59,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_153])).

tff(c_163,plain,(
    ! [C_59] : ~ r2_hidden(C_59,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_160])).

tff(c_205,plain,(
    ! [C_74] : ~ r2_hidden(C_74,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_190,c_163])).

tff(c_217,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_205])).

tff(c_225,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_217])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:41:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.28  
% 1.84/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.28  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_3 > #skF_7 > #skF_1 > #skF_5 > #skF_4
% 1.84/1.28  
% 1.84/1.28  %Foreground sorts:
% 1.84/1.28  
% 1.84/1.28  
% 1.84/1.28  %Background operators:
% 1.84/1.28  
% 1.84/1.28  
% 1.84/1.28  %Foreground operators:
% 1.84/1.28  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.84/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.84/1.28  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 1.84/1.28  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.84/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.84/1.28  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.84/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.84/1.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.84/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.84/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.84/1.28  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 1.84/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.84/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.84/1.28  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 1.84/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.84/1.28  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.84/1.28  
% 1.84/1.29  tff(f_77, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.84/1.29  tff(f_48, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.84/1.29  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.84/1.29  tff(f_56, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.84/1.29  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k1_relat_1(B)) & (![C]: ~r2_hidden(C, k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_relat_1)).
% 1.84/1.29  tff(f_64, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 1.84/1.29  tff(f_52, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.84/1.29  tff(f_50, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.84/1.29  tff(f_40, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.84/1.29  tff(c_30, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.84/1.29  tff(c_44, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_30])).
% 1.84/1.29  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.84/1.29  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.84/1.29  tff(c_32, plain, (![A_34]: (v1_relat_1(A_34) | ~v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.84/1.29  tff(c_36, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_32])).
% 1.84/1.29  tff(c_28, plain, (![A_30, B_31]: (r2_hidden('#skF_7'(A_30, B_31), k2_relat_1(B_31)) | ~r2_hidden(A_30, k1_relat_1(B_31)) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.84/1.29  tff(c_83, plain, (![A_52, C_53]: (r2_hidden(k4_tarski('#skF_6'(A_52, k2_relat_1(A_52), C_53), C_53), A_52) | ~r2_hidden(C_53, k2_relat_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.84/1.29  tff(c_12, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.84/1.29  tff(c_10, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.84/1.29  tff(c_46, plain, (![A_37, B_38, C_39]: (~r1_xboole_0(A_37, B_38) | ~r2_hidden(C_39, k3_xboole_0(A_37, B_38)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.84/1.29  tff(c_53, plain, (![A_8, C_39]: (~r1_xboole_0(A_8, k1_xboole_0) | ~r2_hidden(C_39, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_46])).
% 1.84/1.29  tff(c_56, plain, (![C_39]: (~r2_hidden(C_39, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_53])).
% 1.84/1.29  tff(c_98, plain, (![C_54]: (~r2_hidden(C_54, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_83, c_56])).
% 1.84/1.29  tff(c_106, plain, (![A_30]: (~r2_hidden(A_30, k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_98])).
% 1.84/1.29  tff(c_132, plain, (![A_55]: (~r2_hidden(A_55, k1_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_106])).
% 1.84/1.29  tff(c_140, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_132])).
% 1.84/1.29  tff(c_145, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_140])).
% 1.84/1.29  tff(c_146, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_30])).
% 1.84/1.29  tff(c_190, plain, (![A_72, C_73]: (r2_hidden(k4_tarski('#skF_6'(A_72, k2_relat_1(A_72), C_73), C_73), A_72) | ~r2_hidden(C_73, k2_relat_1(A_72)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.84/1.29  tff(c_153, plain, (![A_57, B_58, C_59]: (~r1_xboole_0(A_57, B_58) | ~r2_hidden(C_59, k3_xboole_0(A_57, B_58)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.84/1.29  tff(c_160, plain, (![A_8, C_59]: (~r1_xboole_0(A_8, k1_xboole_0) | ~r2_hidden(C_59, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_153])).
% 1.84/1.29  tff(c_163, plain, (![C_59]: (~r2_hidden(C_59, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_160])).
% 1.84/1.29  tff(c_205, plain, (![C_74]: (~r2_hidden(C_74, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_190, c_163])).
% 1.84/1.29  tff(c_217, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_205])).
% 1.84/1.29  tff(c_225, plain, $false, inference(negUnitSimplification, [status(thm)], [c_146, c_217])).
% 1.84/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.29  
% 1.84/1.29  Inference rules
% 1.84/1.29  ----------------------
% 1.84/1.29  #Ref     : 0
% 1.84/1.29  #Sup     : 35
% 1.84/1.29  #Fact    : 0
% 1.84/1.29  #Define  : 0
% 1.84/1.29  #Split   : 1
% 1.84/1.29  #Chain   : 0
% 1.84/1.29  #Close   : 0
% 1.84/1.29  
% 1.84/1.29  Ordering : KBO
% 1.84/1.29  
% 1.84/1.29  Simplification rules
% 1.84/1.29  ----------------------
% 1.84/1.29  #Subsume      : 3
% 1.84/1.29  #Demod        : 12
% 1.84/1.29  #Tautology    : 16
% 1.84/1.29  #SimpNegUnit  : 6
% 1.84/1.29  #BackRed      : 1
% 1.84/1.29  
% 1.84/1.29  #Partial instantiations: 0
% 1.84/1.29  #Strategies tried      : 1
% 1.84/1.29  
% 1.84/1.29  Timing (in seconds)
% 1.84/1.29  ----------------------
% 1.84/1.29  Preprocessing        : 0.30
% 1.84/1.29  Parsing              : 0.16
% 1.84/1.29  CNF conversion       : 0.02
% 1.84/1.29  Main loop            : 0.15
% 1.84/1.29  Inferencing          : 0.06
% 1.84/1.29  Reduction            : 0.04
% 1.84/1.29  Demodulation         : 0.03
% 1.84/1.29  BG Simplification    : 0.01
% 1.84/1.29  Subsumption          : 0.02
% 1.84/1.29  Abstraction          : 0.01
% 1.84/1.29  MUC search           : 0.00
% 1.84/1.29  Cooper               : 0.00
% 1.84/1.29  Total                : 0.48
% 1.84/1.29  Index Insertion      : 0.00
% 1.84/1.29  Index Deletion       : 0.00
% 1.84/1.29  Index Matching       : 0.00
% 1.84/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
