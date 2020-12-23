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
% DateTime   : Thu Dec  3 09:58:54 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   54 (  65 expanded)
%              Number of leaves         :   28 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   58 (  78 expanded)
%              Number of equality atoms :   14 (  26 expanded)
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

tff(f_64,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

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
     => ~ ( r2_hidden(A,k2_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relat_1)).

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

tff(c_83,plain,(
    ! [C_52,A_53] :
      ( r2_hidden(k4_tarski(C_52,'#skF_6'(A_53,k1_relat_1(A_53),C_52)),A_53)
      | ~ r2_hidden(C_52,k1_relat_1(A_53)) ) ),
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
    ! [C_54] : ~ r2_hidden(C_54,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_83,c_56])).

tff(c_110,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_98])).

tff(c_118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_110])).

tff(c_119,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_126,plain,(
    ! [A_56,B_57,C_58] :
      ( ~ r1_xboole_0(A_56,B_57)
      | ~ r2_hidden(C_58,k3_xboole_0(A_56,B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_133,plain,(
    ! [A_8,C_58] :
      ( ~ r1_xboole_0(A_8,k1_xboole_0)
      | ~ r2_hidden(C_58,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_126])).

tff(c_136,plain,(
    ! [C_58] : ~ r2_hidden(C_58,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_133])).

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

tff(c_120,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_161,plain,(
    ! [A_67,B_68] :
      ( r2_hidden('#skF_7'(A_67,B_68),k1_relat_1(B_68))
      | ~ r2_hidden(A_67,k2_relat_1(B_68))
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_164,plain,(
    ! [A_67] :
      ( r2_hidden('#skF_7'(A_67,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_67,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_161])).

tff(c_166,plain,(
    ! [A_67] :
      ( r2_hidden('#skF_7'(A_67,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_67,k2_relat_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_164])).

tff(c_168,plain,(
    ! [A_69] : ~ r2_hidden(A_69,k2_relat_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_166])).

tff(c_172,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_168])).

tff(c_176,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_172])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:00:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.11  
% 1.73/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.12  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_3 > #skF_7 > #skF_1 > #skF_5 > #skF_4
% 1.73/1.12  
% 1.73/1.12  %Foreground sorts:
% 1.73/1.12  
% 1.73/1.12  
% 1.73/1.12  %Background operators:
% 1.73/1.12  
% 1.73/1.12  
% 1.73/1.12  %Foreground operators:
% 1.73/1.12  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.73/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.73/1.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.73/1.12  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 1.73/1.12  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.73/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.73/1.12  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.73/1.12  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.73/1.12  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.73/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.73/1.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.73/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.73/1.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.73/1.12  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 1.73/1.12  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.73/1.12  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.73/1.12  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 1.73/1.12  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.73/1.12  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.73/1.12  
% 1.88/1.13  tff(f_77, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.88/1.13  tff(f_48, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.88/1.13  tff(f_64, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 1.88/1.13  tff(f_52, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.88/1.13  tff(f_50, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.88/1.13  tff(f_40, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.88/1.13  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.88/1.13  tff(f_56, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.88/1.13  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k2_relat_1(B)) & (![C]: ~r2_hidden(C, k1_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_relat_1)).
% 1.88/1.13  tff(c_30, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.88/1.13  tff(c_44, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_30])).
% 1.88/1.13  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.88/1.13  tff(c_83, plain, (![C_52, A_53]: (r2_hidden(k4_tarski(C_52, '#skF_6'(A_53, k1_relat_1(A_53), C_52)), A_53) | ~r2_hidden(C_52, k1_relat_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.88/1.13  tff(c_12, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.88/1.13  tff(c_10, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.88/1.13  tff(c_46, plain, (![A_37, B_38, C_39]: (~r1_xboole_0(A_37, B_38) | ~r2_hidden(C_39, k3_xboole_0(A_37, B_38)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.88/1.13  tff(c_53, plain, (![A_8, C_39]: (~r1_xboole_0(A_8, k1_xboole_0) | ~r2_hidden(C_39, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_46])).
% 1.88/1.13  tff(c_56, plain, (![C_39]: (~r2_hidden(C_39, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_53])).
% 1.88/1.13  tff(c_98, plain, (![C_54]: (~r2_hidden(C_54, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_83, c_56])).
% 1.88/1.13  tff(c_110, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_98])).
% 1.88/1.13  tff(c_118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_110])).
% 1.88/1.13  tff(c_119, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_30])).
% 1.88/1.13  tff(c_126, plain, (![A_56, B_57, C_58]: (~r1_xboole_0(A_56, B_57) | ~r2_hidden(C_58, k3_xboole_0(A_56, B_57)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.88/1.13  tff(c_133, plain, (![A_8, C_58]: (~r1_xboole_0(A_8, k1_xboole_0) | ~r2_hidden(C_58, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_126])).
% 1.88/1.13  tff(c_136, plain, (![C_58]: (~r2_hidden(C_58, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_133])).
% 1.88/1.13  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.88/1.13  tff(c_32, plain, (![A_34]: (v1_relat_1(A_34) | ~v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.88/1.13  tff(c_36, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_32])).
% 1.88/1.13  tff(c_120, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_30])).
% 1.88/1.13  tff(c_161, plain, (![A_67, B_68]: (r2_hidden('#skF_7'(A_67, B_68), k1_relat_1(B_68)) | ~r2_hidden(A_67, k2_relat_1(B_68)) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.88/1.13  tff(c_164, plain, (![A_67]: (r2_hidden('#skF_7'(A_67, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_67, k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_120, c_161])).
% 1.88/1.13  tff(c_166, plain, (![A_67]: (r2_hidden('#skF_7'(A_67, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_67, k2_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_164])).
% 1.88/1.13  tff(c_168, plain, (![A_69]: (~r2_hidden(A_69, k2_relat_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_136, c_166])).
% 1.88/1.13  tff(c_172, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_168])).
% 1.88/1.13  tff(c_176, plain, $false, inference(negUnitSimplification, [status(thm)], [c_119, c_172])).
% 1.88/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.13  
% 1.88/1.13  Inference rules
% 1.88/1.13  ----------------------
% 1.88/1.13  #Ref     : 0
% 1.88/1.13  #Sup     : 25
% 1.88/1.13  #Fact    : 0
% 1.88/1.13  #Define  : 0
% 1.88/1.13  #Split   : 1
% 1.88/1.13  #Chain   : 0
% 1.88/1.13  #Close   : 0
% 1.88/1.13  
% 1.88/1.13  Ordering : KBO
% 1.88/1.13  
% 1.88/1.13  Simplification rules
% 1.88/1.13  ----------------------
% 1.88/1.13  #Subsume      : 0
% 1.88/1.13  #Demod        : 8
% 1.88/1.13  #Tautology    : 13
% 1.88/1.13  #SimpNegUnit  : 5
% 1.88/1.13  #BackRed      : 0
% 1.88/1.13  
% 1.88/1.13  #Partial instantiations: 0
% 1.88/1.13  #Strategies tried      : 1
% 1.88/1.13  
% 1.88/1.13  Timing (in seconds)
% 1.88/1.13  ----------------------
% 1.88/1.13  Preprocessing        : 0.27
% 1.88/1.13  Parsing              : 0.15
% 1.88/1.13  CNF conversion       : 0.02
% 1.88/1.13  Main loop            : 0.14
% 1.88/1.13  Inferencing          : 0.06
% 1.88/1.13  Reduction            : 0.04
% 1.88/1.13  Demodulation         : 0.03
% 1.88/1.13  BG Simplification    : 0.01
% 1.88/1.13  Subsumption          : 0.02
% 1.88/1.13  Abstraction          : 0.01
% 1.88/1.13  MUC search           : 0.00
% 1.88/1.13  Cooper               : 0.00
% 1.88/1.13  Total                : 0.44
% 1.88/1.13  Index Insertion      : 0.00
% 1.88/1.13  Index Deletion       : 0.00
% 1.88/1.13  Index Matching       : 0.00
% 1.88/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
