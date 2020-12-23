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
% DateTime   : Thu Dec  3 10:02:22 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :   58 (  76 expanded)
%              Number of leaves         :   28 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   72 ( 112 expanded)
%              Number of equality atoms :   14 (  26 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k11_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_10 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

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

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_16,plain,(
    ! [A_10] : r1_xboole_0(A_10,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_235,plain,(
    ! [A_74,B_75,C_76] :
      ( ~ r1_xboole_0(A_74,B_75)
      | ~ r2_hidden(C_76,k3_xboole_0(A_74,B_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_238,plain,(
    ! [A_9,C_76] :
      ( ~ r1_xboole_0(A_9,k1_xboole_0)
      | ~ r2_hidden(C_76,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_235])).

tff(c_240,plain,(
    ! [C_76] : ~ r2_hidden(C_76,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_238])).

tff(c_40,plain,
    ( k11_relat_1('#skF_10','#skF_9') = k1_xboole_0
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_55,plain,(
    ~ r2_hidden('#skF_9',k1_relat_1('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_46,plain,
    ( r2_hidden('#skF_9',k1_relat_1('#skF_10'))
    | k11_relat_1('#skF_10','#skF_9') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_63,plain,(
    k11_relat_1('#skF_10','#skF_9') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_46])).

tff(c_38,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_129,plain,(
    ! [A_61,B_62] :
      ( r2_hidden('#skF_1'(A_61,B_62),B_62)
      | r2_hidden('#skF_2'(A_61,B_62),A_61)
      | B_62 = A_61 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_56,plain,(
    ! [A_42,B_43,C_44] :
      ( ~ r1_xboole_0(A_42,B_43)
      | ~ r2_hidden(C_44,k3_xboole_0(A_42,B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_59,plain,(
    ! [A_9,C_44] :
      ( ~ r1_xboole_0(A_9,k1_xboole_0)
      | ~ r2_hidden(C_44,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_56])).

tff(c_61,plain,(
    ! [C_44] : ~ r2_hidden(C_44,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_59])).

tff(c_155,plain,(
    ! [B_62] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_62),B_62)
      | k1_xboole_0 = B_62 ) ),
    inference(resolution,[status(thm)],[c_129,c_61])).

tff(c_108,plain,(
    ! [A_58,B_59,C_60] :
      ( r2_hidden(k4_tarski(A_58,B_59),C_60)
      | ~ r2_hidden(B_59,k11_relat_1(C_60,A_58))
      | ~ v1_relat_1(C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_24,plain,(
    ! [C_33,A_18,D_36] :
      ( r2_hidden(C_33,k1_relat_1(A_18))
      | ~ r2_hidden(k4_tarski(C_33,D_36),A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_185,plain,(
    ! [A_69,C_70,B_71] :
      ( r2_hidden(A_69,k1_relat_1(C_70))
      | ~ r2_hidden(B_71,k11_relat_1(C_70,A_69))
      | ~ v1_relat_1(C_70) ) ),
    inference(resolution,[status(thm)],[c_108,c_24])).

tff(c_210,plain,(
    ! [A_72,C_73] :
      ( r2_hidden(A_72,k1_relat_1(C_73))
      | ~ v1_relat_1(C_73)
      | k11_relat_1(C_73,A_72) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_155,c_185])).

tff(c_221,plain,
    ( ~ v1_relat_1('#skF_10')
    | k11_relat_1('#skF_10','#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_210,c_55])).

tff(c_226,plain,(
    k11_relat_1('#skF_10','#skF_9') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_221])).

tff(c_228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_226])).

tff(c_230,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_229,plain,(
    k11_relat_1('#skF_10','#skF_9') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_453,plain,(
    ! [C_112,A_113] :
      ( r2_hidden(k4_tarski(C_112,'#skF_8'(A_113,k1_relat_1(A_113),C_112)),A_113)
      | ~ r2_hidden(C_112,k1_relat_1(A_113)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_36,plain,(
    ! [B_38,C_39,A_37] :
      ( r2_hidden(B_38,k11_relat_1(C_39,A_37))
      | ~ r2_hidden(k4_tarski(A_37,B_38),C_39)
      | ~ v1_relat_1(C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2015,plain,(
    ! [A_195,C_196] :
      ( r2_hidden('#skF_8'(A_195,k1_relat_1(A_195),C_196),k11_relat_1(A_195,C_196))
      | ~ v1_relat_1(A_195)
      | ~ r2_hidden(C_196,k1_relat_1(A_195)) ) ),
    inference(resolution,[status(thm)],[c_453,c_36])).

tff(c_2048,plain,
    ( r2_hidden('#skF_8'('#skF_10',k1_relat_1('#skF_10'),'#skF_9'),k1_xboole_0)
    | ~ v1_relat_1('#skF_10')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_2015])).

tff(c_2054,plain,(
    r2_hidden('#skF_8'('#skF_10',k1_relat_1('#skF_10'),'#skF_9'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_38,c_2048])).

tff(c_2056,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_240,c_2054])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:04:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.54/1.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.73  
% 3.54/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.73  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k11_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_10 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_4
% 3.54/1.73  
% 3.54/1.73  %Foreground sorts:
% 3.54/1.73  
% 3.54/1.73  
% 3.54/1.73  %Background operators:
% 3.54/1.73  
% 3.54/1.73  
% 3.54/1.73  %Foreground operators:
% 3.54/1.73  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.54/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.54/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.54/1.73  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.54/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.54/1.73  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.54/1.73  tff('#skF_10', type, '#skF_10': $i).
% 3.54/1.73  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.54/1.73  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.54/1.73  tff('#skF_9', type, '#skF_9': $i).
% 3.54/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.54/1.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.54/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.54/1.73  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.54/1.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.54/1.73  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 3.54/1.73  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.54/1.73  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.54/1.73  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.54/1.73  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.54/1.73  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.54/1.73  
% 3.54/1.74  tff(f_50, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.54/1.74  tff(f_48, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.54/1.74  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.54/1.74  tff(f_85, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 3.54/1.74  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 3.54/1.74  tff(f_77, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 3.54/1.74  tff(f_71, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 3.54/1.74  tff(c_16, plain, (![A_10]: (r1_xboole_0(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.54/1.74  tff(c_14, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.54/1.74  tff(c_235, plain, (![A_74, B_75, C_76]: (~r1_xboole_0(A_74, B_75) | ~r2_hidden(C_76, k3_xboole_0(A_74, B_75)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.54/1.74  tff(c_238, plain, (![A_9, C_76]: (~r1_xboole_0(A_9, k1_xboole_0) | ~r2_hidden(C_76, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_235])).
% 3.54/1.74  tff(c_240, plain, (![C_76]: (~r2_hidden(C_76, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_238])).
% 3.54/1.74  tff(c_40, plain, (k11_relat_1('#skF_10', '#skF_9')=k1_xboole_0 | ~r2_hidden('#skF_9', k1_relat_1('#skF_10'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.54/1.74  tff(c_55, plain, (~r2_hidden('#skF_9', k1_relat_1('#skF_10'))), inference(splitLeft, [status(thm)], [c_40])).
% 3.54/1.74  tff(c_46, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_10')) | k11_relat_1('#skF_10', '#skF_9')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.54/1.74  tff(c_63, plain, (k11_relat_1('#skF_10', '#skF_9')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_55, c_46])).
% 3.54/1.74  tff(c_38, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.54/1.74  tff(c_129, plain, (![A_61, B_62]: (r2_hidden('#skF_1'(A_61, B_62), B_62) | r2_hidden('#skF_2'(A_61, B_62), A_61) | B_62=A_61)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.54/1.74  tff(c_56, plain, (![A_42, B_43, C_44]: (~r1_xboole_0(A_42, B_43) | ~r2_hidden(C_44, k3_xboole_0(A_42, B_43)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.54/1.74  tff(c_59, plain, (![A_9, C_44]: (~r1_xboole_0(A_9, k1_xboole_0) | ~r2_hidden(C_44, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_56])).
% 3.54/1.74  tff(c_61, plain, (![C_44]: (~r2_hidden(C_44, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_59])).
% 3.54/1.74  tff(c_155, plain, (![B_62]: (r2_hidden('#skF_1'(k1_xboole_0, B_62), B_62) | k1_xboole_0=B_62)), inference(resolution, [status(thm)], [c_129, c_61])).
% 3.54/1.74  tff(c_108, plain, (![A_58, B_59, C_60]: (r2_hidden(k4_tarski(A_58, B_59), C_60) | ~r2_hidden(B_59, k11_relat_1(C_60, A_58)) | ~v1_relat_1(C_60))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.54/1.74  tff(c_24, plain, (![C_33, A_18, D_36]: (r2_hidden(C_33, k1_relat_1(A_18)) | ~r2_hidden(k4_tarski(C_33, D_36), A_18))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.54/1.74  tff(c_185, plain, (![A_69, C_70, B_71]: (r2_hidden(A_69, k1_relat_1(C_70)) | ~r2_hidden(B_71, k11_relat_1(C_70, A_69)) | ~v1_relat_1(C_70))), inference(resolution, [status(thm)], [c_108, c_24])).
% 3.54/1.74  tff(c_210, plain, (![A_72, C_73]: (r2_hidden(A_72, k1_relat_1(C_73)) | ~v1_relat_1(C_73) | k11_relat_1(C_73, A_72)=k1_xboole_0)), inference(resolution, [status(thm)], [c_155, c_185])).
% 3.54/1.74  tff(c_221, plain, (~v1_relat_1('#skF_10') | k11_relat_1('#skF_10', '#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_210, c_55])).
% 3.54/1.74  tff(c_226, plain, (k11_relat_1('#skF_10', '#skF_9')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_221])).
% 3.54/1.74  tff(c_228, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_226])).
% 3.54/1.74  tff(c_230, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_10'))), inference(splitRight, [status(thm)], [c_40])).
% 3.54/1.74  tff(c_229, plain, (k11_relat_1('#skF_10', '#skF_9')=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 3.54/1.74  tff(c_453, plain, (![C_112, A_113]: (r2_hidden(k4_tarski(C_112, '#skF_8'(A_113, k1_relat_1(A_113), C_112)), A_113) | ~r2_hidden(C_112, k1_relat_1(A_113)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.54/1.74  tff(c_36, plain, (![B_38, C_39, A_37]: (r2_hidden(B_38, k11_relat_1(C_39, A_37)) | ~r2_hidden(k4_tarski(A_37, B_38), C_39) | ~v1_relat_1(C_39))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.54/1.74  tff(c_2015, plain, (![A_195, C_196]: (r2_hidden('#skF_8'(A_195, k1_relat_1(A_195), C_196), k11_relat_1(A_195, C_196)) | ~v1_relat_1(A_195) | ~r2_hidden(C_196, k1_relat_1(A_195)))), inference(resolution, [status(thm)], [c_453, c_36])).
% 3.54/1.74  tff(c_2048, plain, (r2_hidden('#skF_8'('#skF_10', k1_relat_1('#skF_10'), '#skF_9'), k1_xboole_0) | ~v1_relat_1('#skF_10') | ~r2_hidden('#skF_9', k1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_229, c_2015])).
% 3.54/1.74  tff(c_2054, plain, (r2_hidden('#skF_8'('#skF_10', k1_relat_1('#skF_10'), '#skF_9'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_230, c_38, c_2048])).
% 3.54/1.74  tff(c_2056, plain, $false, inference(negUnitSimplification, [status(thm)], [c_240, c_2054])).
% 3.54/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.74  
% 3.54/1.74  Inference rules
% 3.54/1.74  ----------------------
% 3.54/1.74  #Ref     : 0
% 3.54/1.74  #Sup     : 416
% 3.54/1.74  #Fact    : 0
% 3.54/1.74  #Define  : 0
% 3.54/1.74  #Split   : 3
% 3.54/1.74  #Chain   : 0
% 3.54/1.74  #Close   : 0
% 3.54/1.74  
% 3.54/1.74  Ordering : KBO
% 3.54/1.74  
% 3.54/1.74  Simplification rules
% 3.54/1.74  ----------------------
% 3.54/1.74  #Subsume      : 138
% 3.54/1.74  #Demod        : 149
% 3.54/1.74  #Tautology    : 57
% 3.54/1.74  #SimpNegUnit  : 41
% 3.54/1.74  #BackRed      : 1
% 3.54/1.74  
% 3.54/1.74  #Partial instantiations: 0
% 3.54/1.74  #Strategies tried      : 1
% 3.54/1.74  
% 3.54/1.74  Timing (in seconds)
% 3.54/1.74  ----------------------
% 3.54/1.75  Preprocessing        : 0.33
% 3.54/1.75  Parsing              : 0.17
% 3.54/1.75  CNF conversion       : 0.03
% 3.54/1.75  Main loop            : 0.59
% 3.54/1.75  Inferencing          : 0.23
% 3.54/1.75  Reduction            : 0.15
% 3.54/1.75  Demodulation         : 0.10
% 3.54/1.75  BG Simplification    : 0.03
% 3.54/1.75  Subsumption          : 0.12
% 3.54/1.75  Abstraction          : 0.03
% 3.54/1.75  MUC search           : 0.00
% 3.54/1.75  Cooper               : 0.00
% 3.54/1.75  Total                : 0.95
% 3.54/1.75  Index Insertion      : 0.00
% 3.54/1.75  Index Deletion       : 0.00
% 3.54/1.75  Index Matching       : 0.00
% 3.54/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
