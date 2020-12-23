%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:57 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   55 (  72 expanded)
%              Number of leaves         :   29 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   57 (  88 expanded)
%              Number of equality atoms :   14 (  25 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_10 > #skF_8 > #skF_9 > #skF_3 > #skF_7 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

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

tff(f_82,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_51,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k1_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_32,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_42,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_3'(A_10),A_10)
      | v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_10,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_45,plain,(
    ! [A_57,B_58,C_59] :
      ( ~ r1_xboole_0(A_57,B_58)
      | ~ r2_hidden(C_59,k3_xboole_0(A_57,B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_56,plain,(
    ! [A_8,C_59] :
      ( ~ r1_xboole_0(A_8,k1_xboole_0)
      | ~ r2_hidden(C_59,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_45])).

tff(c_61,plain,(
    ! [C_60] : ~ r2_hidden(C_60,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_56])).

tff(c_72,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_61])).

tff(c_30,plain,(
    ! [A_47,B_48] :
      ( r2_hidden('#skF_10'(A_47,B_48),k2_relat_1(B_48))
      | ~ r2_hidden(A_47,k1_relat_1(B_48))
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_98,plain,(
    ! [A_74,C_75] :
      ( r2_hidden(k4_tarski('#skF_9'(A_74,k2_relat_1(A_74),C_75),C_75),A_74)
      | ~ r2_hidden(C_75,k2_relat_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_60,plain,(
    ! [C_59] : ~ r2_hidden(C_59,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_56])).

tff(c_113,plain,(
    ! [C_76] : ~ r2_hidden(C_76,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_98,c_60])).

tff(c_121,plain,(
    ! [A_47] :
      ( ~ r2_hidden(A_47,k1_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_30,c_113])).

tff(c_166,plain,(
    ! [A_79] : ~ r2_hidden(A_79,k1_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_121])).

tff(c_174,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_166])).

tff(c_183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_174])).

tff(c_184,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_268,plain,(
    ! [A_108,C_109] :
      ( r2_hidden(k4_tarski('#skF_9'(A_108,k2_relat_1(A_108),C_109),C_109),A_108)
      | ~ r2_hidden(C_109,k2_relat_1(A_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_192,plain,(
    ! [A_84,B_85,C_86] :
      ( ~ r1_xboole_0(A_84,B_85)
      | ~ r2_hidden(C_86,k3_xboole_0(A_84,B_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_203,plain,(
    ! [A_8,C_86] :
      ( ~ r1_xboole_0(A_8,k1_xboole_0)
      | ~ r2_hidden(C_86,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_192])).

tff(c_207,plain,(
    ! [C_86] : ~ r2_hidden(C_86,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_203])).

tff(c_284,plain,(
    ! [C_113] : ~ r2_hidden(C_113,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_268,c_207])).

tff(c_296,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_284])).

tff(c_308,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_184,c_296])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:48:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/2.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/2.19  
% 2.33/2.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/2.20  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_10 > #skF_8 > #skF_9 > #skF_3 > #skF_7 > #skF_1 > #skF_5 > #skF_4
% 2.33/2.20  
% 2.33/2.20  %Foreground sorts:
% 2.33/2.20  
% 2.33/2.20  
% 2.33/2.20  %Background operators:
% 2.33/2.20  
% 2.33/2.20  
% 2.33/2.20  %Foreground operators:
% 2.33/2.20  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.33/2.20  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.33/2.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/2.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.33/2.20  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.33/2.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.33/2.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.33/2.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.33/2.20  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 2.33/2.20  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 2.33/2.20  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 2.33/2.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/2.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.33/2.20  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.33/2.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/2.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.33/2.20  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.33/2.20  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.33/2.20  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.33/2.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.33/2.20  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.33/2.20  
% 2.47/2.23  tff(f_82, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.47/2.23  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.47/2.23  tff(f_61, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.47/2.23  tff(f_51, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.47/2.23  tff(f_49, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.47/2.23  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.47/2.23  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k1_relat_1(B)) & (![C]: ~r2_hidden(C, k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_relat_1)).
% 2.47/2.23  tff(f_69, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 2.47/2.23  tff(c_32, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.47/2.23  tff(c_42, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32])).
% 2.47/2.23  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.47/2.23  tff(c_16, plain, (![A_10]: (r2_hidden('#skF_3'(A_10), A_10) | v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.47/2.23  tff(c_10, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.47/2.23  tff(c_8, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.47/2.23  tff(c_45, plain, (![A_57, B_58, C_59]: (~r1_xboole_0(A_57, B_58) | ~r2_hidden(C_59, k3_xboole_0(A_57, B_58)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.47/2.23  tff(c_56, plain, (![A_8, C_59]: (~r1_xboole_0(A_8, k1_xboole_0) | ~r2_hidden(C_59, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_45])).
% 2.47/2.23  tff(c_61, plain, (![C_60]: (~r2_hidden(C_60, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_56])).
% 2.47/2.23  tff(c_72, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_61])).
% 2.47/2.23  tff(c_30, plain, (![A_47, B_48]: (r2_hidden('#skF_10'(A_47, B_48), k2_relat_1(B_48)) | ~r2_hidden(A_47, k1_relat_1(B_48)) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.47/2.23  tff(c_98, plain, (![A_74, C_75]: (r2_hidden(k4_tarski('#skF_9'(A_74, k2_relat_1(A_74), C_75), C_75), A_74) | ~r2_hidden(C_75, k2_relat_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.47/2.23  tff(c_60, plain, (![C_59]: (~r2_hidden(C_59, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_56])).
% 2.47/2.23  tff(c_113, plain, (![C_76]: (~r2_hidden(C_76, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_98, c_60])).
% 2.47/2.23  tff(c_121, plain, (![A_47]: (~r2_hidden(A_47, k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_30, c_113])).
% 2.47/2.23  tff(c_166, plain, (![A_79]: (~r2_hidden(A_79, k1_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_121])).
% 2.47/2.23  tff(c_174, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_166])).
% 2.47/2.23  tff(c_183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_174])).
% 2.47/2.23  tff(c_184, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 2.47/2.23  tff(c_268, plain, (![A_108, C_109]: (r2_hidden(k4_tarski('#skF_9'(A_108, k2_relat_1(A_108), C_109), C_109), A_108) | ~r2_hidden(C_109, k2_relat_1(A_108)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.47/2.23  tff(c_192, plain, (![A_84, B_85, C_86]: (~r1_xboole_0(A_84, B_85) | ~r2_hidden(C_86, k3_xboole_0(A_84, B_85)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.47/2.23  tff(c_203, plain, (![A_8, C_86]: (~r1_xboole_0(A_8, k1_xboole_0) | ~r2_hidden(C_86, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_192])).
% 2.47/2.23  tff(c_207, plain, (![C_86]: (~r2_hidden(C_86, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_203])).
% 2.47/2.23  tff(c_284, plain, (![C_113]: (~r2_hidden(C_113, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_268, c_207])).
% 2.47/2.23  tff(c_296, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_284])).
% 2.47/2.23  tff(c_308, plain, $false, inference(negUnitSimplification, [status(thm)], [c_184, c_296])).
% 2.47/2.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/2.23  
% 2.47/2.23  Inference rules
% 2.47/2.23  ----------------------
% 2.47/2.23  #Ref     : 1
% 2.47/2.23  #Sup     : 52
% 2.47/2.23  #Fact    : 0
% 2.47/2.23  #Define  : 0
% 2.47/2.23  #Split   : 1
% 2.47/2.23  #Chain   : 0
% 2.47/2.23  #Close   : 0
% 2.47/2.23  
% 2.47/2.23  Ordering : KBO
% 2.47/2.23  
% 2.47/2.23  Simplification rules
% 2.47/2.23  ----------------------
% 2.47/2.23  #Subsume      : 3
% 2.47/2.23  #Demod        : 18
% 2.47/2.23  #Tautology    : 24
% 2.47/2.23  #SimpNegUnit  : 6
% 2.47/2.23  #BackRed      : 1
% 2.47/2.23  
% 2.47/2.23  #Partial instantiations: 0
% 2.47/2.23  #Strategies tried      : 1
% 2.47/2.23  
% 2.47/2.23  Timing (in seconds)
% 2.47/2.23  ----------------------
% 2.47/2.23  Preprocessing        : 0.60
% 2.47/2.23  Parsing              : 0.33
% 2.47/2.23  CNF conversion       : 0.07
% 2.47/2.23  Main loop            : 0.53
% 2.47/2.23  Inferencing          : 0.23
% 2.47/2.23  Reduction            : 0.14
% 2.47/2.23  Demodulation         : 0.09
% 2.47/2.23  BG Simplification    : 0.03
% 2.47/2.24  Subsumption          : 0.07
% 2.47/2.24  Abstraction          : 0.02
% 2.47/2.24  MUC search           : 0.00
% 2.47/2.24  Cooper               : 0.00
% 2.47/2.24  Total                : 1.19
% 2.47/2.24  Index Insertion      : 0.00
% 2.47/2.24  Index Deletion       : 0.00
% 2.47/2.24  Index Matching       : 0.00
% 2.47/2.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
