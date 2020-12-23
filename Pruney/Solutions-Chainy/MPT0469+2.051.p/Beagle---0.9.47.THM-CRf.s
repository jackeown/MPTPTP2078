%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:58 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :   54 (  91 expanded)
%              Number of leaves         :   25 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :   58 ( 120 expanded)
%              Number of equality atoms :   17 (  34 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_5 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_56,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_34,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_56,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_496,plain,(
    ! [C_74,A_75] :
      ( r2_hidden(k4_tarski(C_74,'#skF_5'(A_75,k1_relat_1(A_75),C_74)),A_75)
      | ~ r2_hidden(C_74,k1_relat_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_35,plain,(
    ! [A_44] :
      ( k1_xboole_0 = A_44
      | ~ v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_39,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_35])).

tff(c_40,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_6])).

tff(c_59,plain,(
    ! [A_54,C_55] :
      ( r2_hidden(k4_tarski('#skF_9'(A_54,k2_relat_1(A_54),C_55),C_55),A_54)
      | ~ r2_hidden(C_55,k2_relat_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,(
    ! [A_56,C_57] :
      ( ~ v1_xboole_0(A_56)
      | ~ r2_hidden(C_57,k2_relat_1(A_56)) ) ),
    inference(resolution,[status(thm)],[c_59,c_2])).

tff(c_83,plain,(
    ! [A_58] :
      ( ~ v1_xboole_0(A_58)
      | v1_xboole_0(k2_relat_1(A_58)) ) ),
    inference(resolution,[status(thm)],[c_4,c_72])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_88,plain,(
    ! [A_59] :
      ( k2_relat_1(A_59) = k1_xboole_0
      | ~ v1_xboole_0(A_59) ) ),
    inference(resolution,[status(thm)],[c_83,c_8])).

tff(c_96,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_88])).

tff(c_71,plain,(
    ! [A_54,C_55] :
      ( ~ v1_xboole_0(A_54)
      | ~ r2_hidden(C_55,k2_relat_1(A_54)) ) ),
    inference(resolution,[status(thm)],[c_59,c_2])).

tff(c_103,plain,(
    ! [C_55] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_55,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_71])).

tff(c_112,plain,(
    ! [C_55] : ~ r2_hidden(C_55,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_103])).

tff(c_529,plain,(
    ! [C_76] : ~ r2_hidden(C_76,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_496,c_112])).

tff(c_544,plain,(
    v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_4,c_529])).

tff(c_550,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_544,c_8])).

tff(c_555,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_550])).

tff(c_556,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_565,plain,(
    ! [A_85,C_86] :
      ( r2_hidden(k4_tarski('#skF_9'(A_85,k2_relat_1(A_85),C_86),C_86),A_85)
      | ~ r2_hidden(C_86,k2_relat_1(A_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_578,plain,(
    ! [A_87,C_88] :
      ( ~ v1_xboole_0(A_87)
      | ~ r2_hidden(C_88,k2_relat_1(A_87)) ) ),
    inference(resolution,[status(thm)],[c_565,c_2])).

tff(c_611,plain,(
    ! [A_91] :
      ( ~ v1_xboole_0(A_91)
      | v1_xboole_0(k2_relat_1(A_91)) ) ),
    inference(resolution,[status(thm)],[c_4,c_578])).

tff(c_616,plain,(
    ! [A_92] :
      ( k2_relat_1(A_92) = k1_xboole_0
      | ~ v1_xboole_0(A_92) ) ),
    inference(resolution,[status(thm)],[c_611,c_8])).

tff(c_622,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_616])).

tff(c_627,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_556,c_622])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:30:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.37  
% 2.10/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.37  %$ r2_hidden > v1_xboole_0 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_5 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_4
% 2.39/1.37  
% 2.39/1.37  %Foreground sorts:
% 2.39/1.37  
% 2.39/1.37  
% 2.39/1.37  %Background operators:
% 2.39/1.37  
% 2.39/1.37  
% 2.39/1.37  %Foreground operators:
% 2.39/1.37  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.39/1.37  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 2.39/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.39/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.39/1.37  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.39/1.37  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.39/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.39/1.37  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.39/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.39/1.37  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.39/1.37  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 2.39/1.37  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 2.39/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.39/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.39/1.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.39/1.37  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.39/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.39/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.39/1.37  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.39/1.37  
% 2.39/1.38  tff(f_56, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.39/1.38  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.39/1.38  tff(f_44, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 2.39/1.38  tff(f_32, axiom, v1_xboole_0(o_0_0_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_o_0_0_xboole_0)).
% 2.39/1.38  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.39/1.38  tff(f_52, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 2.39/1.38  tff(c_34, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.39/1.38  tff(c_56, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_34])).
% 2.39/1.38  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.39/1.38  tff(c_496, plain, (![C_74, A_75]: (r2_hidden(k4_tarski(C_74, '#skF_5'(A_75, k1_relat_1(A_75), C_74)), A_75) | ~r2_hidden(C_74, k1_relat_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.39/1.38  tff(c_6, plain, (v1_xboole_0(o_0_0_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.39/1.38  tff(c_35, plain, (![A_44]: (k1_xboole_0=A_44 | ~v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.39/1.38  tff(c_39, plain, (o_0_0_xboole_0=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_35])).
% 2.39/1.38  tff(c_40, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_39, c_6])).
% 2.39/1.38  tff(c_59, plain, (![A_54, C_55]: (r2_hidden(k4_tarski('#skF_9'(A_54, k2_relat_1(A_54), C_55), C_55), A_54) | ~r2_hidden(C_55, k2_relat_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.39/1.38  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.39/1.38  tff(c_72, plain, (![A_56, C_57]: (~v1_xboole_0(A_56) | ~r2_hidden(C_57, k2_relat_1(A_56)))), inference(resolution, [status(thm)], [c_59, c_2])).
% 2.39/1.38  tff(c_83, plain, (![A_58]: (~v1_xboole_0(A_58) | v1_xboole_0(k2_relat_1(A_58)))), inference(resolution, [status(thm)], [c_4, c_72])).
% 2.39/1.38  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.39/1.38  tff(c_88, plain, (![A_59]: (k2_relat_1(A_59)=k1_xboole_0 | ~v1_xboole_0(A_59))), inference(resolution, [status(thm)], [c_83, c_8])).
% 2.39/1.38  tff(c_96, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_88])).
% 2.39/1.38  tff(c_71, plain, (![A_54, C_55]: (~v1_xboole_0(A_54) | ~r2_hidden(C_55, k2_relat_1(A_54)))), inference(resolution, [status(thm)], [c_59, c_2])).
% 2.39/1.38  tff(c_103, plain, (![C_55]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(C_55, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_96, c_71])).
% 2.39/1.38  tff(c_112, plain, (![C_55]: (~r2_hidden(C_55, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_103])).
% 2.39/1.38  tff(c_529, plain, (![C_76]: (~r2_hidden(C_76, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_496, c_112])).
% 2.39/1.38  tff(c_544, plain, (v1_xboole_0(k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_529])).
% 2.39/1.38  tff(c_550, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_544, c_8])).
% 2.39/1.38  tff(c_555, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_550])).
% 2.39/1.38  tff(c_556, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_34])).
% 2.39/1.38  tff(c_565, plain, (![A_85, C_86]: (r2_hidden(k4_tarski('#skF_9'(A_85, k2_relat_1(A_85), C_86), C_86), A_85) | ~r2_hidden(C_86, k2_relat_1(A_85)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.39/1.38  tff(c_578, plain, (![A_87, C_88]: (~v1_xboole_0(A_87) | ~r2_hidden(C_88, k2_relat_1(A_87)))), inference(resolution, [status(thm)], [c_565, c_2])).
% 2.39/1.38  tff(c_611, plain, (![A_91]: (~v1_xboole_0(A_91) | v1_xboole_0(k2_relat_1(A_91)))), inference(resolution, [status(thm)], [c_4, c_578])).
% 2.39/1.38  tff(c_616, plain, (![A_92]: (k2_relat_1(A_92)=k1_xboole_0 | ~v1_xboole_0(A_92))), inference(resolution, [status(thm)], [c_611, c_8])).
% 2.39/1.38  tff(c_622, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_616])).
% 2.39/1.38  tff(c_627, plain, $false, inference(negUnitSimplification, [status(thm)], [c_556, c_622])).
% 2.39/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.38  
% 2.39/1.38  Inference rules
% 2.39/1.38  ----------------------
% 2.39/1.38  #Ref     : 0
% 2.39/1.38  #Sup     : 137
% 2.39/1.38  #Fact    : 0
% 2.39/1.38  #Define  : 0
% 2.39/1.38  #Split   : 1
% 2.39/1.38  #Chain   : 0
% 2.39/1.38  #Close   : 0
% 2.39/1.38  
% 2.39/1.39  Ordering : KBO
% 2.39/1.39  
% 2.39/1.39  Simplification rules
% 2.39/1.39  ----------------------
% 2.39/1.39  #Subsume      : 23
% 2.39/1.39  #Demod        : 111
% 2.39/1.39  #Tautology    : 73
% 2.39/1.39  #SimpNegUnit  : 2
% 2.39/1.39  #BackRed      : 1
% 2.39/1.39  
% 2.39/1.39  #Partial instantiations: 0
% 2.39/1.39  #Strategies tried      : 1
% 2.39/1.39  
% 2.39/1.39  Timing (in seconds)
% 2.39/1.39  ----------------------
% 2.39/1.39  Preprocessing        : 0.30
% 2.39/1.39  Parsing              : 0.15
% 2.39/1.39  CNF conversion       : 0.03
% 2.39/1.39  Main loop            : 0.26
% 2.39/1.39  Inferencing          : 0.10
% 2.39/1.39  Reduction            : 0.07
% 2.39/1.39  Demodulation         : 0.05
% 2.39/1.39  BG Simplification    : 0.02
% 2.39/1.39  Subsumption          : 0.05
% 2.39/1.39  Abstraction          : 0.01
% 2.39/1.39  MUC search           : 0.00
% 2.39/1.39  Cooper               : 0.00
% 2.39/1.39  Total                : 0.59
% 2.39/1.39  Index Insertion      : 0.00
% 2.39/1.39  Index Deletion       : 0.00
% 2.39/1.39  Index Matching       : 0.00
% 2.39/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
