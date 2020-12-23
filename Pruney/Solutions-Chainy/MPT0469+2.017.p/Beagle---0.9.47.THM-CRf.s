%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:53 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 109 expanded)
%              Number of leaves         :   29 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :   80 ( 168 expanded)
%              Number of equality atoms :   25 (  55 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_82,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_48,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_46,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_36,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_57,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_189,plain,(
    ! [A_70,B_71] :
      ( r2_hidden(k4_tarski('#skF_2'(A_70,B_71),'#skF_3'(A_70,B_71)),A_70)
      | r2_hidden('#skF_4'(A_70,B_71),B_71)
      | k1_relat_1(A_70) = B_71 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_12,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_80,plain,(
    ! [A_40,B_41,C_42] :
      ( ~ r1_xboole_0(A_40,B_41)
      | ~ r2_hidden(C_42,k3_xboole_0(A_40,B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_83,plain,(
    ! [A_7,C_42] :
      ( ~ r1_xboole_0(A_7,k1_xboole_0)
      | ~ r2_hidden(C_42,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_80])).

tff(c_85,plain,(
    ! [C_42] : ~ r2_hidden(C_42,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_83])).

tff(c_244,plain,(
    ! [B_72] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_72),B_72)
      | k1_relat_1(k1_xboole_0) = B_72 ) ),
    inference(resolution,[status(thm)],[c_189,c_85])).

tff(c_280,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_244,c_85])).

tff(c_297,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_280])).

tff(c_298,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_44,plain,(
    ! [A_34] :
      ( v1_relat_1(A_34)
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_48,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_44])).

tff(c_299,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_28,plain,(
    ! [A_29] :
      ( v1_relat_1(k4_relat_1(A_29))
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_305,plain,(
    ! [A_74] :
      ( k2_relat_1(k4_relat_1(A_74)) = k1_relat_1(A_74)
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_30,plain,(
    ! [A_30] :
      ( ~ v1_xboole_0(k2_relat_1(A_30))
      | ~ v1_relat_1(A_30)
      | v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_344,plain,(
    ! [A_85] :
      ( ~ v1_xboole_0(k1_relat_1(A_85))
      | ~ v1_relat_1(k4_relat_1(A_85))
      | v1_xboole_0(k4_relat_1(A_85))
      | ~ v1_relat_1(A_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_30])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_353,plain,(
    ! [A_86] :
      ( k4_relat_1(A_86) = k1_xboole_0
      | ~ v1_xboole_0(k1_relat_1(A_86))
      | ~ v1_relat_1(k4_relat_1(A_86))
      | ~ v1_relat_1(A_86) ) ),
    inference(resolution,[status(thm)],[c_344,c_4])).

tff(c_359,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_353])).

tff(c_361,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2,c_359])).

tff(c_362,plain,(
    ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_361])).

tff(c_365,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_28,c_362])).

tff(c_369,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_365])).

tff(c_370,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_361])).

tff(c_34,plain,(
    ! [A_31] :
      ( k1_relat_1(k4_relat_1(A_31)) = k2_relat_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_378,plain,
    ( k2_relat_1(k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_34])).

tff(c_390,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_299,c_378])).

tff(c_392,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_298,c_390])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:33:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.30  
% 2.09/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.30  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 2.09/1.30  
% 2.09/1.30  %Foreground sorts:
% 2.09/1.30  
% 2.09/1.30  
% 2.09/1.30  %Background operators:
% 2.09/1.30  
% 2.09/1.30  
% 2.09/1.30  %Foreground operators:
% 2.09/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.09/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.09/1.30  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.09/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.09/1.30  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.09/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.09/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.09/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.09/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.09/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.09/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.09/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.09/1.30  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.09/1.30  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.09/1.30  
% 2.09/1.31  tff(f_82, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.09/1.31  tff(f_60, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 2.09/1.31  tff(f_48, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.09/1.31  tff(f_46, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.09/1.31  tff(f_44, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.09/1.31  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.09/1.31  tff(f_52, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.09/1.31  tff(f_64, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 2.09/1.31  tff(f_78, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 2.09/1.31  tff(f_72, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.09/1.31  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.09/1.31  tff(c_36, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.09/1.31  tff(c_57, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36])).
% 2.09/1.31  tff(c_189, plain, (![A_70, B_71]: (r2_hidden(k4_tarski('#skF_2'(A_70, B_71), '#skF_3'(A_70, B_71)), A_70) | r2_hidden('#skF_4'(A_70, B_71), B_71) | k1_relat_1(A_70)=B_71)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.09/1.31  tff(c_12, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.09/1.31  tff(c_10, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.09/1.31  tff(c_80, plain, (![A_40, B_41, C_42]: (~r1_xboole_0(A_40, B_41) | ~r2_hidden(C_42, k3_xboole_0(A_40, B_41)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.09/1.31  tff(c_83, plain, (![A_7, C_42]: (~r1_xboole_0(A_7, k1_xboole_0) | ~r2_hidden(C_42, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_80])).
% 2.09/1.31  tff(c_85, plain, (![C_42]: (~r2_hidden(C_42, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_83])).
% 2.09/1.31  tff(c_244, plain, (![B_72]: (r2_hidden('#skF_4'(k1_xboole_0, B_72), B_72) | k1_relat_1(k1_xboole_0)=B_72)), inference(resolution, [status(thm)], [c_189, c_85])).
% 2.09/1.31  tff(c_280, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_244, c_85])).
% 2.09/1.31  tff(c_297, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_280])).
% 2.09/1.31  tff(c_298, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 2.09/1.31  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.09/1.31  tff(c_44, plain, (![A_34]: (v1_relat_1(A_34) | ~v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.09/1.31  tff(c_48, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_44])).
% 2.09/1.31  tff(c_299, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 2.09/1.31  tff(c_28, plain, (![A_29]: (v1_relat_1(k4_relat_1(A_29)) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.09/1.31  tff(c_305, plain, (![A_74]: (k2_relat_1(k4_relat_1(A_74))=k1_relat_1(A_74) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.09/1.31  tff(c_30, plain, (![A_30]: (~v1_xboole_0(k2_relat_1(A_30)) | ~v1_relat_1(A_30) | v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.09/1.31  tff(c_344, plain, (![A_85]: (~v1_xboole_0(k1_relat_1(A_85)) | ~v1_relat_1(k4_relat_1(A_85)) | v1_xboole_0(k4_relat_1(A_85)) | ~v1_relat_1(A_85))), inference(superposition, [status(thm), theory('equality')], [c_305, c_30])).
% 2.09/1.31  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.09/1.31  tff(c_353, plain, (![A_86]: (k4_relat_1(A_86)=k1_xboole_0 | ~v1_xboole_0(k1_relat_1(A_86)) | ~v1_relat_1(k4_relat_1(A_86)) | ~v1_relat_1(A_86))), inference(resolution, [status(thm)], [c_344, c_4])).
% 2.09/1.31  tff(c_359, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_299, c_353])).
% 2.09/1.31  tff(c_361, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2, c_359])).
% 2.09/1.31  tff(c_362, plain, (~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_361])).
% 2.09/1.31  tff(c_365, plain, (~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_362])).
% 2.09/1.31  tff(c_369, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_365])).
% 2.09/1.31  tff(c_370, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_361])).
% 2.09/1.31  tff(c_34, plain, (![A_31]: (k1_relat_1(k4_relat_1(A_31))=k2_relat_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.09/1.31  tff(c_378, plain, (k2_relat_1(k1_xboole_0)=k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_370, c_34])).
% 2.09/1.31  tff(c_390, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_299, c_378])).
% 2.09/1.31  tff(c_392, plain, $false, inference(negUnitSimplification, [status(thm)], [c_298, c_390])).
% 2.09/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.31  
% 2.09/1.31  Inference rules
% 2.09/1.31  ----------------------
% 2.09/1.31  #Ref     : 0
% 2.09/1.31  #Sup     : 71
% 2.09/1.31  #Fact    : 0
% 2.09/1.31  #Define  : 0
% 2.09/1.31  #Split   : 2
% 2.09/1.31  #Chain   : 0
% 2.09/1.31  #Close   : 0
% 2.09/1.31  
% 2.09/1.31  Ordering : KBO
% 2.09/1.31  
% 2.09/1.31  Simplification rules
% 2.09/1.31  ----------------------
% 2.09/1.31  #Subsume      : 4
% 2.09/1.31  #Demod        : 17
% 2.09/1.31  #Tautology    : 21
% 2.09/1.31  #SimpNegUnit  : 4
% 2.09/1.31  #BackRed      : 0
% 2.09/1.31  
% 2.09/1.31  #Partial instantiations: 0
% 2.09/1.31  #Strategies tried      : 1
% 2.09/1.31  
% 2.09/1.31  Timing (in seconds)
% 2.09/1.31  ----------------------
% 2.09/1.31  Preprocessing        : 0.30
% 2.09/1.31  Parsing              : 0.16
% 2.09/1.31  CNF conversion       : 0.02
% 2.09/1.31  Main loop            : 0.24
% 2.09/1.31  Inferencing          : 0.10
% 2.09/1.31  Reduction            : 0.06
% 2.09/1.31  Demodulation         : 0.04
% 2.09/1.31  BG Simplification    : 0.01
% 2.09/1.31  Subsumption          : 0.05
% 2.09/1.31  Abstraction          : 0.01
% 2.09/1.31  MUC search           : 0.00
% 2.09/1.31  Cooper               : 0.00
% 2.09/1.31  Total                : 0.57
% 2.09/1.32  Index Insertion      : 0.00
% 2.09/1.32  Index Deletion       : 0.00
% 2.09/1.32  Index Matching       : 0.00
% 2.09/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
