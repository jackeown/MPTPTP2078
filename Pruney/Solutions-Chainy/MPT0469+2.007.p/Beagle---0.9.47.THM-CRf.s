%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:52 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 111 expanded)
%              Number of leaves         :   32 (  50 expanded)
%              Depth                    :    9
%              Number of atoms          :   86 ( 169 expanded)
%              Number of equality atoms :   25 (  55 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_2 > #skF_5 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_92,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_58,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_56,axiom,(
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

tff(f_62,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_40,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_66,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_12,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_3'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_203,plain,(
    ! [C_70,A_71] :
      ( r2_hidden(k4_tarski(C_70,'#skF_7'(A_71,k1_relat_1(A_71),C_70)),A_71)
      | ~ r2_hidden(C_70,k1_relat_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_16,plain,(
    ! [A_13] : r1_xboole_0(A_13,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_14,plain,(
    ! [A_12] : k3_xboole_0(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_95,plain,(
    ! [A_49,B_50,C_51] :
      ( ~ r1_xboole_0(A_49,B_50)
      | ~ r2_hidden(C_51,k3_xboole_0(A_49,B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_106,plain,(
    ! [A_12,C_51] :
      ( ~ r1_xboole_0(A_12,k1_xboole_0)
      | ~ r2_hidden(C_51,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_95])).

tff(c_110,plain,(
    ! [C_51] : ~ r2_hidden(C_51,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_106])).

tff(c_225,plain,(
    ! [C_72] : ~ r2_hidden(C_72,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_203,c_110])).

tff(c_237,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_225])).

tff(c_247,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_237])).

tff(c_248,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_42,plain,(
    ! [A_38] :
      ( v1_relat_1(A_38)
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_46,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_42])).

tff(c_249,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_32,plain,(
    ! [A_34] :
      ( v1_relat_1(k4_relat_1(A_34))
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_36,plain,(
    ! [A_36] :
      ( k2_relat_1(k4_relat_1(A_36)) = k1_relat_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_278,plain,(
    ! [A_76] :
      ( ~ v1_xboole_0(k2_relat_1(A_76))
      | ~ v1_relat_1(A_76)
      | v1_xboole_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_362,plain,(
    ! [A_94] :
      ( ~ v1_xboole_0(k1_relat_1(A_94))
      | ~ v1_relat_1(k4_relat_1(A_94))
      | v1_xboole_0(k4_relat_1(A_94))
      | ~ v1_relat_1(A_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_278])).

tff(c_61,plain,(
    ! [A_44] :
      ( r2_hidden('#skF_3'(A_44),A_44)
      | k1_xboole_0 = A_44 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_65,plain,(
    ! [A_44] :
      ( ~ v1_xboole_0(A_44)
      | k1_xboole_0 = A_44 ) ),
    inference(resolution,[status(thm)],[c_61,c_2])).

tff(c_371,plain,(
    ! [A_95] :
      ( k4_relat_1(A_95) = k1_xboole_0
      | ~ v1_xboole_0(k1_relat_1(A_95))
      | ~ v1_relat_1(k4_relat_1(A_95))
      | ~ v1_relat_1(A_95) ) ),
    inference(resolution,[status(thm)],[c_362,c_65])).

tff(c_377,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_371])).

tff(c_379,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_6,c_377])).

tff(c_471,plain,(
    ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_379])).

tff(c_474,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_32,c_471])).

tff(c_478,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_474])).

tff(c_479,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_379])).

tff(c_38,plain,(
    ! [A_36] :
      ( k1_relat_1(k4_relat_1(A_36)) = k2_relat_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_487,plain,
    ( k2_relat_1(k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_479,c_38])).

tff(c_499,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_249,c_487])).

tff(c_501,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_248,c_499])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:50:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.38  
% 2.47/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.38  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_2 > #skF_5 > #skF_4
% 2.47/1.38  
% 2.47/1.38  %Foreground sorts:
% 2.47/1.38  
% 2.47/1.38  
% 2.47/1.38  %Background operators:
% 2.47/1.38  
% 2.47/1.38  
% 2.47/1.38  %Foreground operators:
% 2.47/1.38  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.47/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.47/1.38  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.47/1.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.47/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.47/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.47/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.47/1.38  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 2.47/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.47/1.38  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.47/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.47/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.47/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.47/1.38  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.47/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.47/1.38  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.47/1.38  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.47/1.38  
% 2.47/1.40  tff(f_92, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.47/1.40  tff(f_54, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.47/1.40  tff(f_70, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 2.47/1.40  tff(f_58, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.47/1.40  tff(f_56, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.47/1.40  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.47/1.40  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.47/1.40  tff(f_62, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.47/1.40  tff(f_74, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 2.47/1.40  tff(f_88, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 2.47/1.40  tff(f_82, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.47/1.40  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.47/1.40  tff(c_40, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.47/1.40  tff(c_66, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_40])).
% 2.47/1.40  tff(c_12, plain, (![A_10]: (r2_hidden('#skF_3'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.47/1.40  tff(c_203, plain, (![C_70, A_71]: (r2_hidden(k4_tarski(C_70, '#skF_7'(A_71, k1_relat_1(A_71), C_70)), A_71) | ~r2_hidden(C_70, k1_relat_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.47/1.40  tff(c_16, plain, (![A_13]: (r1_xboole_0(A_13, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.47/1.40  tff(c_14, plain, (![A_12]: (k3_xboole_0(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.47/1.40  tff(c_95, plain, (![A_49, B_50, C_51]: (~r1_xboole_0(A_49, B_50) | ~r2_hidden(C_51, k3_xboole_0(A_49, B_50)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.47/1.40  tff(c_106, plain, (![A_12, C_51]: (~r1_xboole_0(A_12, k1_xboole_0) | ~r2_hidden(C_51, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_95])).
% 2.47/1.40  tff(c_110, plain, (![C_51]: (~r2_hidden(C_51, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_106])).
% 2.47/1.40  tff(c_225, plain, (![C_72]: (~r2_hidden(C_72, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_203, c_110])).
% 2.47/1.40  tff(c_237, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_225])).
% 2.47/1.40  tff(c_247, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_237])).
% 2.47/1.40  tff(c_248, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 2.47/1.40  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.47/1.40  tff(c_42, plain, (![A_38]: (v1_relat_1(A_38) | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.47/1.40  tff(c_46, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_42])).
% 2.47/1.40  tff(c_249, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 2.47/1.40  tff(c_32, plain, (![A_34]: (v1_relat_1(k4_relat_1(A_34)) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.47/1.40  tff(c_36, plain, (![A_36]: (k2_relat_1(k4_relat_1(A_36))=k1_relat_1(A_36) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.47/1.40  tff(c_278, plain, (![A_76]: (~v1_xboole_0(k2_relat_1(A_76)) | ~v1_relat_1(A_76) | v1_xboole_0(A_76))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.47/1.40  tff(c_362, plain, (![A_94]: (~v1_xboole_0(k1_relat_1(A_94)) | ~v1_relat_1(k4_relat_1(A_94)) | v1_xboole_0(k4_relat_1(A_94)) | ~v1_relat_1(A_94))), inference(superposition, [status(thm), theory('equality')], [c_36, c_278])).
% 2.47/1.40  tff(c_61, plain, (![A_44]: (r2_hidden('#skF_3'(A_44), A_44) | k1_xboole_0=A_44)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.47/1.40  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.47/1.40  tff(c_65, plain, (![A_44]: (~v1_xboole_0(A_44) | k1_xboole_0=A_44)), inference(resolution, [status(thm)], [c_61, c_2])).
% 2.47/1.40  tff(c_371, plain, (![A_95]: (k4_relat_1(A_95)=k1_xboole_0 | ~v1_xboole_0(k1_relat_1(A_95)) | ~v1_relat_1(k4_relat_1(A_95)) | ~v1_relat_1(A_95))), inference(resolution, [status(thm)], [c_362, c_65])).
% 2.47/1.40  tff(c_377, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_249, c_371])).
% 2.47/1.40  tff(c_379, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_6, c_377])).
% 2.47/1.40  tff(c_471, plain, (~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_379])).
% 2.47/1.40  tff(c_474, plain, (~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_471])).
% 2.47/1.40  tff(c_478, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_474])).
% 2.47/1.40  tff(c_479, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_379])).
% 2.47/1.40  tff(c_38, plain, (![A_36]: (k1_relat_1(k4_relat_1(A_36))=k2_relat_1(A_36) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.47/1.40  tff(c_487, plain, (k2_relat_1(k1_xboole_0)=k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_479, c_38])).
% 2.47/1.40  tff(c_499, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_249, c_487])).
% 2.47/1.40  tff(c_501, plain, $false, inference(negUnitSimplification, [status(thm)], [c_248, c_499])).
% 2.47/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.40  
% 2.47/1.40  Inference rules
% 2.47/1.40  ----------------------
% 2.47/1.40  #Ref     : 0
% 2.47/1.40  #Sup     : 95
% 2.47/1.40  #Fact    : 0
% 2.47/1.40  #Define  : 0
% 2.47/1.40  #Split   : 2
% 2.47/1.40  #Chain   : 0
% 2.47/1.40  #Close   : 0
% 2.47/1.40  
% 2.47/1.40  Ordering : KBO
% 2.47/1.40  
% 2.47/1.40  Simplification rules
% 2.47/1.40  ----------------------
% 2.47/1.40  #Subsume      : 12
% 2.47/1.40  #Demod        : 37
% 2.47/1.40  #Tautology    : 39
% 2.47/1.40  #SimpNegUnit  : 5
% 2.47/1.40  #BackRed      : 0
% 2.47/1.40  
% 2.47/1.40  #Partial instantiations: 0
% 2.47/1.40  #Strategies tried      : 1
% 2.47/1.40  
% 2.47/1.40  Timing (in seconds)
% 2.47/1.40  ----------------------
% 2.47/1.40  Preprocessing        : 0.29
% 2.47/1.40  Parsing              : 0.15
% 2.47/1.40  CNF conversion       : 0.02
% 2.47/1.40  Main loop            : 0.25
% 2.47/1.40  Inferencing          : 0.11
% 2.47/1.40  Reduction            : 0.06
% 2.47/1.40  Demodulation         : 0.04
% 2.47/1.40  BG Simplification    : 0.01
% 2.47/1.40  Subsumption          : 0.04
% 2.47/1.40  Abstraction          : 0.01
% 2.47/1.40  MUC search           : 0.00
% 2.47/1.40  Cooper               : 0.00
% 2.47/1.40  Total                : 0.57
% 2.47/1.40  Index Insertion      : 0.00
% 2.47/1.40  Index Deletion       : 0.00
% 2.47/1.40  Index Matching       : 0.00
% 2.47/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
