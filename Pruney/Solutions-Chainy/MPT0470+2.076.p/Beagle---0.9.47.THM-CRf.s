%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:11 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   62 (  95 expanded)
%              Number of leaves         :   24 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :  110 ( 165 expanded)
%              Number of equality atoms :   29 (  45 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k4_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_36,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_79,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_28,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_65,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_30,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_39,plain,(
    ! [A_16] :
      ( v1_relat_1(A_16)
      | ~ v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_43,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_39])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k5_relat_1(A_6,B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_160,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_35,B_36)),k1_relat_1(A_35))
      | ~ v1_relat_1(B_36)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_166,plain,(
    ! [B_36] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_36)),k1_xboole_0)
      | ~ v1_relat_1(B_36)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_160])).

tff(c_259,plain,(
    ! [B_38] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_38)),k1_xboole_0)
      | ~ v1_relat_1(B_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_166])).

tff(c_8,plain,(
    ! [A_2,B_3] :
      ( k4_xboole_0(A_2,B_3) = k1_xboole_0
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_262,plain,(
    ! [B_38] :
      ( k4_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,B_38)),k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_38) ) ),
    inference(resolution,[status(thm)],[c_259,c_8])).

tff(c_270,plain,(
    ! [B_39] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_39)) = k1_xboole_0
      | ~ v1_relat_1(B_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_262])).

tff(c_16,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(k1_relat_1(A_8))
      | ~ v1_relat_1(A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_285,plain,(
    ! [B_39] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_39))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_39))
      | ~ v1_relat_1(B_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_16])).

tff(c_301,plain,(
    ! [B_40] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_40))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_40))
      | ~ v1_relat_1(B_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_285])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_315,plain,(
    ! [B_41] :
      ( k5_relat_1(k1_xboole_0,B_41) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_41))
      | ~ v1_relat_1(B_41) ) ),
    inference(resolution,[status(thm)],[c_301,c_4])).

tff(c_322,plain,(
    ! [B_7] :
      ( k5_relat_1(k1_xboole_0,B_7) = k1_xboole_0
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_315])).

tff(c_361,plain,(
    ! [B_44] :
      ( k5_relat_1(k1_xboole_0,B_44) = k1_xboole_0
      | ~ v1_relat_1(B_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_322])).

tff(c_370,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_361])).

tff(c_377,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_370])).

tff(c_378,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_24,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_422,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_54,B_55)),k2_relat_1(B_55))
      | ~ v1_relat_1(B_55)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_456,plain,(
    ! [A_57,B_58] :
      ( k4_xboole_0(k2_relat_1(k5_relat_1(A_57,B_58)),k2_relat_1(B_58)) = k1_xboole_0
      | ~ v1_relat_1(B_58)
      | ~ v1_relat_1(A_57) ) ),
    inference(resolution,[status(thm)],[c_422,c_8])).

tff(c_468,plain,(
    ! [A_57] :
      ( k4_xboole_0(k2_relat_1(k5_relat_1(A_57,k1_xboole_0)),k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_456])).

tff(c_506,plain,(
    ! [A_60] :
      ( k2_relat_1(k5_relat_1(A_60,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_10,c_468])).

tff(c_18,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(k2_relat_1(A_9))
      | ~ v1_relat_1(A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_524,plain,(
    ! [A_60] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_60,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_60,k1_xboole_0))
      | ~ v1_relat_1(A_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_506,c_18])).

tff(c_561,plain,(
    ! [A_63] :
      ( ~ v1_relat_1(k5_relat_1(A_63,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_63,k1_xboole_0))
      | ~ v1_relat_1(A_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_524])).

tff(c_684,plain,(
    ! [A_68] :
      ( k5_relat_1(A_68,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_68,k1_xboole_0))
      | ~ v1_relat_1(A_68) ) ),
    inference(resolution,[status(thm)],[c_561,c_4])).

tff(c_691,plain,(
    ! [A_6] :
      ( k5_relat_1(A_6,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_6) ) ),
    inference(resolution,[status(thm)],[c_14,c_684])).

tff(c_697,plain,(
    ! [A_69] :
      ( k5_relat_1(A_69,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_691])).

tff(c_706,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_697])).

tff(c_713,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_378,c_706])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:37:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.32  
% 2.47/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.33  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k4_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.47/1.33  
% 2.47/1.33  %Foreground sorts:
% 2.47/1.33  
% 2.47/1.33  
% 2.47/1.33  %Background operators:
% 2.47/1.33  
% 2.47/1.33  
% 2.47/1.33  %Foreground operators:
% 2.47/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.47/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.47/1.33  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.47/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.47/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.47/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.47/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.47/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.47/1.33  
% 2.47/1.34  tff(f_86, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 2.47/1.34  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.47/1.34  tff(f_40, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.47/1.34  tff(f_46, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.47/1.34  tff(f_36, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.47/1.34  tff(f_79, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.47/1.34  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 2.47/1.34  tff(f_34, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.47/1.34  tff(f_54, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.47/1.34  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.47/1.34  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 2.47/1.34  tff(f_62, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.47/1.34  tff(c_28, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.47/1.34  tff(c_65, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_28])).
% 2.47/1.34  tff(c_30, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.47/1.34  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.47/1.34  tff(c_39, plain, (![A_16]: (v1_relat_1(A_16) | ~v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.47/1.34  tff(c_43, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_39])).
% 2.47/1.34  tff(c_14, plain, (![A_6, B_7]: (v1_relat_1(k5_relat_1(A_6, B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.47/1.34  tff(c_10, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.47/1.34  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.47/1.34  tff(c_160, plain, (![A_35, B_36]: (r1_tarski(k1_relat_1(k5_relat_1(A_35, B_36)), k1_relat_1(A_35)) | ~v1_relat_1(B_36) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.47/1.34  tff(c_166, plain, (![B_36]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_36)), k1_xboole_0) | ~v1_relat_1(B_36) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_160])).
% 2.47/1.34  tff(c_259, plain, (![B_38]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_38)), k1_xboole_0) | ~v1_relat_1(B_38))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_166])).
% 2.47/1.34  tff(c_8, plain, (![A_2, B_3]: (k4_xboole_0(A_2, B_3)=k1_xboole_0 | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.47/1.34  tff(c_262, plain, (![B_38]: (k4_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0, B_38)), k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_38))), inference(resolution, [status(thm)], [c_259, c_8])).
% 2.47/1.34  tff(c_270, plain, (![B_39]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_39))=k1_xboole_0 | ~v1_relat_1(B_39))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_262])).
% 2.47/1.34  tff(c_16, plain, (![A_8]: (~v1_xboole_0(k1_relat_1(A_8)) | ~v1_relat_1(A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.47/1.34  tff(c_285, plain, (![B_39]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_39)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_39)) | ~v1_relat_1(B_39))), inference(superposition, [status(thm), theory('equality')], [c_270, c_16])).
% 2.47/1.34  tff(c_301, plain, (![B_40]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_40)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_40)) | ~v1_relat_1(B_40))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_285])).
% 2.47/1.34  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.47/1.34  tff(c_315, plain, (![B_41]: (k5_relat_1(k1_xboole_0, B_41)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_41)) | ~v1_relat_1(B_41))), inference(resolution, [status(thm)], [c_301, c_4])).
% 2.47/1.34  tff(c_322, plain, (![B_7]: (k5_relat_1(k1_xboole_0, B_7)=k1_xboole_0 | ~v1_relat_1(B_7) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_315])).
% 2.47/1.34  tff(c_361, plain, (![B_44]: (k5_relat_1(k1_xboole_0, B_44)=k1_xboole_0 | ~v1_relat_1(B_44))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_322])).
% 2.47/1.34  tff(c_370, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_361])).
% 2.47/1.34  tff(c_377, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_370])).
% 2.47/1.34  tff(c_378, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_28])).
% 2.47/1.34  tff(c_24, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.47/1.34  tff(c_422, plain, (![A_54, B_55]: (r1_tarski(k2_relat_1(k5_relat_1(A_54, B_55)), k2_relat_1(B_55)) | ~v1_relat_1(B_55) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.47/1.34  tff(c_456, plain, (![A_57, B_58]: (k4_xboole_0(k2_relat_1(k5_relat_1(A_57, B_58)), k2_relat_1(B_58))=k1_xboole_0 | ~v1_relat_1(B_58) | ~v1_relat_1(A_57))), inference(resolution, [status(thm)], [c_422, c_8])).
% 2.47/1.34  tff(c_468, plain, (![A_57]: (k4_xboole_0(k2_relat_1(k5_relat_1(A_57, k1_xboole_0)), k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_57))), inference(superposition, [status(thm), theory('equality')], [c_24, c_456])).
% 2.47/1.34  tff(c_506, plain, (![A_60]: (k2_relat_1(k5_relat_1(A_60, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_60))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_10, c_468])).
% 2.47/1.34  tff(c_18, plain, (![A_9]: (~v1_xboole_0(k2_relat_1(A_9)) | ~v1_relat_1(A_9) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.47/1.34  tff(c_524, plain, (![A_60]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_60, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_60, k1_xboole_0)) | ~v1_relat_1(A_60))), inference(superposition, [status(thm), theory('equality')], [c_506, c_18])).
% 2.47/1.34  tff(c_561, plain, (![A_63]: (~v1_relat_1(k5_relat_1(A_63, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_63, k1_xboole_0)) | ~v1_relat_1(A_63))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_524])).
% 2.47/1.34  tff(c_684, plain, (![A_68]: (k5_relat_1(A_68, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_68, k1_xboole_0)) | ~v1_relat_1(A_68))), inference(resolution, [status(thm)], [c_561, c_4])).
% 2.47/1.34  tff(c_691, plain, (![A_6]: (k5_relat_1(A_6, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_6))), inference(resolution, [status(thm)], [c_14, c_684])).
% 2.47/1.34  tff(c_697, plain, (![A_69]: (k5_relat_1(A_69, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_69))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_691])).
% 2.47/1.34  tff(c_706, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_697])).
% 2.47/1.34  tff(c_713, plain, $false, inference(negUnitSimplification, [status(thm)], [c_378, c_706])).
% 2.47/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.34  
% 2.47/1.34  Inference rules
% 2.47/1.34  ----------------------
% 2.47/1.34  #Ref     : 0
% 2.47/1.34  #Sup     : 145
% 2.47/1.34  #Fact    : 0
% 2.47/1.34  #Define  : 0
% 2.47/1.34  #Split   : 2
% 2.47/1.34  #Chain   : 0
% 2.47/1.34  #Close   : 0
% 2.47/1.34  
% 2.47/1.34  Ordering : KBO
% 2.47/1.34  
% 2.47/1.34  Simplification rules
% 2.47/1.34  ----------------------
% 2.47/1.34  #Subsume      : 14
% 2.47/1.34  #Demod        : 203
% 2.47/1.34  #Tautology    : 93
% 2.47/1.34  #SimpNegUnit  : 6
% 2.47/1.34  #BackRed      : 3
% 2.47/1.34  
% 2.47/1.34  #Partial instantiations: 0
% 2.47/1.34  #Strategies tried      : 1
% 2.47/1.34  
% 2.47/1.34  Timing (in seconds)
% 2.47/1.34  ----------------------
% 2.47/1.34  Preprocessing        : 0.27
% 2.47/1.34  Parsing              : 0.15
% 2.47/1.34  CNF conversion       : 0.02
% 2.47/1.34  Main loop            : 0.31
% 2.47/1.34  Inferencing          : 0.12
% 2.47/1.34  Reduction            : 0.09
% 2.47/1.34  Demodulation         : 0.06
% 2.47/1.34  BG Simplification    : 0.01
% 2.47/1.34  Subsumption          : 0.05
% 2.47/1.34  Abstraction          : 0.01
% 2.47/1.34  MUC search           : 0.00
% 2.47/1.34  Cooper               : 0.00
% 2.47/1.35  Total                : 0.61
% 2.47/1.35  Index Insertion      : 0.00
% 2.47/1.35  Index Deletion       : 0.00
% 2.47/1.35  Index Matching       : 0.00
% 2.47/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
