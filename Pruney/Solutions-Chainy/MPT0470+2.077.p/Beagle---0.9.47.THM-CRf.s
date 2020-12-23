%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:11 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   63 (  96 expanded)
%              Number of leaves         :   24 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :  111 ( 166 expanded)
%              Number of equality atoms :   28 (  44 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

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
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

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
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

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

tff(c_26,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_61,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_28,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_37,plain,(
    ! [A_16] :
      ( v1_relat_1(A_16)
      | ~ v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_41,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_37])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k5_relat_1(A_6,B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_8,plain,(
    ! [A_4] : k3_xboole_0(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_24,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_70,plain,(
    ! [A_25,B_26] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_25,B_26)),k1_relat_1(A_25))
      | ~ v1_relat_1(B_26)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_76,plain,(
    ! [B_26] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_26)),k1_xboole_0)
      | ~ v1_relat_1(B_26)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_70])).

tff(c_90,plain,(
    ! [B_29] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_29)),k1_xboole_0)
      | ~ v1_relat_1(B_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_76])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( k3_xboole_0(A_2,B_3) = A_2
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_93,plain,(
    ! [B_29] :
      ( k3_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,B_29)),k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,B_29))
      | ~ v1_relat_1(B_29) ) ),
    inference(resolution,[status(thm)],[c_90,c_6])).

tff(c_96,plain,(
    ! [B_30] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_30)) = k1_xboole_0
      | ~ v1_relat_1(B_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_93])).

tff(c_14,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(k1_relat_1(A_8))
      | ~ v1_relat_1(A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_111,plain,(
    ! [B_30] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_30))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_30))
      | ~ v1_relat_1(B_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_14])).

tff(c_212,plain,(
    ! [B_37] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_37))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_37))
      | ~ v1_relat_1(B_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_111])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_230,plain,(
    ! [B_39] :
      ( k5_relat_1(k1_xboole_0,B_39) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_39))
      | ~ v1_relat_1(B_39) ) ),
    inference(resolution,[status(thm)],[c_212,c_4])).

tff(c_234,plain,(
    ! [B_7] :
      ( k5_relat_1(k1_xboole_0,B_7) = k1_xboole_0
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_230])).

tff(c_246,plain,(
    ! [B_41] :
      ( k5_relat_1(k1_xboole_0,B_41) = k1_xboole_0
      | ~ v1_relat_1(B_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_234])).

tff(c_255,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_246])).

tff(c_261,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_255])).

tff(c_262,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_22,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_281,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_47,B_48)),k2_relat_1(B_48))
      | ~ v1_relat_1(B_48)
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_290,plain,(
    ! [A_47] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_47,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_281])).

tff(c_366,plain,(
    ! [A_53] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_53,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_290])).

tff(c_369,plain,(
    ! [A_53] :
      ( k3_xboole_0(k2_relat_1(k5_relat_1(A_53,k1_xboole_0)),k1_xboole_0) = k2_relat_1(k5_relat_1(A_53,k1_xboole_0))
      | ~ v1_relat_1(A_53) ) ),
    inference(resolution,[status(thm)],[c_366,c_6])).

tff(c_372,plain,(
    ! [A_54] :
      ( k2_relat_1(k5_relat_1(A_54,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_369])).

tff(c_16,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(k2_relat_1(A_9))
      | ~ v1_relat_1(A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_387,plain,(
    ! [A_54] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_54,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_54,k1_xboole_0))
      | ~ v1_relat_1(A_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_16])).

tff(c_440,plain,(
    ! [A_58] :
      ( ~ v1_relat_1(k5_relat_1(A_58,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_58,k1_xboole_0))
      | ~ v1_relat_1(A_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_387])).

tff(c_462,plain,(
    ! [A_60] :
      ( k5_relat_1(A_60,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_60,k1_xboole_0))
      | ~ v1_relat_1(A_60) ) ),
    inference(resolution,[status(thm)],[c_440,c_4])).

tff(c_466,plain,(
    ! [A_6] :
      ( k5_relat_1(A_6,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_6) ) ),
    inference(resolution,[status(thm)],[c_12,c_462])).

tff(c_543,plain,(
    ! [A_62] :
      ( k5_relat_1(A_62,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_466])).

tff(c_552,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_543])).

tff(c_559,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_262,c_552])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:11:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.28  
% 2.17/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.29  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.17/1.29  
% 2.17/1.29  %Foreground sorts:
% 2.17/1.29  
% 2.17/1.29  
% 2.17/1.29  %Background operators:
% 2.17/1.29  
% 2.17/1.29  
% 2.17/1.29  %Foreground operators:
% 2.17/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.17/1.29  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.17/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.17/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.17/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.17/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.17/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.17/1.29  
% 2.17/1.30  tff(f_86, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 2.17/1.30  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.17/1.30  tff(f_40, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.17/1.30  tff(f_46, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.17/1.30  tff(f_36, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.17/1.30  tff(f_79, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.17/1.30  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 2.17/1.30  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.17/1.30  tff(f_54, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.17/1.30  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.17/1.30  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 2.17/1.30  tff(f_62, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.17/1.30  tff(c_26, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.17/1.30  tff(c_61, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_26])).
% 2.17/1.30  tff(c_28, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.17/1.30  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.17/1.30  tff(c_37, plain, (![A_16]: (v1_relat_1(A_16) | ~v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.17/1.30  tff(c_41, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_37])).
% 2.17/1.30  tff(c_12, plain, (![A_6, B_7]: (v1_relat_1(k5_relat_1(A_6, B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.17/1.30  tff(c_8, plain, (![A_4]: (k3_xboole_0(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.17/1.30  tff(c_24, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.17/1.30  tff(c_70, plain, (![A_25, B_26]: (r1_tarski(k1_relat_1(k5_relat_1(A_25, B_26)), k1_relat_1(A_25)) | ~v1_relat_1(B_26) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.17/1.30  tff(c_76, plain, (![B_26]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_26)), k1_xboole_0) | ~v1_relat_1(B_26) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_70])).
% 2.17/1.30  tff(c_90, plain, (![B_29]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_29)), k1_xboole_0) | ~v1_relat_1(B_29))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_76])).
% 2.17/1.30  tff(c_6, plain, (![A_2, B_3]: (k3_xboole_0(A_2, B_3)=A_2 | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.17/1.30  tff(c_93, plain, (![B_29]: (k3_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0, B_29)), k1_xboole_0)=k1_relat_1(k5_relat_1(k1_xboole_0, B_29)) | ~v1_relat_1(B_29))), inference(resolution, [status(thm)], [c_90, c_6])).
% 2.17/1.30  tff(c_96, plain, (![B_30]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_30))=k1_xboole_0 | ~v1_relat_1(B_30))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_93])).
% 2.17/1.30  tff(c_14, plain, (![A_8]: (~v1_xboole_0(k1_relat_1(A_8)) | ~v1_relat_1(A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.17/1.30  tff(c_111, plain, (![B_30]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_30)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_30)) | ~v1_relat_1(B_30))), inference(superposition, [status(thm), theory('equality')], [c_96, c_14])).
% 2.17/1.30  tff(c_212, plain, (![B_37]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_37)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_37)) | ~v1_relat_1(B_37))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_111])).
% 2.17/1.30  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.17/1.30  tff(c_230, plain, (![B_39]: (k5_relat_1(k1_xboole_0, B_39)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_39)) | ~v1_relat_1(B_39))), inference(resolution, [status(thm)], [c_212, c_4])).
% 2.17/1.30  tff(c_234, plain, (![B_7]: (k5_relat_1(k1_xboole_0, B_7)=k1_xboole_0 | ~v1_relat_1(B_7) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_230])).
% 2.17/1.30  tff(c_246, plain, (![B_41]: (k5_relat_1(k1_xboole_0, B_41)=k1_xboole_0 | ~v1_relat_1(B_41))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_234])).
% 2.17/1.30  tff(c_255, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_246])).
% 2.17/1.30  tff(c_261, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_255])).
% 2.17/1.30  tff(c_262, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_26])).
% 2.17/1.30  tff(c_22, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.17/1.30  tff(c_281, plain, (![A_47, B_48]: (r1_tarski(k2_relat_1(k5_relat_1(A_47, B_48)), k2_relat_1(B_48)) | ~v1_relat_1(B_48) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.17/1.30  tff(c_290, plain, (![A_47]: (r1_tarski(k2_relat_1(k5_relat_1(A_47, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_47))), inference(superposition, [status(thm), theory('equality')], [c_22, c_281])).
% 2.17/1.30  tff(c_366, plain, (![A_53]: (r1_tarski(k2_relat_1(k5_relat_1(A_53, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_53))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_290])).
% 2.17/1.30  tff(c_369, plain, (![A_53]: (k3_xboole_0(k2_relat_1(k5_relat_1(A_53, k1_xboole_0)), k1_xboole_0)=k2_relat_1(k5_relat_1(A_53, k1_xboole_0)) | ~v1_relat_1(A_53))), inference(resolution, [status(thm)], [c_366, c_6])).
% 2.17/1.30  tff(c_372, plain, (![A_54]: (k2_relat_1(k5_relat_1(A_54, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_54))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_369])).
% 2.17/1.30  tff(c_16, plain, (![A_9]: (~v1_xboole_0(k2_relat_1(A_9)) | ~v1_relat_1(A_9) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.17/1.30  tff(c_387, plain, (![A_54]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_54, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_54, k1_xboole_0)) | ~v1_relat_1(A_54))), inference(superposition, [status(thm), theory('equality')], [c_372, c_16])).
% 2.17/1.30  tff(c_440, plain, (![A_58]: (~v1_relat_1(k5_relat_1(A_58, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_58, k1_xboole_0)) | ~v1_relat_1(A_58))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_387])).
% 2.17/1.30  tff(c_462, plain, (![A_60]: (k5_relat_1(A_60, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_60, k1_xboole_0)) | ~v1_relat_1(A_60))), inference(resolution, [status(thm)], [c_440, c_4])).
% 2.17/1.30  tff(c_466, plain, (![A_6]: (k5_relat_1(A_6, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_6))), inference(resolution, [status(thm)], [c_12, c_462])).
% 2.17/1.30  tff(c_543, plain, (![A_62]: (k5_relat_1(A_62, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_62))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_466])).
% 2.17/1.30  tff(c_552, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_543])).
% 2.17/1.30  tff(c_559, plain, $false, inference(negUnitSimplification, [status(thm)], [c_262, c_552])).
% 2.17/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.30  
% 2.17/1.30  Inference rules
% 2.17/1.30  ----------------------
% 2.17/1.30  #Ref     : 0
% 2.17/1.30  #Sup     : 111
% 2.17/1.30  #Fact    : 0
% 2.17/1.30  #Define  : 0
% 2.17/1.30  #Split   : 2
% 2.17/1.30  #Chain   : 0
% 2.17/1.30  #Close   : 0
% 2.17/1.30  
% 2.17/1.30  Ordering : KBO
% 2.17/1.30  
% 2.17/1.30  Simplification rules
% 2.17/1.30  ----------------------
% 2.17/1.30  #Subsume      : 17
% 2.17/1.30  #Demod        : 131
% 2.17/1.30  #Tautology    : 62
% 2.17/1.30  #SimpNegUnit  : 6
% 2.17/1.30  #BackRed      : 3
% 2.17/1.30  
% 2.17/1.30  #Partial instantiations: 0
% 2.17/1.30  #Strategies tried      : 1
% 2.17/1.30  
% 2.17/1.30  Timing (in seconds)
% 2.17/1.30  ----------------------
% 2.17/1.30  Preprocessing        : 0.27
% 2.17/1.30  Parsing              : 0.15
% 2.17/1.30  CNF conversion       : 0.02
% 2.17/1.30  Main loop            : 0.28
% 2.17/1.30  Inferencing          : 0.12
% 2.17/1.30  Reduction            : 0.08
% 2.17/1.30  Demodulation         : 0.06
% 2.17/1.30  BG Simplification    : 0.01
% 2.17/1.30  Subsumption          : 0.05
% 2.17/1.30  Abstraction          : 0.01
% 2.17/1.30  MUC search           : 0.00
% 2.17/1.30  Cooper               : 0.00
% 2.17/1.31  Total                : 0.59
% 2.17/1.31  Index Insertion      : 0.00
% 2.17/1.31  Index Deletion       : 0.00
% 2.17/1.31  Index Matching       : 0.00
% 2.17/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
