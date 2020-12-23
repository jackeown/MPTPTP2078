%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:12 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   62 (  90 expanded)
%              Number of leaves         :   24 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :  108 ( 158 expanded)
%              Number of equality atoms :   20 (  32 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_83,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_32,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_26,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_55,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_28,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_38,plain,(
    ! [A_17] :
      ( v1_relat_1(A_17)
      | ~ v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_42,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_38])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k5_relat_1(A_6,B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_24,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_122,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_31,B_32)),k1_relat_1(A_31))
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_125,plain,(
    ! [B_32] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_32)),k1_xboole_0)
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_122])).

tff(c_146,plain,(
    ! [B_34] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_34)),k1_xboole_0)
      | ~ v1_relat_1(B_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_125])).

tff(c_6,plain,(
    ! [A_2] : r1_xboole_0(A_2,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_62,plain,(
    ! [B_21,A_22] :
      ( ~ r1_xboole_0(B_21,A_22)
      | ~ r1_tarski(B_21,A_22)
      | v1_xboole_0(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_66,plain,(
    ! [A_2] :
      ( ~ r1_tarski(A_2,k1_xboole_0)
      | v1_xboole_0(A_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_62])).

tff(c_151,plain,(
    ! [B_35] :
      ( v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,B_35)))
      | ~ v1_relat_1(B_35) ) ),
    inference(resolution,[status(thm)],[c_146,c_66])).

tff(c_14,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(k1_relat_1(A_8))
      | ~ v1_relat_1(A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_208,plain,(
    ! [B_39] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_39))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_39))
      | ~ v1_relat_1(B_39) ) ),
    inference(resolution,[status(thm)],[c_151,c_14])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_217,plain,(
    ! [B_40] :
      ( k5_relat_1(k1_xboole_0,B_40) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_40))
      | ~ v1_relat_1(B_40) ) ),
    inference(resolution,[status(thm)],[c_208,c_4])).

tff(c_221,plain,(
    ! [B_7] :
      ( k5_relat_1(k1_xboole_0,B_7) = k1_xboole_0
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_217])).

tff(c_225,plain,(
    ! [B_41] :
      ( k5_relat_1(k1_xboole_0,B_41) = k1_xboole_0
      | ~ v1_relat_1(B_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_221])).

tff(c_240,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_225])).

tff(c_248,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_240])).

tff(c_249,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_22,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_273,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_48,B_49)),k2_relat_1(B_49))
      | ~ v1_relat_1(B_49)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_279,plain,(
    ! [A_48] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_48,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_273])).

tff(c_284,plain,(
    ! [A_50] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_50,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_279])).

tff(c_261,plain,(
    ! [B_43,A_44] :
      ( ~ r1_xboole_0(B_43,A_44)
      | ~ r1_tarski(B_43,A_44)
      | v1_xboole_0(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_265,plain,(
    ! [A_2] :
      ( ~ r1_tarski(A_2,k1_xboole_0)
      | v1_xboole_0(A_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_261])).

tff(c_289,plain,(
    ! [A_51] :
      ( v1_xboole_0(k2_relat_1(k5_relat_1(A_51,k1_xboole_0)))
      | ~ v1_relat_1(A_51) ) ),
    inference(resolution,[status(thm)],[c_284,c_265])).

tff(c_16,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(k2_relat_1(A_9))
      | ~ v1_relat_1(A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_353,plain,(
    ! [A_56] :
      ( ~ v1_relat_1(k5_relat_1(A_56,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_56,k1_xboole_0))
      | ~ v1_relat_1(A_56) ) ),
    inference(resolution,[status(thm)],[c_289,c_16])).

tff(c_450,plain,(
    ! [A_62] :
      ( k5_relat_1(A_62,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_62,k1_xboole_0))
      | ~ v1_relat_1(A_62) ) ),
    inference(resolution,[status(thm)],[c_353,c_4])).

tff(c_454,plain,(
    ! [A_6] :
      ( k5_relat_1(A_6,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_6) ) ),
    inference(resolution,[status(thm)],[c_12,c_450])).

tff(c_458,plain,(
    ! [A_63] :
      ( k5_relat_1(A_63,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_454])).

tff(c_473,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_458])).

tff(c_481,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_249,c_473])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:56:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.32  
% 2.12/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.32  %$ r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.12/1.32  
% 2.12/1.32  %Foreground sorts:
% 2.12/1.32  
% 2.12/1.32  
% 2.12/1.32  %Background operators:
% 2.12/1.32  
% 2.12/1.32  
% 2.12/1.32  %Foreground operators:
% 2.12/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.12/1.32  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.12/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.12/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.12/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.12/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.12/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.12/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.12/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.12/1.32  
% 2.43/1.34  tff(f_90, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 2.43/1.34  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.43/1.34  tff(f_44, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.43/1.34  tff(f_50, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.43/1.34  tff(f_83, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.43/1.34  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 2.43/1.34  tff(f_32, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.43/1.34  tff(f_40, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.43/1.34  tff(f_58, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.43/1.34  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.43/1.34  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 2.43/1.34  tff(f_66, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.43/1.34  tff(c_26, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.43/1.34  tff(c_55, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_26])).
% 2.43/1.34  tff(c_28, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.43/1.34  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.43/1.34  tff(c_38, plain, (![A_17]: (v1_relat_1(A_17) | ~v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.43/1.34  tff(c_42, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_38])).
% 2.43/1.34  tff(c_12, plain, (![A_6, B_7]: (v1_relat_1(k5_relat_1(A_6, B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.43/1.34  tff(c_24, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.43/1.34  tff(c_122, plain, (![A_31, B_32]: (r1_tarski(k1_relat_1(k5_relat_1(A_31, B_32)), k1_relat_1(A_31)) | ~v1_relat_1(B_32) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.43/1.34  tff(c_125, plain, (![B_32]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_32)), k1_xboole_0) | ~v1_relat_1(B_32) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_122])).
% 2.43/1.34  tff(c_146, plain, (![B_34]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_34)), k1_xboole_0) | ~v1_relat_1(B_34))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_125])).
% 2.43/1.34  tff(c_6, plain, (![A_2]: (r1_xboole_0(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.43/1.34  tff(c_62, plain, (![B_21, A_22]: (~r1_xboole_0(B_21, A_22) | ~r1_tarski(B_21, A_22) | v1_xboole_0(B_21))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.43/1.34  tff(c_66, plain, (![A_2]: (~r1_tarski(A_2, k1_xboole_0) | v1_xboole_0(A_2))), inference(resolution, [status(thm)], [c_6, c_62])).
% 2.43/1.34  tff(c_151, plain, (![B_35]: (v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0, B_35))) | ~v1_relat_1(B_35))), inference(resolution, [status(thm)], [c_146, c_66])).
% 2.43/1.34  tff(c_14, plain, (![A_8]: (~v1_xboole_0(k1_relat_1(A_8)) | ~v1_relat_1(A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.43/1.34  tff(c_208, plain, (![B_39]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_39)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_39)) | ~v1_relat_1(B_39))), inference(resolution, [status(thm)], [c_151, c_14])).
% 2.43/1.34  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.43/1.34  tff(c_217, plain, (![B_40]: (k5_relat_1(k1_xboole_0, B_40)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_40)) | ~v1_relat_1(B_40))), inference(resolution, [status(thm)], [c_208, c_4])).
% 2.43/1.34  tff(c_221, plain, (![B_7]: (k5_relat_1(k1_xboole_0, B_7)=k1_xboole_0 | ~v1_relat_1(B_7) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_217])).
% 2.43/1.34  tff(c_225, plain, (![B_41]: (k5_relat_1(k1_xboole_0, B_41)=k1_xboole_0 | ~v1_relat_1(B_41))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_221])).
% 2.43/1.34  tff(c_240, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_225])).
% 2.43/1.34  tff(c_248, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_240])).
% 2.43/1.34  tff(c_249, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_26])).
% 2.43/1.34  tff(c_22, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.43/1.34  tff(c_273, plain, (![A_48, B_49]: (r1_tarski(k2_relat_1(k5_relat_1(A_48, B_49)), k2_relat_1(B_49)) | ~v1_relat_1(B_49) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.43/1.34  tff(c_279, plain, (![A_48]: (r1_tarski(k2_relat_1(k5_relat_1(A_48, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_48))), inference(superposition, [status(thm), theory('equality')], [c_22, c_273])).
% 2.43/1.34  tff(c_284, plain, (![A_50]: (r1_tarski(k2_relat_1(k5_relat_1(A_50, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_50))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_279])).
% 2.43/1.34  tff(c_261, plain, (![B_43, A_44]: (~r1_xboole_0(B_43, A_44) | ~r1_tarski(B_43, A_44) | v1_xboole_0(B_43))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.43/1.34  tff(c_265, plain, (![A_2]: (~r1_tarski(A_2, k1_xboole_0) | v1_xboole_0(A_2))), inference(resolution, [status(thm)], [c_6, c_261])).
% 2.43/1.34  tff(c_289, plain, (![A_51]: (v1_xboole_0(k2_relat_1(k5_relat_1(A_51, k1_xboole_0))) | ~v1_relat_1(A_51))), inference(resolution, [status(thm)], [c_284, c_265])).
% 2.43/1.34  tff(c_16, plain, (![A_9]: (~v1_xboole_0(k2_relat_1(A_9)) | ~v1_relat_1(A_9) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.43/1.34  tff(c_353, plain, (![A_56]: (~v1_relat_1(k5_relat_1(A_56, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_56, k1_xboole_0)) | ~v1_relat_1(A_56))), inference(resolution, [status(thm)], [c_289, c_16])).
% 2.43/1.34  tff(c_450, plain, (![A_62]: (k5_relat_1(A_62, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_62, k1_xboole_0)) | ~v1_relat_1(A_62))), inference(resolution, [status(thm)], [c_353, c_4])).
% 2.43/1.34  tff(c_454, plain, (![A_6]: (k5_relat_1(A_6, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_6))), inference(resolution, [status(thm)], [c_12, c_450])).
% 2.43/1.34  tff(c_458, plain, (![A_63]: (k5_relat_1(A_63, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_63))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_454])).
% 2.43/1.34  tff(c_473, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_458])).
% 2.43/1.34  tff(c_481, plain, $false, inference(negUnitSimplification, [status(thm)], [c_249, c_473])).
% 2.43/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.34  
% 2.43/1.34  Inference rules
% 2.43/1.34  ----------------------
% 2.43/1.34  #Ref     : 0
% 2.43/1.34  #Sup     : 95
% 2.43/1.34  #Fact    : 0
% 2.43/1.34  #Define  : 0
% 2.43/1.34  #Split   : 2
% 2.43/1.34  #Chain   : 0
% 2.43/1.34  #Close   : 0
% 2.43/1.34  
% 2.43/1.34  Ordering : KBO
% 2.43/1.34  
% 2.43/1.34  Simplification rules
% 2.43/1.34  ----------------------
% 2.43/1.34  #Subsume      : 12
% 2.43/1.34  #Demod        : 69
% 2.43/1.34  #Tautology    : 45
% 2.43/1.34  #SimpNegUnit  : 6
% 2.43/1.34  #BackRed      : 3
% 2.43/1.34  
% 2.43/1.34  #Partial instantiations: 0
% 2.43/1.34  #Strategies tried      : 1
% 2.43/1.34  
% 2.43/1.34  Timing (in seconds)
% 2.43/1.34  ----------------------
% 2.43/1.34  Preprocessing        : 0.28
% 2.43/1.34  Parsing              : 0.17
% 2.43/1.34  CNF conversion       : 0.02
% 2.43/1.34  Main loop            : 0.25
% 2.43/1.34  Inferencing          : 0.10
% 2.43/1.34  Reduction            : 0.06
% 2.43/1.34  Demodulation         : 0.04
% 2.43/1.34  BG Simplification    : 0.01
% 2.43/1.34  Subsumption          : 0.05
% 2.43/1.34  Abstraction          : 0.01
% 2.43/1.34  MUC search           : 0.00
% 2.43/1.34  Cooper               : 0.00
% 2.43/1.34  Total                : 0.56
% 2.43/1.34  Index Insertion      : 0.00
% 2.43/1.34  Index Deletion       : 0.00
% 2.43/1.34  Index Matching       : 0.00
% 2.43/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
