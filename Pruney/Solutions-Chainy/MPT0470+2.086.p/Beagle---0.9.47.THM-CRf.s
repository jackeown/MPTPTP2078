%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:13 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   57 (  97 expanded)
%              Number of leaves         :   22 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :  109 ( 174 expanded)
%              Number of equality atoms :   29 (  48 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(f_40,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_83,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_24,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_51,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_26,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_36,plain,(
    ! [A_16] :
      ( v1_relat_1(A_16)
      | ~ v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_40,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_36])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( v1_relat_1(k5_relat_1(A_5,B_6))
      | ~ v1_relat_1(B_6)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_22,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_20,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_65,plain,(
    ! [A_24,B_25] :
      ( k1_relat_1(k5_relat_1(A_24,B_25)) = k1_relat_1(A_24)
      | ~ r1_tarski(k2_relat_1(A_24),k1_relat_1(B_25))
      | ~ v1_relat_1(B_25)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_71,plain,(
    ! [B_25] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_25)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_25))
      | ~ v1_relat_1(B_25)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_65])).

tff(c_87,plain,(
    ! [B_28] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_28)) = k1_xboole_0
      | ~ v1_relat_1(B_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4,c_22,c_71])).

tff(c_12,plain,(
    ! [A_7] :
      ( ~ v1_xboole_0(k1_relat_1(A_7))
      | ~ v1_relat_1(A_7)
      | v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_99,plain,(
    ! [B_28] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_28))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_28))
      | ~ v1_relat_1(B_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_12])).

tff(c_131,plain,(
    ! [B_30] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_30))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_30))
      | ~ v1_relat_1(B_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_99])).

tff(c_41,plain,(
    ! [B_17,A_18] :
      ( ~ v1_xboole_0(B_17)
      | B_17 = A_18
      | ~ v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_44,plain,(
    ! [A_18] :
      ( k1_xboole_0 = A_18
      | ~ v1_xboole_0(A_18) ) ),
    inference(resolution,[status(thm)],[c_2,c_41])).

tff(c_165,plain,(
    ! [B_34] :
      ( k5_relat_1(k1_xboole_0,B_34) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_34))
      | ~ v1_relat_1(B_34) ) ),
    inference(resolution,[status(thm)],[c_131,c_44])).

tff(c_169,plain,(
    ! [B_6] :
      ( k5_relat_1(k1_xboole_0,B_6) = k1_xboole_0
      | ~ v1_relat_1(B_6)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_165])).

tff(c_173,plain,(
    ! [B_35] :
      ( k5_relat_1(k1_xboole_0,B_35) = k1_xboole_0
      | ~ v1_relat_1(B_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_169])).

tff(c_182,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_173])).

tff(c_188,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_182])).

tff(c_189,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_213,plain,(
    ! [B_40,A_41] :
      ( k2_relat_1(k5_relat_1(B_40,A_41)) = k2_relat_1(A_41)
      | ~ r1_tarski(k1_relat_1(A_41),k2_relat_1(B_40))
      | ~ v1_relat_1(B_40)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_216,plain,(
    ! [B_40] :
      ( k2_relat_1(k5_relat_1(B_40,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_40))
      | ~ v1_relat_1(B_40)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_213])).

tff(c_235,plain,(
    ! [B_44] :
      ( k2_relat_1(k5_relat_1(B_44,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4,c_20,c_216])).

tff(c_14,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(k2_relat_1(A_8))
      | ~ v1_relat_1(A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_247,plain,(
    ! [B_44] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_44,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(B_44,k1_xboole_0))
      | ~ v1_relat_1(B_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_14])).

tff(c_284,plain,(
    ! [B_46] :
      ( ~ v1_relat_1(k5_relat_1(B_46,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(B_46,k1_xboole_0))
      | ~ v1_relat_1(B_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_247])).

tff(c_313,plain,(
    ! [B_48] :
      ( k5_relat_1(B_48,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_48,k1_xboole_0))
      | ~ v1_relat_1(B_48) ) ),
    inference(resolution,[status(thm)],[c_284,c_44])).

tff(c_317,plain,(
    ! [A_5] :
      ( k5_relat_1(A_5,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_5) ) ),
    inference(resolution,[status(thm)],[c_10,c_313])).

tff(c_361,plain,(
    ! [A_50] :
      ( k5_relat_1(A_50,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_317])).

tff(c_370,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_361])).

tff(c_376,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_370])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:00:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.28  
% 2.11/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.28  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.26/1.28  
% 2.26/1.28  %Foreground sorts:
% 2.26/1.28  
% 2.26/1.28  
% 2.26/1.28  %Background operators:
% 2.26/1.28  
% 2.26/1.28  
% 2.26/1.28  %Foreground operators:
% 2.26/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.26/1.28  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.26/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.26/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.26/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.26/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.26/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.26/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.26/1.28  
% 2.26/1.29  tff(f_90, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 2.26/1.29  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.26/1.29  tff(f_40, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.26/1.29  tff(f_46, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.26/1.29  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.26/1.29  tff(f_83, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.26/1.29  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 2.26/1.29  tff(f_54, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.26/1.29  tff(f_36, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 2.26/1.29  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 2.26/1.29  tff(f_62, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.26/1.29  tff(c_24, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.26/1.29  tff(c_51, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_24])).
% 2.26/1.29  tff(c_26, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.26/1.29  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.26/1.29  tff(c_36, plain, (![A_16]: (v1_relat_1(A_16) | ~v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.26/1.29  tff(c_40, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_36])).
% 2.26/1.29  tff(c_10, plain, (![A_5, B_6]: (v1_relat_1(k5_relat_1(A_5, B_6)) | ~v1_relat_1(B_6) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.26/1.29  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.26/1.29  tff(c_22, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.26/1.29  tff(c_20, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.26/1.29  tff(c_65, plain, (![A_24, B_25]: (k1_relat_1(k5_relat_1(A_24, B_25))=k1_relat_1(A_24) | ~r1_tarski(k2_relat_1(A_24), k1_relat_1(B_25)) | ~v1_relat_1(B_25) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.26/1.29  tff(c_71, plain, (![B_25]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_25))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_25)) | ~v1_relat_1(B_25) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_65])).
% 2.26/1.29  tff(c_87, plain, (![B_28]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_28))=k1_xboole_0 | ~v1_relat_1(B_28))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_4, c_22, c_71])).
% 2.26/1.29  tff(c_12, plain, (![A_7]: (~v1_xboole_0(k1_relat_1(A_7)) | ~v1_relat_1(A_7) | v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.26/1.29  tff(c_99, plain, (![B_28]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_28)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_28)) | ~v1_relat_1(B_28))), inference(superposition, [status(thm), theory('equality')], [c_87, c_12])).
% 2.26/1.29  tff(c_131, plain, (![B_30]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_30)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_30)) | ~v1_relat_1(B_30))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_99])).
% 2.26/1.29  tff(c_41, plain, (![B_17, A_18]: (~v1_xboole_0(B_17) | B_17=A_18 | ~v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.26/1.29  tff(c_44, plain, (![A_18]: (k1_xboole_0=A_18 | ~v1_xboole_0(A_18))), inference(resolution, [status(thm)], [c_2, c_41])).
% 2.26/1.29  tff(c_165, plain, (![B_34]: (k5_relat_1(k1_xboole_0, B_34)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_34)) | ~v1_relat_1(B_34))), inference(resolution, [status(thm)], [c_131, c_44])).
% 2.26/1.29  tff(c_169, plain, (![B_6]: (k5_relat_1(k1_xboole_0, B_6)=k1_xboole_0 | ~v1_relat_1(B_6) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_165])).
% 2.26/1.29  tff(c_173, plain, (![B_35]: (k5_relat_1(k1_xboole_0, B_35)=k1_xboole_0 | ~v1_relat_1(B_35))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_169])).
% 2.26/1.29  tff(c_182, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_173])).
% 2.26/1.29  tff(c_188, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_182])).
% 2.26/1.29  tff(c_189, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_24])).
% 2.26/1.29  tff(c_213, plain, (![B_40, A_41]: (k2_relat_1(k5_relat_1(B_40, A_41))=k2_relat_1(A_41) | ~r1_tarski(k1_relat_1(A_41), k2_relat_1(B_40)) | ~v1_relat_1(B_40) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.26/1.29  tff(c_216, plain, (![B_40]: (k2_relat_1(k5_relat_1(B_40, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_40)) | ~v1_relat_1(B_40) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_213])).
% 2.26/1.29  tff(c_235, plain, (![B_44]: (k2_relat_1(k5_relat_1(B_44, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_44))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_4, c_20, c_216])).
% 2.26/1.29  tff(c_14, plain, (![A_8]: (~v1_xboole_0(k2_relat_1(A_8)) | ~v1_relat_1(A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.26/1.29  tff(c_247, plain, (![B_44]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_44, k1_xboole_0)) | v1_xboole_0(k5_relat_1(B_44, k1_xboole_0)) | ~v1_relat_1(B_44))), inference(superposition, [status(thm), theory('equality')], [c_235, c_14])).
% 2.26/1.29  tff(c_284, plain, (![B_46]: (~v1_relat_1(k5_relat_1(B_46, k1_xboole_0)) | v1_xboole_0(k5_relat_1(B_46, k1_xboole_0)) | ~v1_relat_1(B_46))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_247])).
% 2.26/1.29  tff(c_313, plain, (![B_48]: (k5_relat_1(B_48, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_48, k1_xboole_0)) | ~v1_relat_1(B_48))), inference(resolution, [status(thm)], [c_284, c_44])).
% 2.26/1.29  tff(c_317, plain, (![A_5]: (k5_relat_1(A_5, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_5))), inference(resolution, [status(thm)], [c_10, c_313])).
% 2.26/1.29  tff(c_361, plain, (![A_50]: (k5_relat_1(A_50, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_50))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_317])).
% 2.26/1.29  tff(c_370, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_361])).
% 2.26/1.29  tff(c_376, plain, $false, inference(negUnitSimplification, [status(thm)], [c_189, c_370])).
% 2.26/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.29  
% 2.26/1.29  Inference rules
% 2.26/1.29  ----------------------
% 2.26/1.29  #Ref     : 0
% 2.26/1.29  #Sup     : 76
% 2.26/1.29  #Fact    : 0
% 2.26/1.29  #Define  : 0
% 2.26/1.29  #Split   : 1
% 2.26/1.29  #Chain   : 0
% 2.26/1.29  #Close   : 0
% 2.26/1.29  
% 2.26/1.29  Ordering : KBO
% 2.26/1.29  
% 2.26/1.29  Simplification rules
% 2.26/1.29  ----------------------
% 2.26/1.29  #Subsume      : 2
% 2.26/1.29  #Demod        : 55
% 2.26/1.29  #Tautology    : 30
% 2.26/1.29  #SimpNegUnit  : 2
% 2.26/1.29  #BackRed      : 0
% 2.26/1.29  
% 2.26/1.29  #Partial instantiations: 0
% 2.26/1.29  #Strategies tried      : 1
% 2.26/1.29  
% 2.26/1.29  Timing (in seconds)
% 2.26/1.29  ----------------------
% 2.26/1.29  Preprocessing        : 0.26
% 2.26/1.29  Parsing              : 0.15
% 2.26/1.29  CNF conversion       : 0.02
% 2.26/1.29  Main loop            : 0.24
% 2.26/1.29  Inferencing          : 0.10
% 2.26/1.30  Reduction            : 0.06
% 2.26/1.30  Demodulation         : 0.05
% 2.26/1.30  BG Simplification    : 0.01
% 2.26/1.30  Subsumption          : 0.05
% 2.26/1.30  Abstraction          : 0.01
% 2.26/1.30  MUC search           : 0.00
% 2.26/1.30  Cooper               : 0.00
% 2.26/1.30  Total                : 0.54
% 2.26/1.30  Index Insertion      : 0.00
% 2.26/1.30  Index Deletion       : 0.00
% 2.26/1.30  Index Matching       : 0.00
% 2.26/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
