%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:13 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   59 (  95 expanded)
%              Number of leaves         :   22 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :  109 ( 170 expanded)
%              Number of equality atoms :   25 (  40 expanded)
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

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_81,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_24,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_51,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_26,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_35,plain,(
    ! [A_15] :
      ( v1_relat_1(A_15)
      | ~ v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_39,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_35])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( v1_relat_1(k5_relat_1(A_5,B_6))
      | ~ v1_relat_1(B_6)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_22,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_65,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_24,B_25)),k1_relat_1(A_24))
      | ~ v1_relat_1(B_25)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_68,plain,(
    ! [B_25] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_25)),k1_xboole_0)
      | ~ v1_relat_1(B_25)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_65])).

tff(c_77,plain,(
    ! [B_28] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_28)),k1_xboole_0)
      | ~ v1_relat_1(B_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_68])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_82,plain,(
    ! [B_29] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_29)) = k1_xboole_0
      | ~ v1_relat_1(B_29) ) ),
    inference(resolution,[status(thm)],[c_77,c_4])).

tff(c_12,plain,(
    ! [A_7] :
      ( ~ v1_xboole_0(k1_relat_1(A_7))
      | ~ v1_relat_1(A_7)
      | v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_97,plain,(
    ! [B_29] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_29))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_29))
      | ~ v1_relat_1(B_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_12])).

tff(c_156,plain,(
    ! [B_34] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_34))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_34))
      | ~ v1_relat_1(B_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_97])).

tff(c_41,plain,(
    ! [B_17,A_18] :
      ( ~ v1_xboole_0(B_17)
      | B_17 = A_18
      | ~ v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_44,plain,(
    ! [A_18] :
      ( k1_xboole_0 = A_18
      | ~ v1_xboole_0(A_18) ) ),
    inference(resolution,[status(thm)],[c_2,c_41])).

tff(c_180,plain,(
    ! [B_36] :
      ( k5_relat_1(k1_xboole_0,B_36) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_36))
      | ~ v1_relat_1(B_36) ) ),
    inference(resolution,[status(thm)],[c_156,c_44])).

tff(c_184,plain,(
    ! [B_6] :
      ( k5_relat_1(k1_xboole_0,B_6) = k1_xboole_0
      | ~ v1_relat_1(B_6)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_180])).

tff(c_188,plain,(
    ! [B_37] :
      ( k5_relat_1(k1_xboole_0,B_37) = k1_xboole_0
      | ~ v1_relat_1(B_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_184])).

tff(c_197,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_188])).

tff(c_203,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_197])).

tff(c_204,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_20,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_228,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_42,B_43)),k2_relat_1(B_43))
      | ~ v1_relat_1(B_43)
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_234,plain,(
    ! [A_42] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_42,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_228])).

tff(c_296,plain,(
    ! [A_48] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_48,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_234])).

tff(c_301,plain,(
    ! [A_49] :
      ( k2_relat_1(k5_relat_1(A_49,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_49) ) ),
    inference(resolution,[status(thm)],[c_296,c_4])).

tff(c_14,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(k2_relat_1(A_8))
      | ~ v1_relat_1(A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_316,plain,(
    ! [A_49] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_49,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_49,k1_xboole_0))
      | ~ v1_relat_1(A_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_14])).

tff(c_344,plain,(
    ! [A_51] :
      ( ~ v1_relat_1(k5_relat_1(A_51,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_51,k1_xboole_0))
      | ~ v1_relat_1(A_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_316])).

tff(c_447,plain,(
    ! [A_56] :
      ( k5_relat_1(A_56,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_56,k1_xboole_0))
      | ~ v1_relat_1(A_56) ) ),
    inference(resolution,[status(thm)],[c_344,c_44])).

tff(c_454,plain,(
    ! [A_5] :
      ( k5_relat_1(A_5,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_5) ) ),
    inference(resolution,[status(thm)],[c_10,c_447])).

tff(c_519,plain,(
    ! [A_59] :
      ( k5_relat_1(A_59,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_454])).

tff(c_528,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_519])).

tff(c_535,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_204,c_528])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:08:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.32  
% 2.37/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.32  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.37/1.32  
% 2.37/1.32  %Foreground sorts:
% 2.37/1.32  
% 2.37/1.32  
% 2.37/1.32  %Background operators:
% 2.37/1.32  
% 2.37/1.32  
% 2.37/1.32  %Foreground operators:
% 2.37/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.37/1.32  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.37/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.37/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.37/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.37/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.37/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.37/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.37/1.32  
% 2.37/1.33  tff(f_88, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 2.37/1.33  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.37/1.33  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.37/1.33  tff(f_48, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.37/1.33  tff(f_81, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.37/1.33  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 2.37/1.33  tff(f_30, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.37/1.33  tff(f_56, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.37/1.33  tff(f_38, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 2.37/1.33  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 2.37/1.33  tff(f_64, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.37/1.33  tff(c_24, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.37/1.33  tff(c_51, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_24])).
% 2.37/1.33  tff(c_26, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.37/1.33  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.37/1.33  tff(c_35, plain, (![A_15]: (v1_relat_1(A_15) | ~v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.37/1.33  tff(c_39, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_35])).
% 2.37/1.33  tff(c_10, plain, (![A_5, B_6]: (v1_relat_1(k5_relat_1(A_5, B_6)) | ~v1_relat_1(B_6) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.37/1.33  tff(c_22, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.37/1.33  tff(c_65, plain, (![A_24, B_25]: (r1_tarski(k1_relat_1(k5_relat_1(A_24, B_25)), k1_relat_1(A_24)) | ~v1_relat_1(B_25) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.37/1.33  tff(c_68, plain, (![B_25]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_25)), k1_xboole_0) | ~v1_relat_1(B_25) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_65])).
% 2.37/1.33  tff(c_77, plain, (![B_28]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_28)), k1_xboole_0) | ~v1_relat_1(B_28))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_68])).
% 2.37/1.33  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.37/1.33  tff(c_82, plain, (![B_29]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_29))=k1_xboole_0 | ~v1_relat_1(B_29))), inference(resolution, [status(thm)], [c_77, c_4])).
% 2.37/1.33  tff(c_12, plain, (![A_7]: (~v1_xboole_0(k1_relat_1(A_7)) | ~v1_relat_1(A_7) | v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.37/1.33  tff(c_97, plain, (![B_29]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_29)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_29)) | ~v1_relat_1(B_29))), inference(superposition, [status(thm), theory('equality')], [c_82, c_12])).
% 2.37/1.33  tff(c_156, plain, (![B_34]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_34)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_34)) | ~v1_relat_1(B_34))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_97])).
% 2.37/1.33  tff(c_41, plain, (![B_17, A_18]: (~v1_xboole_0(B_17) | B_17=A_18 | ~v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.37/1.33  tff(c_44, plain, (![A_18]: (k1_xboole_0=A_18 | ~v1_xboole_0(A_18))), inference(resolution, [status(thm)], [c_2, c_41])).
% 2.37/1.33  tff(c_180, plain, (![B_36]: (k5_relat_1(k1_xboole_0, B_36)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_36)) | ~v1_relat_1(B_36))), inference(resolution, [status(thm)], [c_156, c_44])).
% 2.37/1.33  tff(c_184, plain, (![B_6]: (k5_relat_1(k1_xboole_0, B_6)=k1_xboole_0 | ~v1_relat_1(B_6) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_180])).
% 2.37/1.33  tff(c_188, plain, (![B_37]: (k5_relat_1(k1_xboole_0, B_37)=k1_xboole_0 | ~v1_relat_1(B_37))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_184])).
% 2.37/1.33  tff(c_197, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_188])).
% 2.37/1.33  tff(c_203, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_197])).
% 2.37/1.33  tff(c_204, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_24])).
% 2.37/1.33  tff(c_20, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.37/1.33  tff(c_228, plain, (![A_42, B_43]: (r1_tarski(k2_relat_1(k5_relat_1(A_42, B_43)), k2_relat_1(B_43)) | ~v1_relat_1(B_43) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.37/1.33  tff(c_234, plain, (![A_42]: (r1_tarski(k2_relat_1(k5_relat_1(A_42, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_42))), inference(superposition, [status(thm), theory('equality')], [c_20, c_228])).
% 2.37/1.33  tff(c_296, plain, (![A_48]: (r1_tarski(k2_relat_1(k5_relat_1(A_48, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_48))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_234])).
% 2.37/1.33  tff(c_301, plain, (![A_49]: (k2_relat_1(k5_relat_1(A_49, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_49))), inference(resolution, [status(thm)], [c_296, c_4])).
% 2.37/1.33  tff(c_14, plain, (![A_8]: (~v1_xboole_0(k2_relat_1(A_8)) | ~v1_relat_1(A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.37/1.33  tff(c_316, plain, (![A_49]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_49, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_49, k1_xboole_0)) | ~v1_relat_1(A_49))), inference(superposition, [status(thm), theory('equality')], [c_301, c_14])).
% 2.37/1.33  tff(c_344, plain, (![A_51]: (~v1_relat_1(k5_relat_1(A_51, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_51, k1_xboole_0)) | ~v1_relat_1(A_51))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_316])).
% 2.37/1.33  tff(c_447, plain, (![A_56]: (k5_relat_1(A_56, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_56, k1_xboole_0)) | ~v1_relat_1(A_56))), inference(resolution, [status(thm)], [c_344, c_44])).
% 2.37/1.33  tff(c_454, plain, (![A_5]: (k5_relat_1(A_5, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_5))), inference(resolution, [status(thm)], [c_10, c_447])).
% 2.37/1.33  tff(c_519, plain, (![A_59]: (k5_relat_1(A_59, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_59))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_454])).
% 2.37/1.33  tff(c_528, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_519])).
% 2.37/1.33  tff(c_535, plain, $false, inference(negUnitSimplification, [status(thm)], [c_204, c_528])).
% 2.37/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.33  
% 2.37/1.33  Inference rules
% 2.37/1.33  ----------------------
% 2.37/1.33  #Ref     : 0
% 2.37/1.33  #Sup     : 107
% 2.37/1.33  #Fact    : 0
% 2.37/1.33  #Define  : 0
% 2.37/1.33  #Split   : 2
% 2.37/1.33  #Chain   : 0
% 2.37/1.33  #Close   : 0
% 2.37/1.33  
% 2.37/1.33  Ordering : KBO
% 2.37/1.33  
% 2.37/1.33  Simplification rules
% 2.37/1.33  ----------------------
% 2.37/1.33  #Subsume      : 14
% 2.37/1.33  #Demod        : 124
% 2.37/1.33  #Tautology    : 62
% 2.37/1.33  #SimpNegUnit  : 6
% 2.37/1.33  #BackRed      : 3
% 2.37/1.33  
% 2.37/1.33  #Partial instantiations: 0
% 2.37/1.33  #Strategies tried      : 1
% 2.37/1.33  
% 2.37/1.33  Timing (in seconds)
% 2.37/1.33  ----------------------
% 2.37/1.34  Preprocessing        : 0.28
% 2.37/1.34  Parsing              : 0.15
% 2.37/1.34  CNF conversion       : 0.02
% 2.37/1.34  Main loop            : 0.27
% 2.37/1.34  Inferencing          : 0.11
% 2.37/1.34  Reduction            : 0.07
% 2.37/1.34  Demodulation         : 0.05
% 2.37/1.34  BG Simplification    : 0.01
% 2.37/1.34  Subsumption          : 0.05
% 2.37/1.34  Abstraction          : 0.01
% 2.37/1.34  MUC search           : 0.00
% 2.37/1.34  Cooper               : 0.00
% 2.37/1.34  Total                : 0.58
% 2.37/1.34  Index Insertion      : 0.00
% 2.37/1.34  Index Deletion       : 0.00
% 2.37/1.34  Index Matching       : 0.00
% 2.37/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
