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
% DateTime   : Thu Dec  3 09:59:12 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   58 (  89 expanded)
%              Number of leaves         :   22 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :  105 ( 158 expanded)
%              Number of equality atoms :   24 (  38 expanded)
%              Maximal formula depth    :    6 (   4 average)
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

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_77,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_34,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_52,axiom,(
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

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_24,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_53,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_26,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_35,plain,(
    ! [A_14] :
      ( v1_relat_1(A_14)
      | ~ v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_39,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_35])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(k5_relat_1(A_4,B_5))
      | ~ v1_relat_1(B_5)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_22,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_61,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_21,B_22)),k1_relat_1(A_21))
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_64,plain,(
    ! [B_22] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_22)),k1_xboole_0)
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_61])).

tff(c_67,plain,(
    ! [B_23] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_23)),k1_xboole_0)
      | ~ v1_relat_1(B_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_64])).

tff(c_6,plain,(
    ! [A_2] :
      ( k1_xboole_0 = A_2
      | ~ r1_tarski(A_2,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_78,plain,(
    ! [B_26] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_26)) = k1_xboole_0
      | ~ v1_relat_1(B_26) ) ),
    inference(resolution,[status(thm)],[c_67,c_6])).

tff(c_12,plain,(
    ! [A_6] :
      ( ~ v1_xboole_0(k1_relat_1(A_6))
      | ~ v1_relat_1(A_6)
      | v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_93,plain,(
    ! [B_26] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_26))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_26))
      | ~ v1_relat_1(B_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_12])).

tff(c_152,plain,(
    ! [B_31] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_31))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_31))
      | ~ v1_relat_1(B_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_93])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_170,plain,(
    ! [B_33] :
      ( k5_relat_1(k1_xboole_0,B_33) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_33))
      | ~ v1_relat_1(B_33) ) ),
    inference(resolution,[status(thm)],[c_152,c_4])).

tff(c_174,plain,(
    ! [B_5] :
      ( k5_relat_1(k1_xboole_0,B_5) = k1_xboole_0
      | ~ v1_relat_1(B_5)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_170])).

tff(c_178,plain,(
    ! [B_34] :
      ( k5_relat_1(k1_xboole_0,B_34) = k1_xboole_0
      | ~ v1_relat_1(B_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_174])).

tff(c_187,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_178])).

tff(c_193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_187])).

tff(c_194,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_20,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_212,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_38,B_39)),k2_relat_1(B_39))
      | ~ v1_relat_1(B_39)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_218,plain,(
    ! [A_38] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_38,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_212])).

tff(c_223,plain,(
    ! [A_40] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_40,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_218])).

tff(c_244,plain,(
    ! [A_43] :
      ( k2_relat_1(k5_relat_1(A_43,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_43) ) ),
    inference(resolution,[status(thm)],[c_223,c_6])).

tff(c_14,plain,(
    ! [A_7] :
      ( ~ v1_xboole_0(k2_relat_1(A_7))
      | ~ v1_relat_1(A_7)
      | v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_259,plain,(
    ! [A_43] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_43,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_43,k1_xboole_0))
      | ~ v1_relat_1(A_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_14])).

tff(c_311,plain,(
    ! [A_46] :
      ( ~ v1_relat_1(k5_relat_1(A_46,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_46,k1_xboole_0))
      | ~ v1_relat_1(A_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_259])).

tff(c_334,plain,(
    ! [A_48] :
      ( k5_relat_1(A_48,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_48,k1_xboole_0))
      | ~ v1_relat_1(A_48) ) ),
    inference(resolution,[status(thm)],[c_311,c_4])).

tff(c_338,plain,(
    ! [A_4] :
      ( k5_relat_1(A_4,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_4) ) ),
    inference(resolution,[status(thm)],[c_10,c_334])).

tff(c_342,plain,(
    ! [A_49] :
      ( k5_relat_1(A_49,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_338])).

tff(c_351,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_342])).

tff(c_357,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_351])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:38:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.31  
% 2.11/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.31  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.22/1.31  
% 2.22/1.31  %Foreground sorts:
% 2.22/1.31  
% 2.22/1.31  
% 2.22/1.31  %Background operators:
% 2.22/1.31  
% 2.22/1.31  
% 2.22/1.31  %Foreground operators:
% 2.22/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.22/1.31  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.22/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.22/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.22/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.22/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.22/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.22/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.22/1.31  
% 2.22/1.33  tff(f_84, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 2.22/1.33  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.22/1.33  tff(f_38, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.22/1.33  tff(f_44, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.22/1.33  tff(f_77, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.22/1.33  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 2.22/1.33  tff(f_34, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.22/1.33  tff(f_52, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.22/1.33  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.22/1.33  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 2.22/1.33  tff(f_60, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.22/1.33  tff(c_24, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.22/1.33  tff(c_53, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_24])).
% 2.22/1.33  tff(c_26, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.22/1.33  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.22/1.33  tff(c_35, plain, (![A_14]: (v1_relat_1(A_14) | ~v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.22/1.33  tff(c_39, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_35])).
% 2.22/1.33  tff(c_10, plain, (![A_4, B_5]: (v1_relat_1(k5_relat_1(A_4, B_5)) | ~v1_relat_1(B_5) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.22/1.33  tff(c_22, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.22/1.33  tff(c_61, plain, (![A_21, B_22]: (r1_tarski(k1_relat_1(k5_relat_1(A_21, B_22)), k1_relat_1(A_21)) | ~v1_relat_1(B_22) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.22/1.33  tff(c_64, plain, (![B_22]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_22)), k1_xboole_0) | ~v1_relat_1(B_22) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_61])).
% 2.22/1.33  tff(c_67, plain, (![B_23]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_23)), k1_xboole_0) | ~v1_relat_1(B_23))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_64])).
% 2.22/1.33  tff(c_6, plain, (![A_2]: (k1_xboole_0=A_2 | ~r1_tarski(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.22/1.33  tff(c_78, plain, (![B_26]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_26))=k1_xboole_0 | ~v1_relat_1(B_26))), inference(resolution, [status(thm)], [c_67, c_6])).
% 2.22/1.33  tff(c_12, plain, (![A_6]: (~v1_xboole_0(k1_relat_1(A_6)) | ~v1_relat_1(A_6) | v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.22/1.33  tff(c_93, plain, (![B_26]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_26)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_26)) | ~v1_relat_1(B_26))), inference(superposition, [status(thm), theory('equality')], [c_78, c_12])).
% 2.22/1.33  tff(c_152, plain, (![B_31]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_31)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_31)) | ~v1_relat_1(B_31))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_93])).
% 2.22/1.33  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.22/1.33  tff(c_170, plain, (![B_33]: (k5_relat_1(k1_xboole_0, B_33)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_33)) | ~v1_relat_1(B_33))), inference(resolution, [status(thm)], [c_152, c_4])).
% 2.22/1.33  tff(c_174, plain, (![B_5]: (k5_relat_1(k1_xboole_0, B_5)=k1_xboole_0 | ~v1_relat_1(B_5) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_170])).
% 2.22/1.33  tff(c_178, plain, (![B_34]: (k5_relat_1(k1_xboole_0, B_34)=k1_xboole_0 | ~v1_relat_1(B_34))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_174])).
% 2.22/1.33  tff(c_187, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_178])).
% 2.22/1.33  tff(c_193, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_187])).
% 2.22/1.33  tff(c_194, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_24])).
% 2.22/1.33  tff(c_20, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.22/1.33  tff(c_212, plain, (![A_38, B_39]: (r1_tarski(k2_relat_1(k5_relat_1(A_38, B_39)), k2_relat_1(B_39)) | ~v1_relat_1(B_39) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.22/1.33  tff(c_218, plain, (![A_38]: (r1_tarski(k2_relat_1(k5_relat_1(A_38, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_38))), inference(superposition, [status(thm), theory('equality')], [c_20, c_212])).
% 2.22/1.33  tff(c_223, plain, (![A_40]: (r1_tarski(k2_relat_1(k5_relat_1(A_40, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_40))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_218])).
% 2.22/1.33  tff(c_244, plain, (![A_43]: (k2_relat_1(k5_relat_1(A_43, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_43))), inference(resolution, [status(thm)], [c_223, c_6])).
% 2.22/1.33  tff(c_14, plain, (![A_7]: (~v1_xboole_0(k2_relat_1(A_7)) | ~v1_relat_1(A_7) | v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.22/1.33  tff(c_259, plain, (![A_43]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_43, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_43, k1_xboole_0)) | ~v1_relat_1(A_43))), inference(superposition, [status(thm), theory('equality')], [c_244, c_14])).
% 2.22/1.33  tff(c_311, plain, (![A_46]: (~v1_relat_1(k5_relat_1(A_46, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_46, k1_xboole_0)) | ~v1_relat_1(A_46))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_259])).
% 2.22/1.33  tff(c_334, plain, (![A_48]: (k5_relat_1(A_48, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_48, k1_xboole_0)) | ~v1_relat_1(A_48))), inference(resolution, [status(thm)], [c_311, c_4])).
% 2.22/1.33  tff(c_338, plain, (![A_4]: (k5_relat_1(A_4, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_4))), inference(resolution, [status(thm)], [c_10, c_334])).
% 2.22/1.33  tff(c_342, plain, (![A_49]: (k5_relat_1(A_49, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_49))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_338])).
% 2.22/1.33  tff(c_351, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_342])).
% 2.22/1.33  tff(c_357, plain, $false, inference(negUnitSimplification, [status(thm)], [c_194, c_351])).
% 2.22/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.33  
% 2.22/1.33  Inference rules
% 2.22/1.33  ----------------------
% 2.22/1.33  #Ref     : 0
% 2.22/1.33  #Sup     : 68
% 2.22/1.33  #Fact    : 0
% 2.22/1.33  #Define  : 0
% 2.22/1.33  #Split   : 2
% 2.22/1.33  #Chain   : 0
% 2.22/1.33  #Close   : 0
% 2.22/1.33  
% 2.22/1.33  Ordering : KBO
% 2.22/1.33  
% 2.22/1.33  Simplification rules
% 2.22/1.33  ----------------------
% 2.22/1.33  #Subsume      : 9
% 2.22/1.33  #Demod        : 53
% 2.22/1.33  #Tautology    : 35
% 2.22/1.33  #SimpNegUnit  : 6
% 2.22/1.33  #BackRed      : 3
% 2.22/1.33  
% 2.22/1.33  #Partial instantiations: 0
% 2.22/1.33  #Strategies tried      : 1
% 2.22/1.33  
% 2.22/1.33  Timing (in seconds)
% 2.22/1.33  ----------------------
% 2.22/1.33  Preprocessing        : 0.28
% 2.22/1.33  Parsing              : 0.16
% 2.22/1.33  CNF conversion       : 0.02
% 2.22/1.33  Main loop            : 0.22
% 2.22/1.33  Inferencing          : 0.09
% 2.22/1.33  Reduction            : 0.06
% 2.22/1.33  Demodulation         : 0.04
% 2.22/1.33  BG Simplification    : 0.01
% 2.22/1.33  Subsumption          : 0.04
% 2.22/1.33  Abstraction          : 0.01
% 2.22/1.33  MUC search           : 0.00
% 2.22/1.33  Cooper               : 0.00
% 2.22/1.33  Total                : 0.53
% 2.22/1.33  Index Insertion      : 0.00
% 2.22/1.33  Index Deletion       : 0.00
% 2.22/1.33  Index Matching       : 0.00
% 2.22/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
