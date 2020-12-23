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
% DateTime   : Thu Dec  3 09:59:07 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 184 expanded)
%              Number of leaves         :   24 (  72 expanded)
%              Depth                    :   13
%              Number of atoms          :  129 ( 294 expanded)
%              Number of equality atoms :   34 (  96 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_31,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_82,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_57,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_4,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    ! [A_18] :
      ( k1_xboole_0 = A_18
      | ~ v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_44])).

tff(c_30,plain,
    ( k5_relat_1('#skF_2',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_61,plain,
    ( k5_relat_1('#skF_2','#skF_1') != '#skF_1'
    | k5_relat_1('#skF_1','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_48,c_48,c_30])).

tff(c_62,plain,(
    k5_relat_1('#skF_1','#skF_2') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_61])).

tff(c_32,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_68,plain,(
    ! [A_20] :
      ( v1_relat_1(A_20)
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_72,plain,(
    v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_68])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k5_relat_1(A_6,B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_50,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_28])).

tff(c_160,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_33,B_34)),k1_relat_1(A_33))
      | ~ v1_relat_1(B_34)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_165,plain,(
    ! [B_34] :
      ( r1_tarski(k1_relat_1(k5_relat_1('#skF_1',B_34)),'#skF_1')
      | ~ v1_relat_1(B_34)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_160])).

tff(c_169,plain,(
    ! [B_35] :
      ( r1_tarski(k1_relat_1(k5_relat_1('#skF_1',B_35)),'#skF_1')
      | ~ v1_relat_1(B_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_165])).

tff(c_12,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_51,plain,(
    ! [A_4] : r1_tarski('#skF_1',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_12])).

tff(c_92,plain,(
    ! [B_26,A_27] :
      ( B_26 = A_27
      | ~ r1_tarski(B_26,A_27)
      | ~ r1_tarski(A_27,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_97,plain,(
    ! [A_4] :
      ( A_4 = '#skF_1'
      | ~ r1_tarski(A_4,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_51,c_92])).

tff(c_179,plain,(
    ! [B_36] :
      ( k1_relat_1(k5_relat_1('#skF_1',B_36)) = '#skF_1'
      | ~ v1_relat_1(B_36) ) ),
    inference(resolution,[status(thm)],[c_169,c_97])).

tff(c_18,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(k1_relat_1(A_8))
      | ~ v1_relat_1(A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_194,plain,(
    ! [B_36] :
      ( ~ v1_xboole_0('#skF_1')
      | ~ v1_relat_1(k5_relat_1('#skF_1',B_36))
      | v1_xboole_0(k5_relat_1('#skF_1',B_36))
      | ~ v1_relat_1(B_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_18])).

tff(c_224,plain,(
    ! [B_40] :
      ( ~ v1_relat_1(k5_relat_1('#skF_1',B_40))
      | v1_xboole_0(k5_relat_1('#skF_1',B_40))
      | ~ v1_relat_1(B_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_194])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_49,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2])).

tff(c_373,plain,(
    ! [B_45] :
      ( k5_relat_1('#skF_1',B_45) = '#skF_1'
      | ~ v1_relat_1(k5_relat_1('#skF_1',B_45))
      | ~ v1_relat_1(B_45) ) ),
    inference(resolution,[status(thm)],[c_224,c_49])).

tff(c_380,plain,(
    ! [B_7] :
      ( k5_relat_1('#skF_1',B_7) = '#skF_1'
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_16,c_373])).

tff(c_386,plain,(
    ! [B_46] :
      ( k5_relat_1('#skF_1',B_46) = '#skF_1'
      | ~ v1_relat_1(B_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_380])).

tff(c_395,plain,(
    k5_relat_1('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32,c_386])).

tff(c_402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_395])).

tff(c_403,plain,(
    k5_relat_1('#skF_2','#skF_1') != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_410,plain,(
    ! [A_48] :
      ( v1_relat_1(A_48)
      | ~ v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_414,plain,(
    v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_410])).

tff(c_26,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_52,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_26])).

tff(c_466,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_57,B_58)),k2_relat_1(B_58))
      | ~ v1_relat_1(B_58)
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_474,plain,(
    ! [A_57] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_57,'#skF_1')),'#skF_1')
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(A_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_466])).

tff(c_480,plain,(
    ! [A_59] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_59,'#skF_1')),'#skF_1')
      | ~ v1_relat_1(A_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_414,c_474])).

tff(c_443,plain,(
    ! [B_54,A_55] :
      ( B_54 = A_55
      | ~ r1_tarski(B_54,A_55)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_448,plain,(
    ! [A_4] :
      ( A_4 = '#skF_1'
      | ~ r1_tarski(A_4,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_51,c_443])).

tff(c_490,plain,(
    ! [A_60] :
      ( k2_relat_1(k5_relat_1(A_60,'#skF_1')) = '#skF_1'
      | ~ v1_relat_1(A_60) ) ),
    inference(resolution,[status(thm)],[c_480,c_448])).

tff(c_20,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(k2_relat_1(A_9))
      | ~ v1_relat_1(A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_505,plain,(
    ! [A_60] :
      ( ~ v1_xboole_0('#skF_1')
      | ~ v1_relat_1(k5_relat_1(A_60,'#skF_1'))
      | v1_xboole_0(k5_relat_1(A_60,'#skF_1'))
      | ~ v1_relat_1(A_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_490,c_20])).

tff(c_586,plain,(
    ! [A_67] :
      ( ~ v1_relat_1(k5_relat_1(A_67,'#skF_1'))
      | v1_xboole_0(k5_relat_1(A_67,'#skF_1'))
      | ~ v1_relat_1(A_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_505])).

tff(c_609,plain,(
    ! [A_69] :
      ( k5_relat_1(A_69,'#skF_1') = '#skF_1'
      | ~ v1_relat_1(k5_relat_1(A_69,'#skF_1'))
      | ~ v1_relat_1(A_69) ) ),
    inference(resolution,[status(thm)],[c_586,c_49])).

tff(c_613,plain,(
    ! [A_6] :
      ( k5_relat_1(A_6,'#skF_1') = '#skF_1'
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(A_6) ) ),
    inference(resolution,[status(thm)],[c_16,c_609])).

tff(c_617,plain,(
    ! [A_70] :
      ( k5_relat_1(A_70,'#skF_1') = '#skF_1'
      | ~ v1_relat_1(A_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_414,c_613])).

tff(c_626,plain,(
    k5_relat_1('#skF_2','#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32,c_617])).

tff(c_632,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_403,c_626])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:45:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.49  
% 2.69/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.49  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.69/1.49  
% 2.69/1.49  %Foreground sorts:
% 2.69/1.49  
% 2.69/1.49  
% 2.69/1.49  %Background operators:
% 2.69/1.49  
% 2.69/1.49  
% 2.69/1.49  %Foreground operators:
% 2.69/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.69/1.49  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.69/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.69/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.69/1.49  tff('#skF_2', type, '#skF_2': $i).
% 2.69/1.49  tff('#skF_1', type, '#skF_1': $i).
% 2.69/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.69/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.69/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.69/1.49  
% 2.69/1.50  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 2.69/1.50  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.69/1.50  tff(f_89, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 2.69/1.50  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.69/1.50  tff(f_49, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.69/1.50  tff(f_82, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.69/1.50  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 2.69/1.50  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.69/1.50  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.69/1.50  tff(f_57, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.69/1.50  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 2.69/1.50  tff(f_65, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.69/1.50  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.69/1.50  tff(c_44, plain, (![A_18]: (k1_xboole_0=A_18 | ~v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.69/1.50  tff(c_48, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4, c_44])).
% 2.69/1.50  tff(c_30, plain, (k5_relat_1('#skF_2', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.69/1.50  tff(c_61, plain, (k5_relat_1('#skF_2', '#skF_1')!='#skF_1' | k5_relat_1('#skF_1', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_48, c_48, c_30])).
% 2.69/1.50  tff(c_62, plain, (k5_relat_1('#skF_1', '#skF_2')!='#skF_1'), inference(splitLeft, [status(thm)], [c_61])).
% 2.69/1.50  tff(c_32, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.69/1.50  tff(c_68, plain, (![A_20]: (v1_relat_1(A_20) | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.69/1.50  tff(c_72, plain, (v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_4, c_68])).
% 2.69/1.50  tff(c_16, plain, (![A_6, B_7]: (v1_relat_1(k5_relat_1(A_6, B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.69/1.50  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.69/1.50  tff(c_50, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_28])).
% 2.69/1.50  tff(c_160, plain, (![A_33, B_34]: (r1_tarski(k1_relat_1(k5_relat_1(A_33, B_34)), k1_relat_1(A_33)) | ~v1_relat_1(B_34) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.69/1.50  tff(c_165, plain, (![B_34]: (r1_tarski(k1_relat_1(k5_relat_1('#skF_1', B_34)), '#skF_1') | ~v1_relat_1(B_34) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_160])).
% 2.69/1.50  tff(c_169, plain, (![B_35]: (r1_tarski(k1_relat_1(k5_relat_1('#skF_1', B_35)), '#skF_1') | ~v1_relat_1(B_35))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_165])).
% 2.69/1.50  tff(c_12, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.69/1.50  tff(c_51, plain, (![A_4]: (r1_tarski('#skF_1', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_12])).
% 2.69/1.50  tff(c_92, plain, (![B_26, A_27]: (B_26=A_27 | ~r1_tarski(B_26, A_27) | ~r1_tarski(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.69/1.50  tff(c_97, plain, (![A_4]: (A_4='#skF_1' | ~r1_tarski(A_4, '#skF_1'))), inference(resolution, [status(thm)], [c_51, c_92])).
% 2.69/1.50  tff(c_179, plain, (![B_36]: (k1_relat_1(k5_relat_1('#skF_1', B_36))='#skF_1' | ~v1_relat_1(B_36))), inference(resolution, [status(thm)], [c_169, c_97])).
% 2.69/1.50  tff(c_18, plain, (![A_8]: (~v1_xboole_0(k1_relat_1(A_8)) | ~v1_relat_1(A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.69/1.50  tff(c_194, plain, (![B_36]: (~v1_xboole_0('#skF_1') | ~v1_relat_1(k5_relat_1('#skF_1', B_36)) | v1_xboole_0(k5_relat_1('#skF_1', B_36)) | ~v1_relat_1(B_36))), inference(superposition, [status(thm), theory('equality')], [c_179, c_18])).
% 2.69/1.50  tff(c_224, plain, (![B_40]: (~v1_relat_1(k5_relat_1('#skF_1', B_40)) | v1_xboole_0(k5_relat_1('#skF_1', B_40)) | ~v1_relat_1(B_40))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_194])).
% 2.69/1.50  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.69/1.50  tff(c_49, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2])).
% 2.69/1.50  tff(c_373, plain, (![B_45]: (k5_relat_1('#skF_1', B_45)='#skF_1' | ~v1_relat_1(k5_relat_1('#skF_1', B_45)) | ~v1_relat_1(B_45))), inference(resolution, [status(thm)], [c_224, c_49])).
% 2.69/1.50  tff(c_380, plain, (![B_7]: (k5_relat_1('#skF_1', B_7)='#skF_1' | ~v1_relat_1(B_7) | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_16, c_373])).
% 2.69/1.50  tff(c_386, plain, (![B_46]: (k5_relat_1('#skF_1', B_46)='#skF_1' | ~v1_relat_1(B_46))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_380])).
% 2.69/1.50  tff(c_395, plain, (k5_relat_1('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_32, c_386])).
% 2.69/1.50  tff(c_402, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_395])).
% 2.69/1.50  tff(c_403, plain, (k5_relat_1('#skF_2', '#skF_1')!='#skF_1'), inference(splitRight, [status(thm)], [c_61])).
% 2.69/1.50  tff(c_410, plain, (![A_48]: (v1_relat_1(A_48) | ~v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.69/1.50  tff(c_414, plain, (v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_4, c_410])).
% 2.69/1.50  tff(c_26, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.69/1.50  tff(c_52, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_26])).
% 2.69/1.50  tff(c_466, plain, (![A_57, B_58]: (r1_tarski(k2_relat_1(k5_relat_1(A_57, B_58)), k2_relat_1(B_58)) | ~v1_relat_1(B_58) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.69/1.50  tff(c_474, plain, (![A_57]: (r1_tarski(k2_relat_1(k5_relat_1(A_57, '#skF_1')), '#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(A_57))), inference(superposition, [status(thm), theory('equality')], [c_52, c_466])).
% 2.69/1.51  tff(c_480, plain, (![A_59]: (r1_tarski(k2_relat_1(k5_relat_1(A_59, '#skF_1')), '#skF_1') | ~v1_relat_1(A_59))), inference(demodulation, [status(thm), theory('equality')], [c_414, c_474])).
% 2.69/1.51  tff(c_443, plain, (![B_54, A_55]: (B_54=A_55 | ~r1_tarski(B_54, A_55) | ~r1_tarski(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.69/1.51  tff(c_448, plain, (![A_4]: (A_4='#skF_1' | ~r1_tarski(A_4, '#skF_1'))), inference(resolution, [status(thm)], [c_51, c_443])).
% 2.69/1.51  tff(c_490, plain, (![A_60]: (k2_relat_1(k5_relat_1(A_60, '#skF_1'))='#skF_1' | ~v1_relat_1(A_60))), inference(resolution, [status(thm)], [c_480, c_448])).
% 2.69/1.51  tff(c_20, plain, (![A_9]: (~v1_xboole_0(k2_relat_1(A_9)) | ~v1_relat_1(A_9) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.69/1.51  tff(c_505, plain, (![A_60]: (~v1_xboole_0('#skF_1') | ~v1_relat_1(k5_relat_1(A_60, '#skF_1')) | v1_xboole_0(k5_relat_1(A_60, '#skF_1')) | ~v1_relat_1(A_60))), inference(superposition, [status(thm), theory('equality')], [c_490, c_20])).
% 2.69/1.51  tff(c_586, plain, (![A_67]: (~v1_relat_1(k5_relat_1(A_67, '#skF_1')) | v1_xboole_0(k5_relat_1(A_67, '#skF_1')) | ~v1_relat_1(A_67))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_505])).
% 2.69/1.51  tff(c_609, plain, (![A_69]: (k5_relat_1(A_69, '#skF_1')='#skF_1' | ~v1_relat_1(k5_relat_1(A_69, '#skF_1')) | ~v1_relat_1(A_69))), inference(resolution, [status(thm)], [c_586, c_49])).
% 2.69/1.51  tff(c_613, plain, (![A_6]: (k5_relat_1(A_6, '#skF_1')='#skF_1' | ~v1_relat_1('#skF_1') | ~v1_relat_1(A_6))), inference(resolution, [status(thm)], [c_16, c_609])).
% 2.69/1.51  tff(c_617, plain, (![A_70]: (k5_relat_1(A_70, '#skF_1')='#skF_1' | ~v1_relat_1(A_70))), inference(demodulation, [status(thm), theory('equality')], [c_414, c_613])).
% 2.69/1.51  tff(c_626, plain, (k5_relat_1('#skF_2', '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_32, c_617])).
% 2.69/1.51  tff(c_632, plain, $false, inference(negUnitSimplification, [status(thm)], [c_403, c_626])).
% 2.69/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.51  
% 2.69/1.51  Inference rules
% 2.69/1.51  ----------------------
% 2.69/1.51  #Ref     : 0
% 2.69/1.51  #Sup     : 128
% 2.69/1.51  #Fact    : 0
% 2.69/1.51  #Define  : 0
% 2.69/1.51  #Split   : 1
% 2.69/1.51  #Chain   : 0
% 2.69/1.51  #Close   : 0
% 2.69/1.51  
% 2.69/1.51  Ordering : KBO
% 2.69/1.51  
% 2.69/1.51  Simplification rules
% 2.69/1.51  ----------------------
% 2.69/1.51  #Subsume      : 11
% 2.69/1.51  #Demod        : 153
% 2.69/1.51  #Tautology    : 76
% 2.69/1.51  #SimpNegUnit  : 2
% 2.69/1.51  #BackRed      : 4
% 2.69/1.51  
% 2.69/1.51  #Partial instantiations: 0
% 2.69/1.51  #Strategies tried      : 1
% 2.69/1.51  
% 2.69/1.51  Timing (in seconds)
% 2.69/1.51  ----------------------
% 2.82/1.51  Preprocessing        : 0.35
% 2.82/1.51  Parsing              : 0.19
% 2.82/1.51  CNF conversion       : 0.02
% 2.82/1.51  Main loop            : 0.30
% 2.82/1.51  Inferencing          : 0.12
% 2.82/1.51  Reduction            : 0.09
% 2.82/1.51  Demodulation         : 0.06
% 2.82/1.51  BG Simplification    : 0.02
% 2.82/1.51  Subsumption          : 0.06
% 2.82/1.51  Abstraction          : 0.01
% 2.82/1.51  MUC search           : 0.00
% 2.82/1.51  Cooper               : 0.00
% 2.82/1.51  Total                : 0.69
% 2.82/1.51  Index Insertion      : 0.00
% 2.82/1.51  Index Deletion       : 0.00
% 2.82/1.51  Index Matching       : 0.00
% 2.82/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
