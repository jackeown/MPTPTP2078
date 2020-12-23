%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:54 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 125 expanded)
%              Number of leaves         :   22 (  53 expanded)
%              Depth                    :    8
%              Number of atoms          :  116 ( 340 expanded)
%              Number of equality atoms :   34 ( 114 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
            & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_56,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( k2_relat_1(A) = k2_relat_1(B)
               => k2_relat_1(k5_relat_1(A,C)) = k2_relat_1(k5_relat_1(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t199_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_34,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_32,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_26,plain,(
    ! [A_17] :
      ( k2_relat_1(k2_funct_1(A_17)) = k1_relat_1(A_17)
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_20,plain,(
    ! [A_15] :
      ( v1_relat_1(k2_funct_1(A_15))
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_22,plain,(
    ! [A_16] : v1_relat_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_14,plain,(
    ! [A_13] : k2_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_16,plain,(
    ! [A_14] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_14)),A_14) = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1289,plain,(
    ! [B_86,C_87,A_88] :
      ( k2_relat_1(k5_relat_1(B_86,C_87)) = k2_relat_1(k5_relat_1(A_88,C_87))
      | k2_relat_1(B_86) != k2_relat_1(A_88)
      | ~ v1_relat_1(C_87)
      | ~ v1_relat_1(B_86)
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1346,plain,(
    ! [A_88,A_14] :
      ( k2_relat_1(k5_relat_1(A_88,A_14)) = k2_relat_1(A_14)
      | k2_relat_1(k6_relat_1(k1_relat_1(A_14))) != k2_relat_1(A_88)
      | ~ v1_relat_1(A_14)
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(A_14)))
      | ~ v1_relat_1(A_88)
      | ~ v1_relat_1(A_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1289])).

tff(c_1415,plain,(
    ! [A_91,A_92] :
      ( k2_relat_1(k5_relat_1(A_91,A_92)) = k2_relat_1(A_92)
      | k2_relat_1(A_91) != k1_relat_1(A_92)
      | ~ v1_relat_1(A_91)
      | ~ v1_relat_1(A_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_14,c_1346])).

tff(c_28,plain,(
    ! [A_17] :
      ( k1_relat_1(k2_funct_1(A_17)) = k2_relat_1(A_17)
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_113,plain,(
    ! [A_31,B_32] :
      ( k1_relat_1(k5_relat_1(A_31,B_32)) = k1_relat_1(A_31)
      | ~ r1_tarski(k2_relat_1(A_31),k1_relat_1(B_32))
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_995,plain,(
    ! [A_69,B_70] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(A_69),B_70)) = k1_relat_1(k2_funct_1(A_69))
      | ~ r1_tarski(k1_relat_1(A_69),k1_relat_1(B_70))
      | ~ v1_relat_1(B_70)
      | ~ v1_relat_1(k2_funct_1(A_69))
      | ~ v2_funct_1(A_69)
      | ~ v1_funct_1(A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_113])).

tff(c_1053,plain,(
    ! [A_71] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(A_71),A_71)) = k1_relat_1(k2_funct_1(A_71))
      | ~ v1_relat_1(k2_funct_1(A_71))
      | ~ v2_funct_1(A_71)
      | ~ v1_funct_1(A_71)
      | ~ v1_relat_1(A_71) ) ),
    inference(resolution,[status(thm)],[c_6,c_995])).

tff(c_30,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_60,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_1082,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1053,c_60])).

tff(c_1100,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_1082])).

tff(c_1106,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1100])).

tff(c_1109,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_1106])).

tff(c_1113,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_1109])).

tff(c_1114,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1100])).

tff(c_1118,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1114])).

tff(c_1122,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_1118])).

tff(c_1123,plain,(
    k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_1437,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1415,c_1123])).

tff(c_1464,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1437])).

tff(c_1476,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1464])).

tff(c_1479,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_1476])).

tff(c_1483,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_1479])).

tff(c_1484,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1464])).

tff(c_1488,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1484])).

tff(c_1492,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_1488])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:33:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.60/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/1.58  
% 3.60/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/1.58  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 3.60/1.58  
% 3.60/1.58  %Foreground sorts:
% 3.60/1.58  
% 3.60/1.58  
% 3.60/1.58  %Background operators:
% 3.60/1.58  
% 3.60/1.58  
% 3.60/1.58  %Foreground operators:
% 3.60/1.58  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.60/1.58  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.60/1.58  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.60/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.60/1.58  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.60/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.60/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.60/1.58  tff('#skF_1', type, '#skF_1': $i).
% 3.60/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.60/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.60/1.58  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.60/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.60/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.60/1.58  
% 3.60/1.59  tff(f_93, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_funct_1)).
% 3.60/1.59  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 3.60/1.59  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.60/1.59  tff(f_72, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.60/1.59  tff(f_56, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.60/1.59  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 3.60/1.59  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k2_relat_1(A) = k2_relat_1(B)) => (k2_relat_1(k5_relat_1(A, C)) = k2_relat_1(k5_relat_1(B, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t199_relat_1)).
% 3.60/1.59  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.60/1.59  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 3.60/1.59  tff(c_36, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.60/1.59  tff(c_34, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.60/1.60  tff(c_32, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.60/1.60  tff(c_26, plain, (![A_17]: (k2_relat_1(k2_funct_1(A_17))=k1_relat_1(A_17) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.60/1.60  tff(c_20, plain, (![A_15]: (v1_relat_1(k2_funct_1(A_15)) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.60/1.60  tff(c_22, plain, (![A_16]: (v1_relat_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.60/1.60  tff(c_14, plain, (![A_13]: (k2_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.60/1.60  tff(c_16, plain, (![A_14]: (k5_relat_1(k6_relat_1(k1_relat_1(A_14)), A_14)=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.60/1.60  tff(c_1289, plain, (![B_86, C_87, A_88]: (k2_relat_1(k5_relat_1(B_86, C_87))=k2_relat_1(k5_relat_1(A_88, C_87)) | k2_relat_1(B_86)!=k2_relat_1(A_88) | ~v1_relat_1(C_87) | ~v1_relat_1(B_86) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.60/1.60  tff(c_1346, plain, (![A_88, A_14]: (k2_relat_1(k5_relat_1(A_88, A_14))=k2_relat_1(A_14) | k2_relat_1(k6_relat_1(k1_relat_1(A_14)))!=k2_relat_1(A_88) | ~v1_relat_1(A_14) | ~v1_relat_1(k6_relat_1(k1_relat_1(A_14))) | ~v1_relat_1(A_88) | ~v1_relat_1(A_14))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1289])).
% 3.60/1.60  tff(c_1415, plain, (![A_91, A_92]: (k2_relat_1(k5_relat_1(A_91, A_92))=k2_relat_1(A_92) | k2_relat_1(A_91)!=k1_relat_1(A_92) | ~v1_relat_1(A_91) | ~v1_relat_1(A_92))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_14, c_1346])).
% 3.60/1.60  tff(c_28, plain, (![A_17]: (k1_relat_1(k2_funct_1(A_17))=k2_relat_1(A_17) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.60/1.60  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.60/1.60  tff(c_113, plain, (![A_31, B_32]: (k1_relat_1(k5_relat_1(A_31, B_32))=k1_relat_1(A_31) | ~r1_tarski(k2_relat_1(A_31), k1_relat_1(B_32)) | ~v1_relat_1(B_32) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.60/1.60  tff(c_995, plain, (![A_69, B_70]: (k1_relat_1(k5_relat_1(k2_funct_1(A_69), B_70))=k1_relat_1(k2_funct_1(A_69)) | ~r1_tarski(k1_relat_1(A_69), k1_relat_1(B_70)) | ~v1_relat_1(B_70) | ~v1_relat_1(k2_funct_1(A_69)) | ~v2_funct_1(A_69) | ~v1_funct_1(A_69) | ~v1_relat_1(A_69))), inference(superposition, [status(thm), theory('equality')], [c_26, c_113])).
% 3.60/1.60  tff(c_1053, plain, (![A_71]: (k1_relat_1(k5_relat_1(k2_funct_1(A_71), A_71))=k1_relat_1(k2_funct_1(A_71)) | ~v1_relat_1(k2_funct_1(A_71)) | ~v2_funct_1(A_71) | ~v1_funct_1(A_71) | ~v1_relat_1(A_71))), inference(resolution, [status(thm)], [c_6, c_995])).
% 3.60/1.60  tff(c_30, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1') | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.60/1.60  tff(c_60, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_30])).
% 3.60/1.60  tff(c_1082, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1053, c_60])).
% 3.60/1.60  tff(c_1100, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_1082])).
% 3.60/1.60  tff(c_1106, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_1100])).
% 3.60/1.60  tff(c_1109, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_20, c_1106])).
% 3.60/1.60  tff(c_1113, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_1109])).
% 3.60/1.60  tff(c_1114, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_1100])).
% 3.60/1.60  tff(c_1118, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_28, c_1114])).
% 3.60/1.60  tff(c_1122, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_1118])).
% 3.60/1.60  tff(c_1123, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_30])).
% 3.60/1.60  tff(c_1437, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1415, c_1123])).
% 3.60/1.60  tff(c_1464, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1437])).
% 3.60/1.60  tff(c_1476, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_1464])).
% 3.60/1.60  tff(c_1479, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_20, c_1476])).
% 3.60/1.60  tff(c_1483, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_1479])).
% 3.60/1.60  tff(c_1484, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_1464])).
% 3.60/1.60  tff(c_1488, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_26, c_1484])).
% 3.60/1.60  tff(c_1492, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_1488])).
% 3.60/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/1.60  
% 3.60/1.60  Inference rules
% 3.60/1.60  ----------------------
% 3.60/1.60  #Ref     : 1
% 3.60/1.60  #Sup     : 332
% 3.60/1.60  #Fact    : 0
% 3.60/1.60  #Define  : 0
% 3.60/1.60  #Split   : 4
% 3.60/1.60  #Chain   : 0
% 3.60/1.60  #Close   : 0
% 3.60/1.60  
% 3.60/1.60  Ordering : KBO
% 3.60/1.60  
% 3.60/1.60  Simplification rules
% 3.60/1.60  ----------------------
% 3.60/1.60  #Subsume      : 23
% 3.60/1.60  #Demod        : 360
% 3.60/1.60  #Tautology    : 143
% 3.60/1.60  #SimpNegUnit  : 0
% 3.60/1.60  #BackRed      : 0
% 3.60/1.60  
% 3.60/1.60  #Partial instantiations: 0
% 3.60/1.60  #Strategies tried      : 1
% 3.60/1.60  
% 3.60/1.60  Timing (in seconds)
% 3.60/1.60  ----------------------
% 3.60/1.60  Preprocessing        : 0.29
% 3.60/1.60  Parsing              : 0.16
% 3.60/1.60  CNF conversion       : 0.02
% 3.60/1.60  Main loop            : 0.54
% 3.60/1.60  Inferencing          : 0.20
% 3.60/1.60  Reduction            : 0.17
% 3.60/1.60  Demodulation         : 0.12
% 3.60/1.60  BG Simplification    : 0.03
% 3.60/1.60  Subsumption          : 0.11
% 3.60/1.60  Abstraction          : 0.04
% 3.60/1.60  MUC search           : 0.00
% 3.60/1.60  Cooper               : 0.00
% 3.60/1.60  Total                : 0.86
% 3.60/1.60  Index Insertion      : 0.00
% 3.60/1.60  Index Deletion       : 0.00
% 3.60/1.60  Index Matching       : 0.00
% 3.60/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
