%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:53 EST 2020

% Result     : Theorem 4.25s
% Output     : CNFRefutation 4.63s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 125 expanded)
%              Number of leaves         :   22 (  53 expanded)
%              Depth                    :    8
%              Number of atoms          :  115 ( 338 expanded)
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

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
            & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_45,axiom,(
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

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_32,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_30,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_24,plain,(
    ! [A_17] :
      ( k2_relat_1(k2_funct_1(A_17)) = k1_relat_1(A_17)
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_22,plain,(
    ! [A_16] :
      ( v1_relat_1(k2_funct_1(A_16))
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [A_14] : k2_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_18,plain,(
    ! [A_15] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_15)),A_15) = A_15
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_983,plain,(
    ! [B_75,C_76,A_77] :
      ( k2_relat_1(k5_relat_1(B_75,C_76)) = k2_relat_1(k5_relat_1(A_77,C_76))
      | k2_relat_1(B_75) != k2_relat_1(A_77)
      | ~ v1_relat_1(C_76)
      | ~ v1_relat_1(B_75)
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1028,plain,(
    ! [A_77,A_15] :
      ( k2_relat_1(k5_relat_1(A_77,A_15)) = k2_relat_1(A_15)
      | k2_relat_1(k6_relat_1(k1_relat_1(A_15))) != k2_relat_1(A_77)
      | ~ v1_relat_1(A_15)
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(A_15)))
      | ~ v1_relat_1(A_77)
      | ~ v1_relat_1(A_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_983])).

tff(c_1090,plain,(
    ! [A_80,A_81] :
      ( k2_relat_1(k5_relat_1(A_80,A_81)) = k2_relat_1(A_81)
      | k2_relat_1(A_80) != k1_relat_1(A_81)
      | ~ v1_relat_1(A_80)
      | ~ v1_relat_1(A_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_16,c_1028])).

tff(c_26,plain,(
    ! [A_17] :
      ( k1_relat_1(k2_funct_1(A_17)) = k2_relat_1(A_17)
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_110,plain,(
    ! [A_30,B_31] :
      ( k1_relat_1(k5_relat_1(A_30,B_31)) = k1_relat_1(A_30)
      | ~ r1_tarski(k2_relat_1(A_30),k1_relat_1(B_31))
      | ~ v1_relat_1(B_31)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_703,plain,(
    ! [A_58,B_59] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(A_58),B_59)) = k1_relat_1(k2_funct_1(A_58))
      | ~ r1_tarski(k1_relat_1(A_58),k1_relat_1(B_59))
      | ~ v1_relat_1(B_59)
      | ~ v1_relat_1(k2_funct_1(A_58))
      | ~ v2_funct_1(A_58)
      | ~ v1_funct_1(A_58)
      | ~ v1_relat_1(A_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_110])).

tff(c_781,plain,(
    ! [A_62] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(A_62),A_62)) = k1_relat_1(k2_funct_1(A_62))
      | ~ v1_relat_1(k2_funct_1(A_62))
      | ~ v2_funct_1(A_62)
      | ~ v1_funct_1(A_62)
      | ~ v1_relat_1(A_62) ) ),
    inference(resolution,[status(thm)],[c_6,c_703])).

tff(c_28,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_58,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_803,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_781,c_58])).

tff(c_816,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_803])).

tff(c_821,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_816])).

tff(c_824,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_821])).

tff(c_828,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_824])).

tff(c_829,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_816])).

tff(c_833,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_829])).

tff(c_837,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_833])).

tff(c_838,plain,(
    k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_1109,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1090,c_838])).

tff(c_1133,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1109])).

tff(c_1142,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1133])).

tff(c_1145,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_1142])).

tff(c_1149,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1145])).

tff(c_1150,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1133])).

tff(c_1154,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1150])).

tff(c_1158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_1154])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:30:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.25/2.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.25/2.07  
% 4.25/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.25/2.07  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 4.25/2.07  
% 4.25/2.07  %Foreground sorts:
% 4.25/2.07  
% 4.25/2.07  
% 4.25/2.07  %Background operators:
% 4.25/2.07  
% 4.25/2.07  
% 4.25/2.07  %Foreground operators:
% 4.25/2.07  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.25/2.07  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.25/2.07  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.25/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.25/2.07  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.25/2.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.25/2.07  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.25/2.07  tff('#skF_1', type, '#skF_1': $i).
% 4.25/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.25/2.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.25/2.07  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.25/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.25/2.07  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.25/2.07  
% 4.63/2.09  tff(f_91, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_funct_1)).
% 4.63/2.09  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 4.63/2.09  tff(f_70, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 4.63/2.09  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 4.63/2.09  tff(f_58, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 4.63/2.09  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 4.63/2.09  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k2_relat_1(A) = k2_relat_1(B)) => (k2_relat_1(k5_relat_1(A, C)) = k2_relat_1(k5_relat_1(B, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t199_relat_1)).
% 4.63/2.09  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.63/2.09  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 4.63/2.09  tff(c_34, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.63/2.09  tff(c_32, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.63/2.09  tff(c_30, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.63/2.09  tff(c_24, plain, (![A_17]: (k2_relat_1(k2_funct_1(A_17))=k1_relat_1(A_17) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.63/2.09  tff(c_22, plain, (![A_16]: (v1_relat_1(k2_funct_1(A_16)) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.63/2.09  tff(c_8, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.63/2.09  tff(c_16, plain, (![A_14]: (k2_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.63/2.09  tff(c_18, plain, (![A_15]: (k5_relat_1(k6_relat_1(k1_relat_1(A_15)), A_15)=A_15 | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.63/2.09  tff(c_983, plain, (![B_75, C_76, A_77]: (k2_relat_1(k5_relat_1(B_75, C_76))=k2_relat_1(k5_relat_1(A_77, C_76)) | k2_relat_1(B_75)!=k2_relat_1(A_77) | ~v1_relat_1(C_76) | ~v1_relat_1(B_75) | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.63/2.09  tff(c_1028, plain, (![A_77, A_15]: (k2_relat_1(k5_relat_1(A_77, A_15))=k2_relat_1(A_15) | k2_relat_1(k6_relat_1(k1_relat_1(A_15)))!=k2_relat_1(A_77) | ~v1_relat_1(A_15) | ~v1_relat_1(k6_relat_1(k1_relat_1(A_15))) | ~v1_relat_1(A_77) | ~v1_relat_1(A_15))), inference(superposition, [status(thm), theory('equality')], [c_18, c_983])).
% 4.63/2.09  tff(c_1090, plain, (![A_80, A_81]: (k2_relat_1(k5_relat_1(A_80, A_81))=k2_relat_1(A_81) | k2_relat_1(A_80)!=k1_relat_1(A_81) | ~v1_relat_1(A_80) | ~v1_relat_1(A_81))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_16, c_1028])).
% 4.63/2.09  tff(c_26, plain, (![A_17]: (k1_relat_1(k2_funct_1(A_17))=k2_relat_1(A_17) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.63/2.09  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.63/2.09  tff(c_110, plain, (![A_30, B_31]: (k1_relat_1(k5_relat_1(A_30, B_31))=k1_relat_1(A_30) | ~r1_tarski(k2_relat_1(A_30), k1_relat_1(B_31)) | ~v1_relat_1(B_31) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.63/2.09  tff(c_703, plain, (![A_58, B_59]: (k1_relat_1(k5_relat_1(k2_funct_1(A_58), B_59))=k1_relat_1(k2_funct_1(A_58)) | ~r1_tarski(k1_relat_1(A_58), k1_relat_1(B_59)) | ~v1_relat_1(B_59) | ~v1_relat_1(k2_funct_1(A_58)) | ~v2_funct_1(A_58) | ~v1_funct_1(A_58) | ~v1_relat_1(A_58))), inference(superposition, [status(thm), theory('equality')], [c_24, c_110])).
% 4.63/2.09  tff(c_781, plain, (![A_62]: (k1_relat_1(k5_relat_1(k2_funct_1(A_62), A_62))=k1_relat_1(k2_funct_1(A_62)) | ~v1_relat_1(k2_funct_1(A_62)) | ~v2_funct_1(A_62) | ~v1_funct_1(A_62) | ~v1_relat_1(A_62))), inference(resolution, [status(thm)], [c_6, c_703])).
% 4.63/2.09  tff(c_28, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1') | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.63/2.09  tff(c_58, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_28])).
% 4.63/2.09  tff(c_803, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_781, c_58])).
% 4.63/2.09  tff(c_816, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_803])).
% 4.63/2.09  tff(c_821, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_816])).
% 4.63/2.09  tff(c_824, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_22, c_821])).
% 4.63/2.09  tff(c_828, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_824])).
% 4.63/2.09  tff(c_829, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_816])).
% 4.63/2.09  tff(c_833, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_26, c_829])).
% 4.63/2.09  tff(c_837, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_833])).
% 4.63/2.09  tff(c_838, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_28])).
% 4.63/2.09  tff(c_1109, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1090, c_838])).
% 4.63/2.09  tff(c_1133, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1109])).
% 4.63/2.09  tff(c_1142, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_1133])).
% 4.63/2.09  tff(c_1145, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_22, c_1142])).
% 4.63/2.09  tff(c_1149, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1145])).
% 4.63/2.09  tff(c_1150, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_1133])).
% 4.63/2.09  tff(c_1154, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_24, c_1150])).
% 4.63/2.09  tff(c_1158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_1154])).
% 4.63/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.63/2.09  
% 4.63/2.09  Inference rules
% 4.63/2.09  ----------------------
% 4.63/2.09  #Ref     : 2
% 4.63/2.09  #Sup     : 264
% 4.63/2.09  #Fact    : 0
% 4.63/2.09  #Define  : 0
% 4.63/2.09  #Split   : 4
% 4.63/2.09  #Chain   : 0
% 4.63/2.09  #Close   : 0
% 4.63/2.09  
% 4.63/2.09  Ordering : KBO
% 4.63/2.09  
% 4.63/2.09  Simplification rules
% 4.63/2.09  ----------------------
% 4.63/2.09  #Subsume      : 17
% 4.63/2.09  #Demod        : 240
% 4.63/2.09  #Tautology    : 101
% 4.63/2.09  #SimpNegUnit  : 0
% 4.63/2.09  #BackRed      : 0
% 4.63/2.09  
% 4.63/2.09  #Partial instantiations: 0
% 4.63/2.09  #Strategies tried      : 1
% 4.63/2.09  
% 4.63/2.09  Timing (in seconds)
% 4.63/2.09  ----------------------
% 4.63/2.09  Preprocessing        : 0.49
% 4.63/2.09  Parsing              : 0.27
% 4.63/2.09  CNF conversion       : 0.03
% 4.63/2.09  Main loop            : 0.75
% 4.63/2.09  Inferencing          : 0.27
% 4.63/2.09  Reduction            : 0.23
% 4.63/2.09  Demodulation         : 0.17
% 4.63/2.09  BG Simplification    : 0.05
% 4.63/2.09  Subsumption          : 0.15
% 4.63/2.10  Abstraction          : 0.04
% 4.63/2.10  MUC search           : 0.00
% 4.63/2.10  Cooper               : 0.00
% 4.63/2.10  Total                : 1.28
% 4.63/2.10  Index Insertion      : 0.00
% 4.63/2.10  Index Deletion       : 0.00
% 4.63/2.10  Index Matching       : 0.00
% 4.63/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
