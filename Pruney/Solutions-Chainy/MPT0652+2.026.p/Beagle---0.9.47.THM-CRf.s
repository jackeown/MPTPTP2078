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
% DateTime   : Thu Dec  3 10:03:55 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 176 expanded)
%              Number of leaves         :   23 (  72 expanded)
%              Depth                    :   11
%              Number of atoms          :  108 ( 429 expanded)
%              Number of equality atoms :   39 ( 151 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k10_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
            & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_24,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_95,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_30,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_28,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_26,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_103,plain,(
    ! [A_23] :
      ( k4_relat_1(A_23) = k2_funct_1(A_23)
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_106,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_103])).

tff(c_109,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_106])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_relat_1(k4_relat_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_122,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_2])).

tff(c_132,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_122])).

tff(c_263,plain,(
    ! [A_27,B_28] :
      ( k10_relat_1(A_27,k1_relat_1(B_28)) = k1_relat_1(k5_relat_1(A_27,B_28))
      | ~ v1_relat_1(B_28)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_14,plain,(
    ! [A_9] :
      ( k1_relat_1(k4_relat_1(A_9)) = k2_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_116,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_14])).

tff(c_128,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_116])).

tff(c_12,plain,(
    ! [A_9] :
      ( k2_relat_1(k4_relat_1(A_9)) = k1_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_113,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_12])).

tff(c_126,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_113])).

tff(c_8,plain,(
    ! [A_5] :
      ( k10_relat_1(A_5,k2_relat_1(A_5)) = k1_relat_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_179,plain,
    ( k10_relat_1(k2_funct_1('#skF_1'),k1_relat_1('#skF_1')) = k1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_8])).

tff(c_183,plain,(
    k10_relat_1(k2_funct_1('#skF_1'),k1_relat_1('#skF_1')) = k1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_179])).

tff(c_226,plain,(
    k10_relat_1(k2_funct_1('#skF_1'),k1_relat_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_183])).

tff(c_269,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_226])).

tff(c_294,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_30,c_269])).

tff(c_296,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_294])).

tff(c_297,plain,(
    k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_321,plain,(
    ! [A_30] :
      ( k4_relat_1(A_30) = k2_funct_1(A_30)
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_324,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_321])).

tff(c_327,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_324])).

tff(c_340,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_2])).

tff(c_350,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_340])).

tff(c_4,plain,(
    ! [A_2] :
      ( k4_relat_1(k4_relat_1(A_2)) = A_2
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_337,plain,
    ( k4_relat_1(k2_funct_1('#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_4])).

tff(c_348,plain,(
    k4_relat_1(k2_funct_1('#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_337])).

tff(c_88,plain,(
    ! [B_20,A_21] :
      ( r1_tarski(k10_relat_1(B_20,A_21),k1_relat_1(B_20))
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_306,plain,(
    ! [A_29] :
      ( r1_tarski(k1_relat_1(A_29),k1_relat_1(A_29))
      | ~ v1_relat_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_88])).

tff(c_753,plain,(
    ! [A_47] :
      ( r1_tarski(k1_relat_1(k4_relat_1(A_47)),k2_relat_1(A_47))
      | ~ v1_relat_1(k4_relat_1(A_47))
      | ~ v1_relat_1(k4_relat_1(A_47))
      | ~ v1_relat_1(A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_306])).

tff(c_16,plain,(
    ! [B_12,A_10] :
      ( k2_relat_1(k5_relat_1(B_12,A_10)) = k2_relat_1(A_10)
      | ~ r1_tarski(k1_relat_1(A_10),k2_relat_1(B_12))
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_785,plain,(
    ! [A_48] :
      ( k2_relat_1(k5_relat_1(A_48,k4_relat_1(A_48))) = k2_relat_1(k4_relat_1(A_48))
      | ~ v1_relat_1(k4_relat_1(A_48))
      | ~ v1_relat_1(A_48) ) ),
    inference(resolution,[status(thm)],[c_753,c_16])).

tff(c_806,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) = k2_relat_1(k4_relat_1(k2_funct_1('#skF_1')))
    | ~ v1_relat_1(k4_relat_1(k2_funct_1('#skF_1')))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_785])).

tff(c_816,plain,(
    k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_30,c_348,c_348,c_806])).

tff(c_818,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_297,c_816])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:43:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.91/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.43  
% 2.91/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.43  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k10_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 2.91/1.43  
% 2.91/1.43  %Foreground sorts:
% 2.91/1.43  
% 2.91/1.43  
% 2.91/1.43  %Background operators:
% 2.91/1.43  
% 2.91/1.43  
% 2.91/1.43  %Foreground operators:
% 2.91/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.91/1.43  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.91/1.43  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.91/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.91/1.43  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.91/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.91/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.91/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.91/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.91/1.43  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.91/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.91/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.91/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.91/1.43  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.91/1.43  
% 2.91/1.45  tff(f_92, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_funct_1)).
% 2.91/1.45  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 2.91/1.45  tff(f_29, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 2.91/1.45  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 2.91/1.45  tff(f_54, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 2.91/1.45  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.91/1.45  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 2.91/1.45  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 2.91/1.45  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 2.91/1.45  tff(c_24, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1') | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.91/1.45  tff(c_95, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_24])).
% 2.91/1.45  tff(c_30, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.91/1.45  tff(c_28, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.91/1.45  tff(c_26, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.91/1.45  tff(c_103, plain, (![A_23]: (k4_relat_1(A_23)=k2_funct_1(A_23) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.91/1.45  tff(c_106, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_26, c_103])).
% 2.91/1.45  tff(c_109, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_106])).
% 2.91/1.45  tff(c_2, plain, (![A_1]: (v1_relat_1(k4_relat_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.91/1.45  tff(c_122, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_109, c_2])).
% 2.91/1.45  tff(c_132, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_122])).
% 2.91/1.45  tff(c_263, plain, (![A_27, B_28]: (k10_relat_1(A_27, k1_relat_1(B_28))=k1_relat_1(k5_relat_1(A_27, B_28)) | ~v1_relat_1(B_28) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.91/1.45  tff(c_14, plain, (![A_9]: (k1_relat_1(k4_relat_1(A_9))=k2_relat_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.91/1.45  tff(c_116, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_109, c_14])).
% 2.91/1.45  tff(c_128, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_116])).
% 2.91/1.45  tff(c_12, plain, (![A_9]: (k2_relat_1(k4_relat_1(A_9))=k1_relat_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.91/1.45  tff(c_113, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_109, c_12])).
% 2.91/1.45  tff(c_126, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_113])).
% 2.91/1.45  tff(c_8, plain, (![A_5]: (k10_relat_1(A_5, k2_relat_1(A_5))=k1_relat_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.91/1.45  tff(c_179, plain, (k10_relat_1(k2_funct_1('#skF_1'), k1_relat_1('#skF_1'))=k1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_126, c_8])).
% 2.91/1.45  tff(c_183, plain, (k10_relat_1(k2_funct_1('#skF_1'), k1_relat_1('#skF_1'))=k1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_179])).
% 2.91/1.45  tff(c_226, plain, (k10_relat_1(k2_funct_1('#skF_1'), k1_relat_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_183])).
% 2.91/1.45  tff(c_269, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_263, c_226])).
% 2.91/1.45  tff(c_294, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_30, c_269])).
% 2.91/1.45  tff(c_296, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95, c_294])).
% 2.91/1.45  tff(c_297, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_24])).
% 2.91/1.45  tff(c_321, plain, (![A_30]: (k4_relat_1(A_30)=k2_funct_1(A_30) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.91/1.45  tff(c_324, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_26, c_321])).
% 2.91/1.45  tff(c_327, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_324])).
% 2.91/1.45  tff(c_340, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_327, c_2])).
% 2.91/1.45  tff(c_350, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_340])).
% 2.91/1.45  tff(c_4, plain, (![A_2]: (k4_relat_1(k4_relat_1(A_2))=A_2 | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.91/1.45  tff(c_337, plain, (k4_relat_1(k2_funct_1('#skF_1'))='#skF_1' | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_327, c_4])).
% 2.91/1.45  tff(c_348, plain, (k4_relat_1(k2_funct_1('#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_337])).
% 2.91/1.45  tff(c_88, plain, (![B_20, A_21]: (r1_tarski(k10_relat_1(B_20, A_21), k1_relat_1(B_20)) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.91/1.45  tff(c_306, plain, (![A_29]: (r1_tarski(k1_relat_1(A_29), k1_relat_1(A_29)) | ~v1_relat_1(A_29) | ~v1_relat_1(A_29))), inference(superposition, [status(thm), theory('equality')], [c_8, c_88])).
% 2.91/1.45  tff(c_753, plain, (![A_47]: (r1_tarski(k1_relat_1(k4_relat_1(A_47)), k2_relat_1(A_47)) | ~v1_relat_1(k4_relat_1(A_47)) | ~v1_relat_1(k4_relat_1(A_47)) | ~v1_relat_1(A_47))), inference(superposition, [status(thm), theory('equality')], [c_14, c_306])).
% 2.91/1.45  tff(c_16, plain, (![B_12, A_10]: (k2_relat_1(k5_relat_1(B_12, A_10))=k2_relat_1(A_10) | ~r1_tarski(k1_relat_1(A_10), k2_relat_1(B_12)) | ~v1_relat_1(B_12) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.91/1.45  tff(c_785, plain, (![A_48]: (k2_relat_1(k5_relat_1(A_48, k4_relat_1(A_48)))=k2_relat_1(k4_relat_1(A_48)) | ~v1_relat_1(k4_relat_1(A_48)) | ~v1_relat_1(A_48))), inference(resolution, [status(thm)], [c_753, c_16])).
% 2.91/1.45  tff(c_806, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))=k2_relat_1(k4_relat_1(k2_funct_1('#skF_1'))) | ~v1_relat_1(k4_relat_1(k2_funct_1('#skF_1'))) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_348, c_785])).
% 2.91/1.45  tff(c_816, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_350, c_30, c_348, c_348, c_806])).
% 2.91/1.45  tff(c_818, plain, $false, inference(negUnitSimplification, [status(thm)], [c_297, c_816])).
% 2.91/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.45  
% 2.91/1.45  Inference rules
% 2.91/1.45  ----------------------
% 2.91/1.45  #Ref     : 0
% 2.91/1.45  #Sup     : 192
% 2.91/1.45  #Fact    : 0
% 2.91/1.45  #Define  : 0
% 2.91/1.45  #Split   : 2
% 2.91/1.45  #Chain   : 0
% 2.91/1.45  #Close   : 0
% 2.91/1.45  
% 2.91/1.45  Ordering : KBO
% 2.91/1.45  
% 2.91/1.45  Simplification rules
% 2.91/1.45  ----------------------
% 2.91/1.45  #Subsume      : 12
% 2.91/1.45  #Demod        : 182
% 2.91/1.45  #Tautology    : 93
% 2.91/1.45  #SimpNegUnit  : 2
% 2.91/1.45  #BackRed      : 0
% 2.91/1.45  
% 2.91/1.45  #Partial instantiations: 0
% 2.91/1.45  #Strategies tried      : 1
% 2.91/1.45  
% 2.91/1.45  Timing (in seconds)
% 2.91/1.45  ----------------------
% 2.91/1.45  Preprocessing        : 0.32
% 2.91/1.45  Parsing              : 0.17
% 2.91/1.45  CNF conversion       : 0.02
% 2.91/1.45  Main loop            : 0.36
% 2.91/1.45  Inferencing          : 0.14
% 2.91/1.45  Reduction            : 0.11
% 2.91/1.45  Demodulation         : 0.08
% 2.91/1.45  BG Simplification    : 0.02
% 2.91/1.45  Subsumption          : 0.06
% 2.91/1.45  Abstraction          : 0.02
% 2.91/1.45  MUC search           : 0.00
% 2.91/1.45  Cooper               : 0.00
% 2.91/1.45  Total                : 0.71
% 2.91/1.45  Index Insertion      : 0.00
% 2.91/1.45  Index Deletion       : 0.00
% 2.91/1.45  Index Matching       : 0.00
% 2.91/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
