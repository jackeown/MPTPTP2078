%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:53 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 112 expanded)
%              Number of leaves         :   22 (  51 expanded)
%              Depth                    :    8
%              Number of atoms          :  111 ( 295 expanded)
%              Number of equality atoms :   28 (  88 expanded)
%              Maximal formula depth    :   10 (   4 average)
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

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
            & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_26,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_24,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_48,plain,(
    ! [A_18] :
      ( k4_relat_1(A_18) = k2_funct_1(A_18)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_51,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_48])).

tff(c_54,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_51])).

tff(c_8,plain,(
    ! [A_3] :
      ( v1_relat_1(k4_relat_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_58,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_8])).

tff(c_62,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_58])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_12] :
      ( k2_relat_1(k2_funct_1(A_12)) = k1_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_222,plain,(
    ! [B_33,A_34] :
      ( k2_relat_1(k5_relat_1(B_33,A_34)) = k2_relat_1(A_34)
      | ~ r1_tarski(k1_relat_1(A_34),k2_relat_1(B_33))
      | ~ v1_relat_1(B_33)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_341,plain,(
    ! [A_39,A_40] :
      ( k2_relat_1(k5_relat_1(k2_funct_1(A_39),A_40)) = k2_relat_1(A_40)
      | ~ r1_tarski(k1_relat_1(A_40),k1_relat_1(A_39))
      | ~ v1_relat_1(k2_funct_1(A_39))
      | ~ v1_relat_1(A_40)
      | ~ v2_funct_1(A_39)
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_222])).

tff(c_455,plain,(
    ! [A_43] :
      ( k2_relat_1(k5_relat_1(k2_funct_1(A_43),A_43)) = k2_relat_1(A_43)
      | ~ v1_relat_1(k2_funct_1(A_43))
      | ~ v2_funct_1(A_43)
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(resolution,[status(thm)],[c_6,c_341])).

tff(c_20,plain,(
    ! [A_12] :
      ( k1_relat_1(k2_funct_1(A_12)) = k2_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_74,plain,(
    ! [A_20] :
      ( k2_relat_1(k2_funct_1(A_20)) = k1_relat_1(A_20)
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_10,plain,(
    ! [A_4] :
      ( k10_relat_1(A_4,k2_relat_1(A_4)) = k1_relat_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_105,plain,(
    ! [A_25] :
      ( k10_relat_1(k2_funct_1(A_25),k1_relat_1(A_25)) = k1_relat_1(k2_funct_1(A_25))
      | ~ v1_relat_1(k2_funct_1(A_25))
      | ~ v2_funct_1(A_25)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_10])).

tff(c_12,plain,(
    ! [A_5,B_7] :
      ( k10_relat_1(A_5,k1_relat_1(B_7)) = k1_relat_1(k5_relat_1(A_5,B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_142,plain,(
    ! [A_28] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(A_28),A_28)) = k1_relat_1(k2_funct_1(A_28))
      | ~ v1_relat_1(A_28)
      | ~ v1_relat_1(k2_funct_1(A_28))
      | ~ v1_relat_1(k2_funct_1(A_28))
      | ~ v2_funct_1(A_28)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_12])).

tff(c_22,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_64,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_161,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_64])).

tff(c_171,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_62,c_62,c_28,c_161])).

tff(c_175,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_171])).

tff(c_179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_175])).

tff(c_180,plain,(
    k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_467,plain,
    ( ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_455,c_180])).

tff(c_478,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_62,c_467])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:25:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.32  
% 2.23/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.32  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k10_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 2.23/1.32  
% 2.23/1.32  %Foreground sorts:
% 2.23/1.32  
% 2.23/1.32  
% 2.23/1.32  %Background operators:
% 2.23/1.32  
% 2.23/1.32  
% 2.23/1.32  %Foreground operators:
% 2.23/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.23/1.32  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.23/1.32  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.23/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.32  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.23/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.23/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.23/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.32  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.23/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.23/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.23/1.32  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.23/1.32  
% 2.53/1.34  tff(f_84, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_funct_1)).
% 2.53/1.34  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 2.53/1.34  tff(f_35, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 2.53/1.34  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.53/1.34  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 2.53/1.34  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 2.53/1.34  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 2.53/1.34  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 2.53/1.34  tff(c_28, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.53/1.34  tff(c_26, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.53/1.34  tff(c_24, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.53/1.34  tff(c_48, plain, (![A_18]: (k4_relat_1(A_18)=k2_funct_1(A_18) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.53/1.34  tff(c_51, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_24, c_48])).
% 2.53/1.34  tff(c_54, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_51])).
% 2.53/1.34  tff(c_8, plain, (![A_3]: (v1_relat_1(k4_relat_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.53/1.34  tff(c_58, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_54, c_8])).
% 2.53/1.34  tff(c_62, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_58])).
% 2.53/1.34  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.53/1.34  tff(c_18, plain, (![A_12]: (k2_relat_1(k2_funct_1(A_12))=k1_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.53/1.34  tff(c_222, plain, (![B_33, A_34]: (k2_relat_1(k5_relat_1(B_33, A_34))=k2_relat_1(A_34) | ~r1_tarski(k1_relat_1(A_34), k2_relat_1(B_33)) | ~v1_relat_1(B_33) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.53/1.34  tff(c_341, plain, (![A_39, A_40]: (k2_relat_1(k5_relat_1(k2_funct_1(A_39), A_40))=k2_relat_1(A_40) | ~r1_tarski(k1_relat_1(A_40), k1_relat_1(A_39)) | ~v1_relat_1(k2_funct_1(A_39)) | ~v1_relat_1(A_40) | ~v2_funct_1(A_39) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(superposition, [status(thm), theory('equality')], [c_18, c_222])).
% 2.53/1.34  tff(c_455, plain, (![A_43]: (k2_relat_1(k5_relat_1(k2_funct_1(A_43), A_43))=k2_relat_1(A_43) | ~v1_relat_1(k2_funct_1(A_43)) | ~v2_funct_1(A_43) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(resolution, [status(thm)], [c_6, c_341])).
% 2.53/1.34  tff(c_20, plain, (![A_12]: (k1_relat_1(k2_funct_1(A_12))=k2_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.53/1.34  tff(c_74, plain, (![A_20]: (k2_relat_1(k2_funct_1(A_20))=k1_relat_1(A_20) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.53/1.34  tff(c_10, plain, (![A_4]: (k10_relat_1(A_4, k2_relat_1(A_4))=k1_relat_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.53/1.34  tff(c_105, plain, (![A_25]: (k10_relat_1(k2_funct_1(A_25), k1_relat_1(A_25))=k1_relat_1(k2_funct_1(A_25)) | ~v1_relat_1(k2_funct_1(A_25)) | ~v2_funct_1(A_25) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(superposition, [status(thm), theory('equality')], [c_74, c_10])).
% 2.53/1.34  tff(c_12, plain, (![A_5, B_7]: (k10_relat_1(A_5, k1_relat_1(B_7))=k1_relat_1(k5_relat_1(A_5, B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.53/1.34  tff(c_142, plain, (![A_28]: (k1_relat_1(k5_relat_1(k2_funct_1(A_28), A_28))=k1_relat_1(k2_funct_1(A_28)) | ~v1_relat_1(A_28) | ~v1_relat_1(k2_funct_1(A_28)) | ~v1_relat_1(k2_funct_1(A_28)) | ~v2_funct_1(A_28) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(superposition, [status(thm), theory('equality')], [c_105, c_12])).
% 2.53/1.34  tff(c_22, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1') | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.53/1.34  tff(c_64, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_22])).
% 2.53/1.34  tff(c_161, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_142, c_64])).
% 2.53/1.34  tff(c_171, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_62, c_62, c_28, c_161])).
% 2.53/1.34  tff(c_175, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_20, c_171])).
% 2.53/1.34  tff(c_179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_175])).
% 2.53/1.34  tff(c_180, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_22])).
% 2.53/1.34  tff(c_467, plain, (~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_455, c_180])).
% 2.53/1.34  tff(c_478, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_62, c_467])).
% 2.53/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.34  
% 2.53/1.34  Inference rules
% 2.53/1.34  ----------------------
% 2.53/1.34  #Ref     : 0
% 2.53/1.34  #Sup     : 112
% 2.53/1.34  #Fact    : 0
% 2.53/1.34  #Define  : 0
% 2.53/1.34  #Split   : 3
% 2.53/1.34  #Chain   : 0
% 2.53/1.34  #Close   : 0
% 2.53/1.34  
% 2.53/1.34  Ordering : KBO
% 2.53/1.34  
% 2.53/1.34  Simplification rules
% 2.53/1.34  ----------------------
% 2.53/1.34  #Subsume      : 4
% 2.53/1.34  #Demod        : 55
% 2.53/1.34  #Tautology    : 44
% 2.53/1.34  #SimpNegUnit  : 0
% 2.53/1.34  #BackRed      : 0
% 2.53/1.34  
% 2.53/1.34  #Partial instantiations: 0
% 2.53/1.34  #Strategies tried      : 1
% 2.53/1.34  
% 2.53/1.34  Timing (in seconds)
% 2.53/1.34  ----------------------
% 2.53/1.34  Preprocessing        : 0.30
% 2.53/1.34  Parsing              : 0.16
% 2.53/1.34  CNF conversion       : 0.02
% 2.53/1.34  Main loop            : 0.27
% 2.53/1.34  Inferencing          : 0.10
% 2.53/1.34  Reduction            : 0.08
% 2.53/1.34  Demodulation         : 0.06
% 2.53/1.34  BG Simplification    : 0.02
% 2.53/1.34  Subsumption          : 0.05
% 2.53/1.34  Abstraction          : 0.02
% 2.53/1.34  MUC search           : 0.00
% 2.53/1.34  Cooper               : 0.00
% 2.53/1.34  Total                : 0.60
% 2.53/1.34  Index Insertion      : 0.00
% 2.53/1.34  Index Deletion       : 0.00
% 2.53/1.34  Index Matching       : 0.00
% 2.53/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
