%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:59 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   43 (  82 expanded)
%              Number of leaves         :   20 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :   87 ( 193 expanded)
%              Number of equality atoms :   17 (  25 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_43,axiom,(
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

tff(f_53,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k4_relat_1(A))
        & v1_funct_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_funct_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( ? [B] :
            ( v1_relat_1(B)
            & v1_funct_1(B)
            & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
       => v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_24,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_22,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_16,plain,(
    ! [A_8] :
      ( k5_relat_1(k2_funct_1(A_8),A_8) = k6_relat_1(k2_relat_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_20,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_47,plain,(
    ! [A_13] :
      ( k4_relat_1(A_13) = k2_funct_1(A_13)
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_50,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_47])).

tff(c_53,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_50])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_relat_1(k4_relat_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_66,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_2])).

tff(c_76,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_66])).

tff(c_10,plain,(
    ! [A_4] :
      ( v1_funct_1(k4_relat_1(A_4))
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_57,plain,
    ( v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_10])).

tff(c_70,plain,(
    v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_57])).

tff(c_6,plain,(
    ! [A_2] :
      ( k1_relat_1(k4_relat_1(A_2)) = k2_relat_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_60,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_6])).

tff(c_72,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_60])).

tff(c_104,plain,(
    ! [A_16,B_17] :
      ( v2_funct_1(A_16)
      | k6_relat_1(k1_relat_1(A_16)) != k5_relat_1(A_16,B_17)
      | ~ v1_funct_1(B_17)
      | ~ v1_relat_1(B_17)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_110,plain,(
    ! [B_17] :
      ( v2_funct_1(k2_funct_1('#skF_1'))
      | k5_relat_1(k2_funct_1('#skF_1'),B_17) != k6_relat_1(k2_relat_1('#skF_1'))
      | ~ v1_funct_1(B_17)
      | ~ v1_relat_1(B_17)
      | ~ v1_funct_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_104])).

tff(c_115,plain,(
    ! [B_17] :
      ( v2_funct_1(k2_funct_1('#skF_1'))
      | k5_relat_1(k2_funct_1('#skF_1'),B_17) != k6_relat_1(k2_relat_1('#skF_1'))
      | ~ v1_funct_1(B_17)
      | ~ v1_relat_1(B_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_70,c_110])).

tff(c_117,plain,(
    ! [B_18] :
      ( k5_relat_1(k2_funct_1('#skF_1'),B_18) != k6_relat_1(k2_relat_1('#skF_1'))
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_115])).

tff(c_121,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_117])).

tff(c_129,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_121])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:48:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.15  
% 1.73/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.16  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 1.73/1.16  
% 1.73/1.16  %Foreground sorts:
% 1.73/1.16  
% 1.73/1.16  
% 1.73/1.16  %Background operators:
% 1.73/1.16  
% 1.73/1.16  
% 1.73/1.16  %Foreground operators:
% 1.73/1.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.73/1.16  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 1.73/1.16  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.73/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.73/1.16  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.73/1.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.73/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.73/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.73/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.73/1.16  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.73/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.73/1.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.73/1.16  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 1.73/1.16  
% 1.86/1.17  tff(f_85, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_1)).
% 1.86/1.17  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 1.86/1.17  tff(f_43, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 1.86/1.17  tff(f_29, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 1.86/1.17  tff(f_53, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => (v1_relat_1(k4_relat_1(A)) & v1_funct_1(k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_funct_1)).
% 1.86/1.17  tff(f_35, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 1.86/1.17  tff(f_66, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((?[B]: ((v1_relat_1(B) & v1_funct_1(B)) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A))))) => v2_funct_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_funct_1)).
% 1.86/1.17  tff(c_26, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.86/1.17  tff(c_24, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.86/1.17  tff(c_22, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.86/1.17  tff(c_16, plain, (![A_8]: (k5_relat_1(k2_funct_1(A_8), A_8)=k6_relat_1(k2_relat_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.86/1.17  tff(c_20, plain, (~v2_funct_1(k2_funct_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.86/1.17  tff(c_47, plain, (![A_13]: (k4_relat_1(A_13)=k2_funct_1(A_13) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.86/1.17  tff(c_50, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_22, c_47])).
% 1.86/1.17  tff(c_53, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_50])).
% 1.86/1.17  tff(c_2, plain, (![A_1]: (v1_relat_1(k4_relat_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.86/1.17  tff(c_66, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_53, c_2])).
% 1.86/1.17  tff(c_76, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_66])).
% 1.86/1.17  tff(c_10, plain, (![A_4]: (v1_funct_1(k4_relat_1(A_4)) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.86/1.17  tff(c_57, plain, (v1_funct_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_53, c_10])).
% 1.86/1.17  tff(c_70, plain, (v1_funct_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_57])).
% 1.86/1.17  tff(c_6, plain, (![A_2]: (k1_relat_1(k4_relat_1(A_2))=k2_relat_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.86/1.17  tff(c_60, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_53, c_6])).
% 1.86/1.17  tff(c_72, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_60])).
% 1.86/1.17  tff(c_104, plain, (![A_16, B_17]: (v2_funct_1(A_16) | k6_relat_1(k1_relat_1(A_16))!=k5_relat_1(A_16, B_17) | ~v1_funct_1(B_17) | ~v1_relat_1(B_17) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.86/1.17  tff(c_110, plain, (![B_17]: (v2_funct_1(k2_funct_1('#skF_1')) | k5_relat_1(k2_funct_1('#skF_1'), B_17)!=k6_relat_1(k2_relat_1('#skF_1')) | ~v1_funct_1(B_17) | ~v1_relat_1(B_17) | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_72, c_104])).
% 1.86/1.17  tff(c_115, plain, (![B_17]: (v2_funct_1(k2_funct_1('#skF_1')) | k5_relat_1(k2_funct_1('#skF_1'), B_17)!=k6_relat_1(k2_relat_1('#skF_1')) | ~v1_funct_1(B_17) | ~v1_relat_1(B_17))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_70, c_110])).
% 1.86/1.17  tff(c_117, plain, (![B_18]: (k5_relat_1(k2_funct_1('#skF_1'), B_18)!=k6_relat_1(k2_relat_1('#skF_1')) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18))), inference(negUnitSimplification, [status(thm)], [c_20, c_115])).
% 1.86/1.17  tff(c_121, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_16, c_117])).
% 1.86/1.17  tff(c_129, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_121])).
% 1.86/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.17  
% 1.86/1.17  Inference rules
% 1.86/1.17  ----------------------
% 1.86/1.17  #Ref     : 0
% 1.86/1.17  #Sup     : 25
% 1.86/1.17  #Fact    : 0
% 1.86/1.17  #Define  : 0
% 1.86/1.17  #Split   : 0
% 1.86/1.17  #Chain   : 0
% 1.86/1.17  #Close   : 0
% 1.86/1.17  
% 1.86/1.17  Ordering : KBO
% 1.86/1.17  
% 1.86/1.17  Simplification rules
% 1.86/1.17  ----------------------
% 1.86/1.17  #Subsume      : 1
% 1.86/1.17  #Demod        : 13
% 1.86/1.17  #Tautology    : 15
% 1.86/1.17  #SimpNegUnit  : 1
% 1.86/1.17  #BackRed      : 0
% 1.86/1.17  
% 1.86/1.17  #Partial instantiations: 0
% 1.86/1.17  #Strategies tried      : 1
% 1.86/1.17  
% 1.86/1.17  Timing (in seconds)
% 1.86/1.17  ----------------------
% 1.86/1.17  Preprocessing        : 0.28
% 1.86/1.17  Parsing              : 0.15
% 1.86/1.17  CNF conversion       : 0.02
% 1.86/1.17  Main loop            : 0.12
% 1.86/1.17  Inferencing          : 0.05
% 1.86/1.17  Reduction            : 0.04
% 1.86/1.17  Demodulation         : 0.03
% 1.86/1.17  BG Simplification    : 0.01
% 1.86/1.17  Subsumption          : 0.02
% 1.86/1.17  Abstraction          : 0.01
% 1.86/1.17  MUC search           : 0.00
% 1.86/1.17  Cooper               : 0.00
% 1.86/1.17  Total                : 0.43
% 1.86/1.17  Index Insertion      : 0.00
% 1.86/1.17  Index Deletion       : 0.00
% 1.86/1.17  Index Matching       : 0.00
% 1.86/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
