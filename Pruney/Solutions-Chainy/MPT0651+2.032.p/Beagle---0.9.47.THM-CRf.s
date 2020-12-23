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
% DateTime   : Thu Dec  3 10:03:52 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 161 expanded)
%              Number of leaves         :   20 (  68 expanded)
%              Depth                    :    8
%              Number of atoms          :  124 ( 468 expanded)
%              Number of equality atoms :   32 ( 151 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_76,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
            & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_22,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_20,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_14,plain,(
    ! [A_10] :
      ( k2_relat_1(k2_funct_1(A_10)) = k1_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_12,plain,(
    ! [A_9] :
      ( v1_relat_1(k2_funct_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16,plain,(
    ! [A_10] :
      ( k1_relat_1(k2_funct_1(A_10)) = k2_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_211,plain,(
    ! [A_29,B_30] :
      ( k10_relat_1(A_29,k1_relat_1(B_30)) = k1_relat_1(k5_relat_1(A_29,B_30))
      | ~ v1_relat_1(B_30)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_286,plain,(
    ! [A_35,A_36] :
      ( k1_relat_1(k5_relat_1(A_35,k2_funct_1(A_36))) = k10_relat_1(A_35,k2_relat_1(A_36))
      | ~ v1_relat_1(k2_funct_1(A_36))
      | ~ v1_relat_1(A_35)
      | ~ v2_funct_1(A_36)
      | ~ v1_funct_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_211])).

tff(c_6,plain,(
    ! [A_5] :
      ( k10_relat_1(A_5,k2_relat_1(A_5)) = k1_relat_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_82,plain,(
    ! [A_19,B_20] :
      ( k10_relat_1(A_19,k1_relat_1(B_20)) = k1_relat_1(k5_relat_1(A_19,B_20))
      | ~ v1_relat_1(B_20)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_150,plain,(
    ! [A_25,A_26] :
      ( k1_relat_1(k5_relat_1(A_25,k2_funct_1(A_26))) = k10_relat_1(A_25,k2_relat_1(A_26))
      | ~ v1_relat_1(k2_funct_1(A_26))
      | ~ v1_relat_1(A_25)
      | ~ v2_funct_1(A_26)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_82])).

tff(c_18,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_69,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_162,plain,
    ( k10_relat_1('#skF_1',k2_relat_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_69])).

tff(c_171,plain,
    ( k10_relat_1('#skF_1',k2_relat_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_24,c_162])).

tff(c_173,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_171])).

tff(c_176,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_173])).

tff(c_180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_176])).

tff(c_181,plain,(
    k10_relat_1('#skF_1',k2_relat_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_171])).

tff(c_185,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_181])).

tff(c_189,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_185])).

tff(c_191,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_298,plain,
    ( k10_relat_1('#skF_1',k2_relat_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_191])).

tff(c_310,plain,
    ( k10_relat_1('#skF_1',k2_relat_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_24,c_298])).

tff(c_314,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_310])).

tff(c_317,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_314])).

tff(c_321,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_317])).

tff(c_323,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_310])).

tff(c_4,plain,(
    ! [B_4,A_2] :
      ( k9_relat_1(B_4,k2_relat_1(A_2)) = k2_relat_1(k5_relat_1(A_2,B_4))
      | ~ v1_relat_1(B_4)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_57,plain,(
    ! [A_16] :
      ( k1_relat_1(k2_funct_1(A_16)) = k2_relat_1(A_16)
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2,plain,(
    ! [A_1] :
      ( k9_relat_1(A_1,k1_relat_1(A_1)) = k2_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_227,plain,(
    ! [A_31] :
      ( k9_relat_1(k2_funct_1(A_31),k2_relat_1(A_31)) = k2_relat_1(k2_funct_1(A_31))
      | ~ v1_relat_1(k2_funct_1(A_31))
      | ~ v2_funct_1(A_31)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_2])).

tff(c_342,plain,(
    ! [A_37] :
      ( k2_relat_1(k5_relat_1(A_37,k2_funct_1(A_37))) = k2_relat_1(k2_funct_1(A_37))
      | ~ v1_relat_1(k2_funct_1(A_37))
      | ~ v2_funct_1(A_37)
      | ~ v1_funct_1(A_37)
      | ~ v1_relat_1(A_37)
      | ~ v1_relat_1(k2_funct_1(A_37))
      | ~ v1_relat_1(A_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_227])).

tff(c_190,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_358,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_190])).

tff(c_371,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_323,c_24,c_22,c_20,c_323,c_358])).

tff(c_375,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_371])).

tff(c_379,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_375])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:11:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.30  
% 2.14/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.30  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 2.14/1.30  
% 2.14/1.30  %Foreground sorts:
% 2.14/1.30  
% 2.14/1.30  
% 2.14/1.30  %Background operators:
% 2.14/1.30  
% 2.14/1.30  
% 2.14/1.30  %Foreground operators:
% 2.14/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.14/1.30  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.14/1.30  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.14/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.30  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.14/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.14/1.30  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.14/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.14/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.30  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.14/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.14/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.14/1.30  
% 2.14/1.32  tff(f_76, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 2.14/1.32  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 2.14/1.32  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.14/1.32  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 2.14/1.32  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.14/1.32  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 2.14/1.32  tff(f_29, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 2.14/1.32  tff(c_24, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.14/1.32  tff(c_22, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.14/1.32  tff(c_20, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.14/1.32  tff(c_14, plain, (![A_10]: (k2_relat_1(k2_funct_1(A_10))=k1_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.14/1.32  tff(c_12, plain, (![A_9]: (v1_relat_1(k2_funct_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.14/1.32  tff(c_16, plain, (![A_10]: (k1_relat_1(k2_funct_1(A_10))=k2_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.14/1.32  tff(c_211, plain, (![A_29, B_30]: (k10_relat_1(A_29, k1_relat_1(B_30))=k1_relat_1(k5_relat_1(A_29, B_30)) | ~v1_relat_1(B_30) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.14/1.32  tff(c_286, plain, (![A_35, A_36]: (k1_relat_1(k5_relat_1(A_35, k2_funct_1(A_36)))=k10_relat_1(A_35, k2_relat_1(A_36)) | ~v1_relat_1(k2_funct_1(A_36)) | ~v1_relat_1(A_35) | ~v2_funct_1(A_36) | ~v1_funct_1(A_36) | ~v1_relat_1(A_36))), inference(superposition, [status(thm), theory('equality')], [c_16, c_211])).
% 2.14/1.32  tff(c_6, plain, (![A_5]: (k10_relat_1(A_5, k2_relat_1(A_5))=k1_relat_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.14/1.32  tff(c_82, plain, (![A_19, B_20]: (k10_relat_1(A_19, k1_relat_1(B_20))=k1_relat_1(k5_relat_1(A_19, B_20)) | ~v1_relat_1(B_20) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.14/1.32  tff(c_150, plain, (![A_25, A_26]: (k1_relat_1(k5_relat_1(A_25, k2_funct_1(A_26)))=k10_relat_1(A_25, k2_relat_1(A_26)) | ~v1_relat_1(k2_funct_1(A_26)) | ~v1_relat_1(A_25) | ~v2_funct_1(A_26) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(superposition, [status(thm), theory('equality')], [c_16, c_82])).
% 2.14/1.32  tff(c_18, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.14/1.32  tff(c_69, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_18])).
% 2.14/1.32  tff(c_162, plain, (k10_relat_1('#skF_1', k2_relat_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_150, c_69])).
% 2.14/1.32  tff(c_171, plain, (k10_relat_1('#skF_1', k2_relat_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_24, c_162])).
% 2.14/1.32  tff(c_173, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_171])).
% 2.14/1.32  tff(c_176, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_12, c_173])).
% 2.14/1.32  tff(c_180, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_176])).
% 2.14/1.32  tff(c_181, plain, (k10_relat_1('#skF_1', k2_relat_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_171])).
% 2.14/1.32  tff(c_185, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6, c_181])).
% 2.14/1.32  tff(c_189, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_185])).
% 2.14/1.32  tff(c_191, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_18])).
% 2.14/1.32  tff(c_298, plain, (k10_relat_1('#skF_1', k2_relat_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_286, c_191])).
% 2.14/1.32  tff(c_310, plain, (k10_relat_1('#skF_1', k2_relat_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_24, c_298])).
% 2.14/1.32  tff(c_314, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_310])).
% 2.14/1.32  tff(c_317, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_12, c_314])).
% 2.14/1.32  tff(c_321, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_317])).
% 2.14/1.32  tff(c_323, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_310])).
% 2.14/1.32  tff(c_4, plain, (![B_4, A_2]: (k9_relat_1(B_4, k2_relat_1(A_2))=k2_relat_1(k5_relat_1(A_2, B_4)) | ~v1_relat_1(B_4) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.14/1.32  tff(c_57, plain, (![A_16]: (k1_relat_1(k2_funct_1(A_16))=k2_relat_1(A_16) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.14/1.32  tff(c_2, plain, (![A_1]: (k9_relat_1(A_1, k1_relat_1(A_1))=k2_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.14/1.32  tff(c_227, plain, (![A_31]: (k9_relat_1(k2_funct_1(A_31), k2_relat_1(A_31))=k2_relat_1(k2_funct_1(A_31)) | ~v1_relat_1(k2_funct_1(A_31)) | ~v2_funct_1(A_31) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(superposition, [status(thm), theory('equality')], [c_57, c_2])).
% 2.14/1.32  tff(c_342, plain, (![A_37]: (k2_relat_1(k5_relat_1(A_37, k2_funct_1(A_37)))=k2_relat_1(k2_funct_1(A_37)) | ~v1_relat_1(k2_funct_1(A_37)) | ~v2_funct_1(A_37) | ~v1_funct_1(A_37) | ~v1_relat_1(A_37) | ~v1_relat_1(k2_funct_1(A_37)) | ~v1_relat_1(A_37))), inference(superposition, [status(thm), theory('equality')], [c_4, c_227])).
% 2.14/1.32  tff(c_190, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_18])).
% 2.14/1.32  tff(c_358, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_342, c_190])).
% 2.14/1.32  tff(c_371, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_323, c_24, c_22, c_20, c_323, c_358])).
% 2.14/1.32  tff(c_375, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14, c_371])).
% 2.14/1.32  tff(c_379, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_375])).
% 2.14/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.32  
% 2.14/1.32  Inference rules
% 2.14/1.32  ----------------------
% 2.14/1.32  #Ref     : 0
% 2.14/1.32  #Sup     : 86
% 2.14/1.32  #Fact    : 0
% 2.14/1.32  #Define  : 0
% 2.14/1.32  #Split   : 4
% 2.14/1.32  #Chain   : 0
% 2.14/1.32  #Close   : 0
% 2.14/1.32  
% 2.14/1.32  Ordering : KBO
% 2.14/1.32  
% 2.14/1.32  Simplification rules
% 2.14/1.32  ----------------------
% 2.14/1.32  #Subsume      : 2
% 2.14/1.32  #Demod        : 30
% 2.14/1.32  #Tautology    : 41
% 2.14/1.32  #SimpNegUnit  : 0
% 2.14/1.32  #BackRed      : 0
% 2.14/1.32  
% 2.14/1.32  #Partial instantiations: 0
% 2.14/1.32  #Strategies tried      : 1
% 2.14/1.32  
% 2.14/1.32  Timing (in seconds)
% 2.14/1.32  ----------------------
% 2.14/1.32  Preprocessing        : 0.30
% 2.14/1.32  Parsing              : 0.17
% 2.14/1.32  CNF conversion       : 0.02
% 2.14/1.32  Main loop            : 0.25
% 2.14/1.32  Inferencing          : 0.10
% 2.14/1.32  Reduction            : 0.07
% 2.14/1.32  Demodulation         : 0.05
% 2.14/1.32  BG Simplification    : 0.02
% 2.14/1.32  Subsumption          : 0.04
% 2.14/1.32  Abstraction          : 0.02
% 2.50/1.32  MUC search           : 0.00
% 2.50/1.32  Cooper               : 0.00
% 2.50/1.32  Total                : 0.58
% 2.50/1.32  Index Insertion      : 0.00
% 2.50/1.32  Index Deletion       : 0.00
% 2.50/1.32  Index Matching       : 0.00
% 2.50/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
