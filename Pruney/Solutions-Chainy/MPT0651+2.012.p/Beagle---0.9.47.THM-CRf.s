%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:49 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 140 expanded)
%              Number of leaves         :   20 (  60 expanded)
%              Depth                    :    8
%              Number of atoms          :  120 ( 400 expanded)
%              Number of equality atoms :   30 ( 127 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
            & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_26,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_24,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_18,plain,(
    ! [A_11] :
      ( k2_relat_1(k2_funct_1(A_11)) = k1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_16,plain,(
    ! [A_10] :
      ( v1_relat_1(k2_funct_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    ! [A_11] :
      ( k1_relat_1(k2_funct_1(A_11)) = k2_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_167,plain,(
    ! [A_28,B_29] :
      ( k10_relat_1(A_28,k1_relat_1(B_29)) = k1_relat_1(k5_relat_1(A_28,B_29))
      | ~ v1_relat_1(B_29)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_215,plain,(
    ! [A_33,A_34] :
      ( k1_relat_1(k5_relat_1(A_33,k2_funct_1(A_34))) = k10_relat_1(A_33,k2_relat_1(A_34))
      | ~ v1_relat_1(k2_funct_1(A_34))
      | ~ v1_relat_1(A_33)
      | ~ v2_funct_1(A_34)
      | ~ v1_funct_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_167])).

tff(c_8,plain,(
    ! [A_3] :
      ( k10_relat_1(A_3,k2_relat_1(A_3)) = k1_relat_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_71,plain,(
    ! [A_20,B_21] :
      ( k10_relat_1(A_20,k1_relat_1(B_21)) = k1_relat_1(k5_relat_1(A_20,B_21))
      | ~ v1_relat_1(B_21)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_109,plain,(
    ! [A_25,A_26] :
      ( k1_relat_1(k5_relat_1(A_25,k2_funct_1(A_26))) = k10_relat_1(A_25,k2_relat_1(A_26))
      | ~ v1_relat_1(k2_funct_1(A_26))
      | ~ v1_relat_1(A_25)
      | ~ v2_funct_1(A_26)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_71])).

tff(c_22,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_58,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_124,plain,
    ( k10_relat_1('#skF_1',k2_relat_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_58])).

tff(c_130,plain,
    ( k10_relat_1('#skF_1',k2_relat_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_28,c_124])).

tff(c_132,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_130])).

tff(c_135,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_132])).

tff(c_139,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_135])).

tff(c_140,plain,(
    k10_relat_1('#skF_1',k2_relat_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_144,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_140])).

tff(c_148,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_144])).

tff(c_150,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_230,plain,
    ( k10_relat_1('#skF_1',k2_relat_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_150])).

tff(c_239,plain,
    ( k10_relat_1('#skF_1',k2_relat_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_28,c_230])).

tff(c_243,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_239])).

tff(c_246,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_243])).

tff(c_250,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_246])).

tff(c_252,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_239])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_182,plain,(
    ! [B_30,A_31] :
      ( k2_relat_1(k5_relat_1(B_30,A_31)) = k2_relat_1(A_31)
      | ~ r1_tarski(k1_relat_1(A_31),k2_relat_1(B_30))
      | ~ v1_relat_1(B_30)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_342,plain,(
    ! [B_39,A_40] :
      ( k2_relat_1(k5_relat_1(B_39,k2_funct_1(A_40))) = k2_relat_1(k2_funct_1(A_40))
      | ~ r1_tarski(k2_relat_1(A_40),k2_relat_1(B_39))
      | ~ v1_relat_1(B_39)
      | ~ v1_relat_1(k2_funct_1(A_40))
      | ~ v2_funct_1(A_40)
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_182])).

tff(c_360,plain,(
    ! [A_41] :
      ( k2_relat_1(k5_relat_1(A_41,k2_funct_1(A_41))) = k2_relat_1(k2_funct_1(A_41))
      | ~ v1_relat_1(k2_funct_1(A_41))
      | ~ v2_funct_1(A_41)
      | ~ v1_funct_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(resolution,[status(thm)],[c_6,c_342])).

tff(c_149,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_375,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_149])).

tff(c_384,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_252,c_375])).

tff(c_388,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_384])).

tff(c_392,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_388])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:37:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.33  
% 2.33/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.33  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 2.33/1.33  
% 2.33/1.33  %Foreground sorts:
% 2.33/1.33  
% 2.33/1.33  
% 2.33/1.33  %Background operators:
% 2.33/1.33  
% 2.33/1.33  
% 2.33/1.33  %Foreground operators:
% 2.33/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.33/1.33  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.33/1.33  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.33/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.33  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.33/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.33/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.33/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.33/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.33  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.33/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.33/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.33/1.33  
% 2.33/1.34  tff(f_80, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 2.33/1.34  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 2.33/1.34  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.33/1.34  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 2.33/1.34  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.33/1.34  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.33/1.34  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 2.33/1.34  tff(c_28, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.33/1.34  tff(c_26, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.33/1.34  tff(c_24, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.33/1.34  tff(c_18, plain, (![A_11]: (k2_relat_1(k2_funct_1(A_11))=k1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.33/1.34  tff(c_16, plain, (![A_10]: (v1_relat_1(k2_funct_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.33/1.34  tff(c_20, plain, (![A_11]: (k1_relat_1(k2_funct_1(A_11))=k2_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.33/1.34  tff(c_167, plain, (![A_28, B_29]: (k10_relat_1(A_28, k1_relat_1(B_29))=k1_relat_1(k5_relat_1(A_28, B_29)) | ~v1_relat_1(B_29) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.33/1.34  tff(c_215, plain, (![A_33, A_34]: (k1_relat_1(k5_relat_1(A_33, k2_funct_1(A_34)))=k10_relat_1(A_33, k2_relat_1(A_34)) | ~v1_relat_1(k2_funct_1(A_34)) | ~v1_relat_1(A_33) | ~v2_funct_1(A_34) | ~v1_funct_1(A_34) | ~v1_relat_1(A_34))), inference(superposition, [status(thm), theory('equality')], [c_20, c_167])).
% 2.33/1.34  tff(c_8, plain, (![A_3]: (k10_relat_1(A_3, k2_relat_1(A_3))=k1_relat_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.33/1.34  tff(c_71, plain, (![A_20, B_21]: (k10_relat_1(A_20, k1_relat_1(B_21))=k1_relat_1(k5_relat_1(A_20, B_21)) | ~v1_relat_1(B_21) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.33/1.34  tff(c_109, plain, (![A_25, A_26]: (k1_relat_1(k5_relat_1(A_25, k2_funct_1(A_26)))=k10_relat_1(A_25, k2_relat_1(A_26)) | ~v1_relat_1(k2_funct_1(A_26)) | ~v1_relat_1(A_25) | ~v2_funct_1(A_26) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(superposition, [status(thm), theory('equality')], [c_20, c_71])).
% 2.33/1.34  tff(c_22, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.33/1.34  tff(c_58, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_22])).
% 2.33/1.34  tff(c_124, plain, (k10_relat_1('#skF_1', k2_relat_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_109, c_58])).
% 2.33/1.34  tff(c_130, plain, (k10_relat_1('#skF_1', k2_relat_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_28, c_124])).
% 2.33/1.34  tff(c_132, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_130])).
% 2.33/1.34  tff(c_135, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_16, c_132])).
% 2.33/1.34  tff(c_139, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_135])).
% 2.33/1.34  tff(c_140, plain, (k10_relat_1('#skF_1', k2_relat_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_130])).
% 2.33/1.34  tff(c_144, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8, c_140])).
% 2.33/1.34  tff(c_148, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_144])).
% 2.33/1.34  tff(c_150, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_22])).
% 2.33/1.34  tff(c_230, plain, (k10_relat_1('#skF_1', k2_relat_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_215, c_150])).
% 2.33/1.34  tff(c_239, plain, (k10_relat_1('#skF_1', k2_relat_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_28, c_230])).
% 2.33/1.34  tff(c_243, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_239])).
% 2.33/1.34  tff(c_246, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_16, c_243])).
% 2.33/1.34  tff(c_250, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_246])).
% 2.33/1.34  tff(c_252, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_239])).
% 2.33/1.34  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.33/1.34  tff(c_182, plain, (![B_30, A_31]: (k2_relat_1(k5_relat_1(B_30, A_31))=k2_relat_1(A_31) | ~r1_tarski(k1_relat_1(A_31), k2_relat_1(B_30)) | ~v1_relat_1(B_30) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.33/1.34  tff(c_342, plain, (![B_39, A_40]: (k2_relat_1(k5_relat_1(B_39, k2_funct_1(A_40)))=k2_relat_1(k2_funct_1(A_40)) | ~r1_tarski(k2_relat_1(A_40), k2_relat_1(B_39)) | ~v1_relat_1(B_39) | ~v1_relat_1(k2_funct_1(A_40)) | ~v2_funct_1(A_40) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(superposition, [status(thm), theory('equality')], [c_20, c_182])).
% 2.33/1.34  tff(c_360, plain, (![A_41]: (k2_relat_1(k5_relat_1(A_41, k2_funct_1(A_41)))=k2_relat_1(k2_funct_1(A_41)) | ~v1_relat_1(k2_funct_1(A_41)) | ~v2_funct_1(A_41) | ~v1_funct_1(A_41) | ~v1_relat_1(A_41))), inference(resolution, [status(thm)], [c_6, c_342])).
% 2.33/1.34  tff(c_149, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_22])).
% 2.33/1.34  tff(c_375, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_360, c_149])).
% 2.33/1.34  tff(c_384, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_252, c_375])).
% 2.33/1.34  tff(c_388, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_18, c_384])).
% 2.33/1.34  tff(c_392, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_388])).
% 2.33/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.34  
% 2.33/1.34  Inference rules
% 2.33/1.34  ----------------------
% 2.33/1.34  #Ref     : 0
% 2.33/1.34  #Sup     : 89
% 2.33/1.34  #Fact    : 0
% 2.33/1.34  #Define  : 0
% 2.33/1.34  #Split   : 4
% 2.33/1.34  #Chain   : 0
% 2.33/1.34  #Close   : 0
% 2.33/1.34  
% 2.33/1.34  Ordering : KBO
% 2.33/1.34  
% 2.33/1.34  Simplification rules
% 2.33/1.34  ----------------------
% 2.33/1.34  #Subsume      : 5
% 2.33/1.34  #Demod        : 30
% 2.33/1.34  #Tautology    : 35
% 2.33/1.34  #SimpNegUnit  : 0
% 2.33/1.34  #BackRed      : 0
% 2.33/1.34  
% 2.33/1.34  #Partial instantiations: 0
% 2.33/1.34  #Strategies tried      : 1
% 2.33/1.34  
% 2.33/1.34  Timing (in seconds)
% 2.33/1.34  ----------------------
% 2.33/1.35  Preprocessing        : 0.28
% 2.33/1.35  Parsing              : 0.14
% 2.33/1.35  CNF conversion       : 0.02
% 2.33/1.35  Main loop            : 0.25
% 2.33/1.35  Inferencing          : 0.09
% 2.33/1.35  Reduction            : 0.07
% 2.33/1.35  Demodulation         : 0.05
% 2.33/1.35  BG Simplification    : 0.02
% 2.33/1.35  Subsumption          : 0.05
% 2.33/1.35  Abstraction          : 0.02
% 2.33/1.35  MUC search           : 0.00
% 2.33/1.35  Cooper               : 0.00
% 2.33/1.35  Total                : 0.56
% 2.33/1.35  Index Insertion      : 0.00
% 2.33/1.35  Index Deletion       : 0.00
% 2.33/1.35  Index Matching       : 0.00
% 2.33/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
