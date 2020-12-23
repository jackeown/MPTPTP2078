%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:08 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   44 (  69 expanded)
%              Number of leaves         :   17 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :  111 ( 229 expanded)
%              Number of equality atoms :   19 (  36 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k4_relat_1 > k2_funct_1 > #skF_2 > #skF_1

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( v2_funct_1(A)
                & v2_funct_1(B) )
             => k2_funct_1(k5_relat_1(A,B)) = k5_relat_1(k2_funct_1(B),k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v1_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & v2_funct_1(B) )
           => v2_funct_1(k5_relat_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_funct_1)).

tff(f_46,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_24,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_20,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_18,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_16,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( v1_funct_1(k5_relat_1(A_7,B_8))
      | ~ v1_funct_1(B_8)
      | ~ v1_relat_1(B_8)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k5_relat_1(A_1,B_2))
      | ~ v1_relat_1(B_2)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_120,plain,(
    ! [A_21,B_22] :
      ( v2_funct_1(k5_relat_1(A_21,B_22))
      | ~ v2_funct_1(B_22)
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6,plain,(
    ! [A_6] :
      ( k4_relat_1(A_6) = k2_funct_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_376,plain,(
    ! [A_34,B_35] :
      ( k4_relat_1(k5_relat_1(A_34,B_35)) = k2_funct_1(k5_relat_1(A_34,B_35))
      | ~ v1_funct_1(k5_relat_1(A_34,B_35))
      | ~ v1_relat_1(k5_relat_1(A_34,B_35))
      | ~ v2_funct_1(B_35)
      | ~ v2_funct_1(A_34)
      | ~ v1_funct_1(B_35)
      | ~ v1_relat_1(B_35)
      | ~ v1_funct_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(resolution,[status(thm)],[c_120,c_6])).

tff(c_412,plain,(
    ! [A_36,B_37] :
      ( k4_relat_1(k5_relat_1(A_36,B_37)) = k2_funct_1(k5_relat_1(A_36,B_37))
      | ~ v1_funct_1(k5_relat_1(A_36,B_37))
      | ~ v2_funct_1(B_37)
      | ~ v2_funct_1(A_36)
      | ~ v1_funct_1(B_37)
      | ~ v1_funct_1(A_36)
      | ~ v1_relat_1(B_37)
      | ~ v1_relat_1(A_36) ) ),
    inference(resolution,[status(thm)],[c_2,c_376])).

tff(c_448,plain,(
    ! [A_38,B_39] :
      ( k4_relat_1(k5_relat_1(A_38,B_39)) = k2_funct_1(k5_relat_1(A_38,B_39))
      | ~ v2_funct_1(B_39)
      | ~ v2_funct_1(A_38)
      | ~ v1_funct_1(B_39)
      | ~ v1_relat_1(B_39)
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(resolution,[status(thm)],[c_8,c_412])).

tff(c_28,plain,(
    ! [A_15] :
      ( k4_relat_1(A_15) = k2_funct_1(A_15)
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_31,plain,
    ( k4_relat_1('#skF_2') = k2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_28])).

tff(c_37,plain,(
    k4_relat_1('#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_31])).

tff(c_34,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_28])).

tff(c_40,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_34])).

tff(c_50,plain,(
    ! [B_18,A_19] :
      ( k5_relat_1(k4_relat_1(B_18),k4_relat_1(A_19)) = k4_relat_1(k5_relat_1(A_19,B_18))
      | ~ v1_relat_1(B_18)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_68,plain,(
    ! [B_18] :
      ( k5_relat_1(k4_relat_1(B_18),k2_funct_1('#skF_1')) = k4_relat_1(k5_relat_1('#skF_1',B_18))
      | ~ v1_relat_1(B_18)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_50])).

tff(c_147,plain,(
    ! [B_23] :
      ( k5_relat_1(k4_relat_1(B_23),k2_funct_1('#skF_1')) = k4_relat_1(k5_relat_1('#skF_1',B_23))
      | ~ v1_relat_1(B_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_68])).

tff(c_168,plain,
    ( k5_relat_1(k2_funct_1('#skF_2'),k2_funct_1('#skF_1')) = k4_relat_1(k5_relat_1('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_147])).

tff(c_174,plain,(
    k5_relat_1(k2_funct_1('#skF_2'),k2_funct_1('#skF_1')) = k4_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_168])).

tff(c_14,plain,(
    k5_relat_1(k2_funct_1('#skF_2'),k2_funct_1('#skF_1')) != k2_funct_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_175,plain,(
    k4_relat_1(k5_relat_1('#skF_1','#skF_2')) != k2_funct_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_14])).

tff(c_472,plain,
    ( ~ v2_funct_1('#skF_2')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_448,c_175])).

tff(c_519,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_20,c_18,c_16,c_472])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:28:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.36  
% 2.66/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.36  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k4_relat_1 > k2_funct_1 > #skF_2 > #skF_1
% 2.66/1.36  
% 2.66/1.36  %Foreground sorts:
% 2.66/1.36  
% 2.66/1.36  
% 2.66/1.36  %Background operators:
% 2.66/1.36  
% 2.66/1.36  
% 2.66/1.36  %Foreground operators:
% 2.66/1.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.66/1.36  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.66/1.36  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.66/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.36  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.66/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.66/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.66/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.66/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.36  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.66/1.36  
% 2.66/1.37  tff(f_89, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(A) & v2_funct_1(B)) => (k2_funct_1(k5_relat_1(A, B)) = k5_relat_1(k2_funct_1(B), k2_funct_1(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_funct_1)).
% 2.66/1.37  tff(f_58, axiom, (![A, B]: ((((v1_relat_1(A) & v1_funct_1(A)) & v1_relat_1(B)) & v1_funct_1(B)) => (v1_relat_1(k5_relat_1(A, B)) & v1_funct_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funct_1)).
% 2.66/1.37  tff(f_31, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.66/1.37  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(A) & v2_funct_1(B)) => v2_funct_1(k5_relat_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_funct_1)).
% 2.66/1.37  tff(f_46, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 2.66/1.37  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 2.66/1.37  tff(c_26, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.66/1.37  tff(c_24, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.66/1.37  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.66/1.37  tff(c_20, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.66/1.37  tff(c_18, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.66/1.37  tff(c_16, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.66/1.37  tff(c_8, plain, (![A_7, B_8]: (v1_funct_1(k5_relat_1(A_7, B_8)) | ~v1_funct_1(B_8) | ~v1_relat_1(B_8) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.66/1.37  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k5_relat_1(A_1, B_2)) | ~v1_relat_1(B_2) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.66/1.37  tff(c_120, plain, (![A_21, B_22]: (v2_funct_1(k5_relat_1(A_21, B_22)) | ~v2_funct_1(B_22) | ~v2_funct_1(A_21) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.66/1.37  tff(c_6, plain, (![A_6]: (k4_relat_1(A_6)=k2_funct_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.66/1.37  tff(c_376, plain, (![A_34, B_35]: (k4_relat_1(k5_relat_1(A_34, B_35))=k2_funct_1(k5_relat_1(A_34, B_35)) | ~v1_funct_1(k5_relat_1(A_34, B_35)) | ~v1_relat_1(k5_relat_1(A_34, B_35)) | ~v2_funct_1(B_35) | ~v2_funct_1(A_34) | ~v1_funct_1(B_35) | ~v1_relat_1(B_35) | ~v1_funct_1(A_34) | ~v1_relat_1(A_34))), inference(resolution, [status(thm)], [c_120, c_6])).
% 2.66/1.37  tff(c_412, plain, (![A_36, B_37]: (k4_relat_1(k5_relat_1(A_36, B_37))=k2_funct_1(k5_relat_1(A_36, B_37)) | ~v1_funct_1(k5_relat_1(A_36, B_37)) | ~v2_funct_1(B_37) | ~v2_funct_1(A_36) | ~v1_funct_1(B_37) | ~v1_funct_1(A_36) | ~v1_relat_1(B_37) | ~v1_relat_1(A_36))), inference(resolution, [status(thm)], [c_2, c_376])).
% 2.66/1.37  tff(c_448, plain, (![A_38, B_39]: (k4_relat_1(k5_relat_1(A_38, B_39))=k2_funct_1(k5_relat_1(A_38, B_39)) | ~v2_funct_1(B_39) | ~v2_funct_1(A_38) | ~v1_funct_1(B_39) | ~v1_relat_1(B_39) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(resolution, [status(thm)], [c_8, c_412])).
% 2.66/1.37  tff(c_28, plain, (![A_15]: (k4_relat_1(A_15)=k2_funct_1(A_15) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.66/1.37  tff(c_31, plain, (k4_relat_1('#skF_2')=k2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_16, c_28])).
% 2.66/1.37  tff(c_37, plain, (k4_relat_1('#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_31])).
% 2.66/1.37  tff(c_34, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_18, c_28])).
% 2.66/1.37  tff(c_40, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_34])).
% 2.66/1.37  tff(c_50, plain, (![B_18, A_19]: (k5_relat_1(k4_relat_1(B_18), k4_relat_1(A_19))=k4_relat_1(k5_relat_1(A_19, B_18)) | ~v1_relat_1(B_18) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.66/1.37  tff(c_68, plain, (![B_18]: (k5_relat_1(k4_relat_1(B_18), k2_funct_1('#skF_1'))=k4_relat_1(k5_relat_1('#skF_1', B_18)) | ~v1_relat_1(B_18) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_50])).
% 2.66/1.37  tff(c_147, plain, (![B_23]: (k5_relat_1(k4_relat_1(B_23), k2_funct_1('#skF_1'))=k4_relat_1(k5_relat_1('#skF_1', B_23)) | ~v1_relat_1(B_23))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_68])).
% 2.66/1.37  tff(c_168, plain, (k5_relat_1(k2_funct_1('#skF_2'), k2_funct_1('#skF_1'))=k4_relat_1(k5_relat_1('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_37, c_147])).
% 2.66/1.37  tff(c_174, plain, (k5_relat_1(k2_funct_1('#skF_2'), k2_funct_1('#skF_1'))=k4_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_168])).
% 2.66/1.37  tff(c_14, plain, (k5_relat_1(k2_funct_1('#skF_2'), k2_funct_1('#skF_1'))!=k2_funct_1(k5_relat_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.66/1.37  tff(c_175, plain, (k4_relat_1(k5_relat_1('#skF_1', '#skF_2'))!=k2_funct_1(k5_relat_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_14])).
% 2.66/1.37  tff(c_472, plain, (~v2_funct_1('#skF_2') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_448, c_175])).
% 2.66/1.37  tff(c_519, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_20, c_18, c_16, c_472])).
% 2.66/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.37  
% 2.66/1.37  Inference rules
% 2.66/1.37  ----------------------
% 2.66/1.37  #Ref     : 0
% 2.66/1.37  #Sup     : 143
% 2.66/1.37  #Fact    : 0
% 2.66/1.37  #Define  : 0
% 2.66/1.37  #Split   : 2
% 2.66/1.37  #Chain   : 0
% 2.66/1.37  #Close   : 0
% 2.66/1.37  
% 2.66/1.37  Ordering : KBO
% 2.66/1.37  
% 2.66/1.37  Simplification rules
% 2.66/1.37  ----------------------
% 2.66/1.37  #Subsume      : 72
% 2.66/1.37  #Demod        : 47
% 2.66/1.37  #Tautology    : 27
% 2.66/1.37  #SimpNegUnit  : 0
% 2.66/1.37  #BackRed      : 1
% 2.66/1.37  
% 2.66/1.37  #Partial instantiations: 0
% 2.66/1.37  #Strategies tried      : 1
% 2.66/1.37  
% 2.66/1.37  Timing (in seconds)
% 2.66/1.37  ----------------------
% 2.66/1.38  Preprocessing        : 0.30
% 2.66/1.38  Parsing              : 0.16
% 2.66/1.38  CNF conversion       : 0.02
% 2.66/1.38  Main loop            : 0.32
% 2.66/1.38  Inferencing          : 0.12
% 2.66/1.38  Reduction            : 0.10
% 2.66/1.38  Demodulation         : 0.07
% 2.66/1.38  BG Simplification    : 0.02
% 2.66/1.38  Subsumption          : 0.07
% 2.66/1.38  Abstraction          : 0.02
% 2.66/1.38  MUC search           : 0.00
% 2.66/1.38  Cooper               : 0.00
% 2.66/1.38  Total                : 0.64
% 2.66/1.38  Index Insertion      : 0.00
% 2.66/1.38  Index Deletion       : 0.00
% 2.66/1.38  Index Matching       : 0.00
% 2.66/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
