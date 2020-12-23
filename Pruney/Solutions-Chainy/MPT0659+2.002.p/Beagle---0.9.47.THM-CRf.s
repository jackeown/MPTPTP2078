%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:08 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   43 (  69 expanded)
%              Number of leaves         :   16 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :  111 ( 235 expanded)
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

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( v2_funct_1(A)
                & v2_funct_1(B) )
             => k2_funct_1(k5_relat_1(A,B)) = k5_relat_1(k2_funct_1(B),k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_funct_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v1_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B)
        & v2_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v2_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_funct_1)).

tff(f_40,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_24,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_20,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_18,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_16,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( v1_funct_1(k5_relat_1(A_5,B_6))
      | ~ v1_funct_1(B_6)
      | ~ v1_relat_1(B_6)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( v1_relat_1(k5_relat_1(A_5,B_6))
      | ~ v1_funct_1(B_6)
      | ~ v1_relat_1(B_6)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_120,plain,(
    ! [A_18,B_19] :
      ( v2_funct_1(k5_relat_1(A_18,B_19))
      | ~ v2_funct_1(B_19)
      | ~ v1_funct_1(B_19)
      | ~ v1_relat_1(B_19)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4,plain,(
    ! [A_4] :
      ( k4_relat_1(A_4) = k2_funct_1(A_4)
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_348,plain,(
    ! [A_29,B_30] :
      ( k4_relat_1(k5_relat_1(A_29,B_30)) = k2_funct_1(k5_relat_1(A_29,B_30))
      | ~ v1_funct_1(k5_relat_1(A_29,B_30))
      | ~ v1_relat_1(k5_relat_1(A_29,B_30))
      | ~ v2_funct_1(B_30)
      | ~ v1_funct_1(B_30)
      | ~ v1_relat_1(B_30)
      | ~ v2_funct_1(A_29)
      | ~ v1_funct_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(resolution,[status(thm)],[c_120,c_4])).

tff(c_384,plain,(
    ! [A_31,B_32] :
      ( k4_relat_1(k5_relat_1(A_31,B_32)) = k2_funct_1(k5_relat_1(A_31,B_32))
      | ~ v1_funct_1(k5_relat_1(A_31,B_32))
      | ~ v2_funct_1(B_32)
      | ~ v2_funct_1(A_31)
      | ~ v1_funct_1(B_32)
      | ~ v1_relat_1(B_32)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(resolution,[status(thm)],[c_8,c_348])).

tff(c_420,plain,(
    ! [A_33,B_34] :
      ( k4_relat_1(k5_relat_1(A_33,B_34)) = k2_funct_1(k5_relat_1(A_33,B_34))
      | ~ v2_funct_1(B_34)
      | ~ v2_funct_1(A_33)
      | ~ v1_funct_1(B_34)
      | ~ v1_relat_1(B_34)
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(resolution,[status(thm)],[c_6,c_384])).

tff(c_27,plain,(
    ! [A_10] :
      ( k4_relat_1(A_10) = k2_funct_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_30,plain,
    ( k4_relat_1('#skF_2') = k2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_27])).

tff(c_36,plain,(
    k4_relat_1('#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_30])).

tff(c_33,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_27])).

tff(c_39,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_33])).

tff(c_50,plain,(
    ! [B_15,A_16] :
      ( k5_relat_1(k4_relat_1(B_15),k4_relat_1(A_16)) = k4_relat_1(k5_relat_1(A_16,B_15))
      | ~ v1_relat_1(B_15)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_68,plain,(
    ! [B_15] :
      ( k5_relat_1(k4_relat_1(B_15),k2_funct_1('#skF_1')) = k4_relat_1(k5_relat_1('#skF_1',B_15))
      | ~ v1_relat_1(B_15)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_50])).

tff(c_147,plain,(
    ! [B_20] :
      ( k5_relat_1(k4_relat_1(B_20),k2_funct_1('#skF_1')) = k4_relat_1(k5_relat_1('#skF_1',B_20))
      | ~ v1_relat_1(B_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_68])).

tff(c_168,plain,
    ( k5_relat_1(k2_funct_1('#skF_2'),k2_funct_1('#skF_1')) = k4_relat_1(k5_relat_1('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_147])).

tff(c_174,plain,(
    k5_relat_1(k2_funct_1('#skF_2'),k2_funct_1('#skF_1')) = k4_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_168])).

tff(c_14,plain,(
    k5_relat_1(k2_funct_1('#skF_2'),k2_funct_1('#skF_1')) != k2_funct_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_175,plain,(
    k4_relat_1(k5_relat_1('#skF_1','#skF_2')) != k2_funct_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_14])).

tff(c_441,plain,
    ( ~ v2_funct_1('#skF_2')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_175])).

tff(c_488,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_20,c_18,c_16,c_441])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:51:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.35  
% 2.49/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.35  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k4_relat_1 > k2_funct_1 > #skF_2 > #skF_1
% 2.49/1.35  
% 2.49/1.35  %Foreground sorts:
% 2.49/1.35  
% 2.49/1.35  
% 2.49/1.35  %Background operators:
% 2.49/1.35  
% 2.49/1.35  
% 2.49/1.35  %Foreground operators:
% 2.49/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.49/1.35  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.49/1.35  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.49/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.35  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.49/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.49/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.49/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.49/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.35  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.49/1.35  
% 2.49/1.36  tff(f_84, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(A) & v2_funct_1(B)) => (k2_funct_1(k5_relat_1(A, B)) = k5_relat_1(k2_funct_1(B), k2_funct_1(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_funct_1)).
% 2.49/1.36  tff(f_52, axiom, (![A, B]: ((((v1_relat_1(A) & v1_funct_1(A)) & v1_relat_1(B)) & v1_funct_1(B)) => (v1_relat_1(k5_relat_1(A, B)) & v1_funct_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_funct_1)).
% 2.49/1.36  tff(f_68, axiom, (![A, B]: ((((((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) & v1_relat_1(B)) & v1_funct_1(B)) & v2_funct_1(B)) => (v1_relat_1(k5_relat_1(A, B)) & v2_funct_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_funct_1)).
% 2.49/1.36  tff(f_40, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 2.49/1.36  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 2.49/1.36  tff(c_26, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.49/1.36  tff(c_24, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.49/1.36  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.49/1.36  tff(c_20, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.49/1.36  tff(c_18, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.49/1.36  tff(c_16, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.49/1.36  tff(c_6, plain, (![A_5, B_6]: (v1_funct_1(k5_relat_1(A_5, B_6)) | ~v1_funct_1(B_6) | ~v1_relat_1(B_6) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.49/1.36  tff(c_8, plain, (![A_5, B_6]: (v1_relat_1(k5_relat_1(A_5, B_6)) | ~v1_funct_1(B_6) | ~v1_relat_1(B_6) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.49/1.36  tff(c_120, plain, (![A_18, B_19]: (v2_funct_1(k5_relat_1(A_18, B_19)) | ~v2_funct_1(B_19) | ~v1_funct_1(B_19) | ~v1_relat_1(B_19) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.49/1.36  tff(c_4, plain, (![A_4]: (k4_relat_1(A_4)=k2_funct_1(A_4) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.49/1.36  tff(c_348, plain, (![A_29, B_30]: (k4_relat_1(k5_relat_1(A_29, B_30))=k2_funct_1(k5_relat_1(A_29, B_30)) | ~v1_funct_1(k5_relat_1(A_29, B_30)) | ~v1_relat_1(k5_relat_1(A_29, B_30)) | ~v2_funct_1(B_30) | ~v1_funct_1(B_30) | ~v1_relat_1(B_30) | ~v2_funct_1(A_29) | ~v1_funct_1(A_29) | ~v1_relat_1(A_29))), inference(resolution, [status(thm)], [c_120, c_4])).
% 2.49/1.36  tff(c_384, plain, (![A_31, B_32]: (k4_relat_1(k5_relat_1(A_31, B_32))=k2_funct_1(k5_relat_1(A_31, B_32)) | ~v1_funct_1(k5_relat_1(A_31, B_32)) | ~v2_funct_1(B_32) | ~v2_funct_1(A_31) | ~v1_funct_1(B_32) | ~v1_relat_1(B_32) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(resolution, [status(thm)], [c_8, c_348])).
% 2.49/1.36  tff(c_420, plain, (![A_33, B_34]: (k4_relat_1(k5_relat_1(A_33, B_34))=k2_funct_1(k5_relat_1(A_33, B_34)) | ~v2_funct_1(B_34) | ~v2_funct_1(A_33) | ~v1_funct_1(B_34) | ~v1_relat_1(B_34) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(resolution, [status(thm)], [c_6, c_384])).
% 2.49/1.36  tff(c_27, plain, (![A_10]: (k4_relat_1(A_10)=k2_funct_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.49/1.36  tff(c_30, plain, (k4_relat_1('#skF_2')=k2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_16, c_27])).
% 2.49/1.36  tff(c_36, plain, (k4_relat_1('#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_30])).
% 2.49/1.36  tff(c_33, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_18, c_27])).
% 2.49/1.36  tff(c_39, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_33])).
% 2.49/1.36  tff(c_50, plain, (![B_15, A_16]: (k5_relat_1(k4_relat_1(B_15), k4_relat_1(A_16))=k4_relat_1(k5_relat_1(A_16, B_15)) | ~v1_relat_1(B_15) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.49/1.36  tff(c_68, plain, (![B_15]: (k5_relat_1(k4_relat_1(B_15), k2_funct_1('#skF_1'))=k4_relat_1(k5_relat_1('#skF_1', B_15)) | ~v1_relat_1(B_15) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_39, c_50])).
% 2.49/1.36  tff(c_147, plain, (![B_20]: (k5_relat_1(k4_relat_1(B_20), k2_funct_1('#skF_1'))=k4_relat_1(k5_relat_1('#skF_1', B_20)) | ~v1_relat_1(B_20))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_68])).
% 2.49/1.36  tff(c_168, plain, (k5_relat_1(k2_funct_1('#skF_2'), k2_funct_1('#skF_1'))=k4_relat_1(k5_relat_1('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_36, c_147])).
% 2.49/1.36  tff(c_174, plain, (k5_relat_1(k2_funct_1('#skF_2'), k2_funct_1('#skF_1'))=k4_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_168])).
% 2.49/1.36  tff(c_14, plain, (k5_relat_1(k2_funct_1('#skF_2'), k2_funct_1('#skF_1'))!=k2_funct_1(k5_relat_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.49/1.36  tff(c_175, plain, (k4_relat_1(k5_relat_1('#skF_1', '#skF_2'))!=k2_funct_1(k5_relat_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_14])).
% 2.49/1.36  tff(c_441, plain, (~v2_funct_1('#skF_2') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_420, c_175])).
% 2.49/1.36  tff(c_488, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_20, c_18, c_16, c_441])).
% 2.49/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.36  
% 2.49/1.36  Inference rules
% 2.49/1.36  ----------------------
% 2.49/1.36  #Ref     : 0
% 2.49/1.36  #Sup     : 133
% 2.49/1.36  #Fact    : 0
% 2.49/1.36  #Define  : 0
% 2.49/1.36  #Split   : 2
% 2.49/1.36  #Chain   : 0
% 2.49/1.36  #Close   : 0
% 2.49/1.36  
% 2.49/1.36  Ordering : KBO
% 2.49/1.36  
% 2.49/1.36  Simplification rules
% 2.49/1.36  ----------------------
% 2.49/1.36  #Subsume      : 62
% 2.49/1.36  #Demod        : 47
% 2.49/1.36  #Tautology    : 27
% 2.49/1.36  #SimpNegUnit  : 0
% 2.49/1.36  #BackRed      : 1
% 2.49/1.36  
% 2.49/1.36  #Partial instantiations: 0
% 2.49/1.36  #Strategies tried      : 1
% 2.49/1.36  
% 2.49/1.36  Timing (in seconds)
% 2.49/1.36  ----------------------
% 2.49/1.37  Preprocessing        : 0.29
% 2.49/1.37  Parsing              : 0.16
% 2.49/1.37  CNF conversion       : 0.02
% 2.49/1.37  Main loop            : 0.31
% 2.49/1.37  Inferencing          : 0.11
% 2.49/1.37  Reduction            : 0.10
% 2.49/1.37  Demodulation         : 0.07
% 2.49/1.37  BG Simplification    : 0.02
% 2.49/1.37  Subsumption          : 0.07
% 2.49/1.37  Abstraction          : 0.02
% 2.49/1.37  MUC search           : 0.00
% 2.49/1.37  Cooper               : 0.00
% 2.49/1.37  Total                : 0.63
% 2.49/1.37  Index Insertion      : 0.00
% 2.49/1.37  Index Deletion       : 0.00
% 2.49/1.37  Index Matching       : 0.00
% 2.49/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
