%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:59 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   43 (  79 expanded)
%              Number of leaves         :   20 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :  105 ( 240 expanded)
%              Number of equality atoms :    7 (  14 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_87,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & r1_tarski(k2_relat_1(B),k1_relat_1(A)) )
           => v2_funct_1(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_30,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_8,plain,(
    ! [A_3] :
      ( v1_funct_1(k2_funct_1(A_3))
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_3] :
      ( v1_relat_1(k2_funct_1(A_3))
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_14,plain,(
    ! [A_4] : v2_funct_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [A_9] :
      ( k5_relat_1(k2_funct_1(A_9),A_9) = k6_relat_1(k2_relat_1(A_9))
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_8] :
      ( k2_relat_1(k2_funct_1(A_8)) = k1_relat_1(A_8)
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_82,plain,(
    ! [B_21,A_22] :
      ( v2_funct_1(B_21)
      | ~ r1_tarski(k2_relat_1(B_21),k1_relat_1(A_22))
      | ~ v2_funct_1(k5_relat_1(B_21,A_22))
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_101,plain,(
    ! [A_25,A_26] :
      ( v2_funct_1(k2_funct_1(A_25))
      | ~ r1_tarski(k1_relat_1(A_25),k1_relat_1(A_26))
      | ~ v2_funct_1(k5_relat_1(k2_funct_1(A_25),A_26))
      | ~ v1_funct_1(k2_funct_1(A_25))
      | ~ v1_relat_1(k2_funct_1(A_25))
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26)
      | ~ v2_funct_1(A_25)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_82])).

tff(c_113,plain,(
    ! [A_27] :
      ( v2_funct_1(k2_funct_1(A_27))
      | ~ v2_funct_1(k5_relat_1(k2_funct_1(A_27),A_27))
      | ~ v1_funct_1(k2_funct_1(A_27))
      | ~ v1_relat_1(k2_funct_1(A_27))
      | ~ v2_funct_1(A_27)
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(resolution,[status(thm)],[c_6,c_101])).

tff(c_116,plain,(
    ! [A_9] :
      ( v2_funct_1(k2_funct_1(A_9))
      | ~ v2_funct_1(k6_relat_1(k2_relat_1(A_9)))
      | ~ v1_funct_1(k2_funct_1(A_9))
      | ~ v1_relat_1(k2_funct_1(A_9))
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9)
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_113])).

tff(c_119,plain,(
    ! [A_28] :
      ( v2_funct_1(k2_funct_1(A_28))
      | ~ v1_funct_1(k2_funct_1(A_28))
      | ~ v1_relat_1(k2_funct_1(A_28))
      | ~ v2_funct_1(A_28)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_116])).

tff(c_26,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_122,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_119,c_26])).

tff(c_125,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_122])).

tff(c_126,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_125])).

tff(c_129,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_126])).

tff(c_133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_129])).

tff(c_134,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_125])).

tff(c_138,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_134])).

tff(c_142,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_138])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 19:57:20 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.25  
% 2.12/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.26  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 2.12/1.26  
% 2.12/1.26  %Foreground sorts:
% 2.12/1.26  
% 2.12/1.26  
% 2.12/1.26  %Background operators:
% 2.12/1.26  
% 2.12/1.26  
% 2.12/1.26  %Foreground operators:
% 2.12/1.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.12/1.26  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.12/1.26  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.12/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.26  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.12/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.12/1.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.12/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.12/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.12/1.26  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.12/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.12/1.26  
% 2.12/1.27  tff(f_87, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_1)).
% 2.12/1.27  tff(f_39, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.12/1.27  tff(f_43, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 2.12/1.27  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 2.12/1.27  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.12/1.27  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 2.12/1.27  tff(f_58, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & r1_tarski(k2_relat_1(B), k1_relat_1(A))) => v2_funct_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_funct_1)).
% 2.12/1.27  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.12/1.27  tff(c_30, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.12/1.27  tff(c_8, plain, (![A_3]: (v1_funct_1(k2_funct_1(A_3)) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.12/1.27  tff(c_10, plain, (![A_3]: (v1_relat_1(k2_funct_1(A_3)) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.12/1.27  tff(c_28, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.12/1.27  tff(c_14, plain, (![A_4]: (v2_funct_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.12/1.27  tff(c_22, plain, (![A_9]: (k5_relat_1(k2_funct_1(A_9), A_9)=k6_relat_1(k2_relat_1(A_9)) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.12/1.27  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.12/1.27  tff(c_18, plain, (![A_8]: (k2_relat_1(k2_funct_1(A_8))=k1_relat_1(A_8) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.12/1.27  tff(c_82, plain, (![B_21, A_22]: (v2_funct_1(B_21) | ~r1_tarski(k2_relat_1(B_21), k1_relat_1(A_22)) | ~v2_funct_1(k5_relat_1(B_21, A_22)) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.12/1.27  tff(c_101, plain, (![A_25, A_26]: (v2_funct_1(k2_funct_1(A_25)) | ~r1_tarski(k1_relat_1(A_25), k1_relat_1(A_26)) | ~v2_funct_1(k5_relat_1(k2_funct_1(A_25), A_26)) | ~v1_funct_1(k2_funct_1(A_25)) | ~v1_relat_1(k2_funct_1(A_25)) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26) | ~v2_funct_1(A_25) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(superposition, [status(thm), theory('equality')], [c_18, c_82])).
% 2.12/1.27  tff(c_113, plain, (![A_27]: (v2_funct_1(k2_funct_1(A_27)) | ~v2_funct_1(k5_relat_1(k2_funct_1(A_27), A_27)) | ~v1_funct_1(k2_funct_1(A_27)) | ~v1_relat_1(k2_funct_1(A_27)) | ~v2_funct_1(A_27) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(resolution, [status(thm)], [c_6, c_101])).
% 2.12/1.27  tff(c_116, plain, (![A_9]: (v2_funct_1(k2_funct_1(A_9)) | ~v2_funct_1(k6_relat_1(k2_relat_1(A_9))) | ~v1_funct_1(k2_funct_1(A_9)) | ~v1_relat_1(k2_funct_1(A_9)) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(superposition, [status(thm), theory('equality')], [c_22, c_113])).
% 2.12/1.27  tff(c_119, plain, (![A_28]: (v2_funct_1(k2_funct_1(A_28)) | ~v1_funct_1(k2_funct_1(A_28)) | ~v1_relat_1(k2_funct_1(A_28)) | ~v2_funct_1(A_28) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_116])).
% 2.12/1.27  tff(c_26, plain, (~v2_funct_1(k2_funct_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.12/1.27  tff(c_122, plain, (~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_119, c_26])).
% 2.12/1.27  tff(c_125, plain, (~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_122])).
% 2.12/1.27  tff(c_126, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_125])).
% 2.12/1.27  tff(c_129, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_10, c_126])).
% 2.12/1.27  tff(c_133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_129])).
% 2.12/1.27  tff(c_134, plain, (~v1_funct_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_125])).
% 2.12/1.27  tff(c_138, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_8, c_134])).
% 2.12/1.27  tff(c_142, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_138])).
% 2.12/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.27  
% 2.12/1.27  Inference rules
% 2.12/1.27  ----------------------
% 2.12/1.27  #Ref     : 0
% 2.12/1.27  #Sup     : 21
% 2.12/1.27  #Fact    : 0
% 2.12/1.27  #Define  : 0
% 2.12/1.27  #Split   : 1
% 2.12/1.27  #Chain   : 0
% 2.12/1.27  #Close   : 0
% 2.12/1.27  
% 2.12/1.27  Ordering : KBO
% 2.12/1.27  
% 2.12/1.27  Simplification rules
% 2.12/1.27  ----------------------
% 2.12/1.27  #Subsume      : 2
% 2.12/1.27  #Demod        : 10
% 2.12/1.27  #Tautology    : 11
% 2.12/1.27  #SimpNegUnit  : 0
% 2.12/1.27  #BackRed      : 0
% 2.12/1.27  
% 2.12/1.27  #Partial instantiations: 0
% 2.12/1.27  #Strategies tried      : 1
% 2.12/1.27  
% 2.12/1.27  Timing (in seconds)
% 2.12/1.27  ----------------------
% 2.12/1.27  Preprocessing        : 0.32
% 2.12/1.27  Parsing              : 0.17
% 2.12/1.27  CNF conversion       : 0.02
% 2.12/1.27  Main loop            : 0.17
% 2.12/1.27  Inferencing          : 0.06
% 2.12/1.27  Reduction            : 0.05
% 2.12/1.27  Demodulation         : 0.04
% 2.12/1.27  BG Simplification    : 0.01
% 2.12/1.27  Subsumption          : 0.03
% 2.12/1.27  Abstraction          : 0.01
% 2.12/1.27  MUC search           : 0.00
% 2.12/1.27  Cooper               : 0.00
% 2.12/1.27  Total                : 0.53
% 2.12/1.27  Index Insertion      : 0.00
% 2.12/1.27  Index Deletion       : 0.00
% 2.12/1.27  Index Matching       : 0.00
% 2.12/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
