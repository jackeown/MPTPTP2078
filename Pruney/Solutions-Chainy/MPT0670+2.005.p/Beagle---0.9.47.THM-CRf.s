%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:20 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   44 (  62 expanded)
%              Number of leaves         :   21 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :   78 ( 122 expanded)
%              Number of equality atoms :   20 (  29 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k8_relat_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k1_relat_1(k8_relat_1(B,C)))
         => k1_funct_1(k8_relat_1(B,C),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k1_relat_1(k8_relat_1(B,C)))
      <=> ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(k1_funct_1(C,A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

tff(c_24,plain,(
    k1_funct_1(k8_relat_1('#skF_3','#skF_4'),'#skF_2') != k1_funct_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_30,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_28,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_26,plain,(
    r2_hidden('#skF_2',k1_relat_1(k8_relat_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_91,plain,(
    ! [C_27,A_28,B_29] :
      ( r2_hidden(k1_funct_1(C_27,A_28),B_29)
      | ~ r2_hidden(A_28,k1_relat_1(k8_relat_1(B_29,C_27)))
      | ~ v1_funct_1(C_27)
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_98,plain,
    ( r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_91])).

tff(c_102,plain,(
    r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_98])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k5_relat_1(B_2,k6_relat_1(A_1)) = k8_relat_1(A_1,B_2)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_3] : v1_funct_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_125,plain,(
    ! [C_34,B_35,A_36] :
      ( k1_funct_1(k5_relat_1(C_34,B_35),A_36) = k1_funct_1(B_35,k1_funct_1(C_34,A_36))
      | ~ r2_hidden(A_36,k1_relat_1(k5_relat_1(C_34,B_35)))
      | ~ v1_funct_1(C_34)
      | ~ v1_relat_1(C_34)
      | ~ v1_funct_1(B_35)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_132,plain,(
    ! [B_2,A_1,A_36] :
      ( k1_funct_1(k5_relat_1(B_2,k6_relat_1(A_1)),A_36) = k1_funct_1(k6_relat_1(A_1),k1_funct_1(B_2,A_36))
      | ~ r2_hidden(A_36,k1_relat_1(k8_relat_1(A_1,B_2)))
      | ~ v1_funct_1(B_2)
      | ~ v1_relat_1(B_2)
      | ~ v1_funct_1(k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1))
      | ~ v1_relat_1(B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_125])).

tff(c_136,plain,(
    ! [B_37,A_38,A_39] :
      ( k1_funct_1(k5_relat_1(B_37,k6_relat_1(A_38)),A_39) = k1_funct_1(k6_relat_1(A_38),k1_funct_1(B_37,A_39))
      | ~ r2_hidden(A_39,k1_relat_1(k8_relat_1(A_38,B_37)))
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6,c_132])).

tff(c_146,plain,
    ( k1_funct_1(k5_relat_1('#skF_4',k6_relat_1('#skF_3')),'#skF_2') = k1_funct_1(k6_relat_1('#skF_3'),k1_funct_1('#skF_4','#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_136])).

tff(c_151,plain,(
    k1_funct_1(k5_relat_1('#skF_4',k6_relat_1('#skF_3')),'#skF_2') = k1_funct_1(k6_relat_1('#skF_3'),k1_funct_1('#skF_4','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_146])).

tff(c_156,plain,
    ( k1_funct_1(k6_relat_1('#skF_3'),k1_funct_1('#skF_4','#skF_2')) = k1_funct_1(k8_relat_1('#skF_3','#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_151])).

tff(c_160,plain,(
    k1_funct_1(k6_relat_1('#skF_3'),k1_funct_1('#skF_4','#skF_2')) = k1_funct_1(k8_relat_1('#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_156])).

tff(c_14,plain,(
    ! [A_8,C_12] :
      ( k1_funct_1(k6_relat_1(A_8),C_12) = C_12
      | ~ r2_hidden(C_12,A_8)
      | ~ v1_funct_1(k6_relat_1(A_8))
      | ~ v1_relat_1(k6_relat_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_34,plain,(
    ! [A_8,C_12] :
      ( k1_funct_1(k6_relat_1(A_8),C_12) = C_12
      | ~ r2_hidden(C_12,A_8)
      | ~ v1_relat_1(k6_relat_1(A_8)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14])).

tff(c_38,plain,(
    ! [A_8,C_12] :
      ( k1_funct_1(k6_relat_1(A_8),C_12) = C_12
      | ~ r2_hidden(C_12,A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_34])).

tff(c_165,plain,
    ( k1_funct_1(k8_relat_1('#skF_3','#skF_4'),'#skF_2') = k1_funct_1('#skF_4','#skF_2')
    | ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_38])).

tff(c_172,plain,(
    k1_funct_1(k8_relat_1('#skF_3','#skF_4'),'#skF_2') = k1_funct_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_165])).

tff(c_174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_172])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:18:39 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.17  
% 1.90/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.17  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k8_relat_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.90/1.17  
% 1.90/1.17  %Foreground sorts:
% 1.90/1.17  
% 1.90/1.17  
% 1.90/1.17  %Background operators:
% 1.90/1.17  
% 1.90/1.17  
% 1.90/1.17  %Foreground operators:
% 1.90/1.17  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.90/1.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.90/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.90/1.17  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.90/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.90/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.90/1.17  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.90/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.90/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.90/1.17  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.90/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.90/1.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.90/1.17  
% 1.90/1.18  tff(f_78, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k8_relat_1(B, C))) => (k1_funct_1(k8_relat_1(B, C), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_1)).
% 1.90/1.18  tff(f_69, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k8_relat_1(B, C))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_funct_1)).
% 1.90/1.18  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 1.90/1.18  tff(f_33, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.90/1.18  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) => (k1_funct_1(k5_relat_1(C, B), A) = k1_funct_1(B, k1_funct_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_funct_1)).
% 1.90/1.18  tff(f_59, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 1.90/1.18  tff(c_24, plain, (k1_funct_1(k8_relat_1('#skF_3', '#skF_4'), '#skF_2')!=k1_funct_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.90/1.18  tff(c_30, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.90/1.18  tff(c_28, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.90/1.18  tff(c_26, plain, (r2_hidden('#skF_2', k1_relat_1(k8_relat_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.90/1.18  tff(c_91, plain, (![C_27, A_28, B_29]: (r2_hidden(k1_funct_1(C_27, A_28), B_29) | ~r2_hidden(A_28, k1_relat_1(k8_relat_1(B_29, C_27))) | ~v1_funct_1(C_27) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.90/1.18  tff(c_98, plain, (r2_hidden(k1_funct_1('#skF_4', '#skF_2'), '#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_91])).
% 1.90/1.18  tff(c_102, plain, (r2_hidden(k1_funct_1('#skF_4', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_98])).
% 1.90/1.18  tff(c_2, plain, (![B_2, A_1]: (k5_relat_1(B_2, k6_relat_1(A_1))=k8_relat_1(A_1, B_2) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.90/1.18  tff(c_4, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.90/1.18  tff(c_6, plain, (![A_3]: (v1_funct_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.90/1.18  tff(c_125, plain, (![C_34, B_35, A_36]: (k1_funct_1(k5_relat_1(C_34, B_35), A_36)=k1_funct_1(B_35, k1_funct_1(C_34, A_36)) | ~r2_hidden(A_36, k1_relat_1(k5_relat_1(C_34, B_35))) | ~v1_funct_1(C_34) | ~v1_relat_1(C_34) | ~v1_funct_1(B_35) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.90/1.18  tff(c_132, plain, (![B_2, A_1, A_36]: (k1_funct_1(k5_relat_1(B_2, k6_relat_1(A_1)), A_36)=k1_funct_1(k6_relat_1(A_1), k1_funct_1(B_2, A_36)) | ~r2_hidden(A_36, k1_relat_1(k8_relat_1(A_1, B_2))) | ~v1_funct_1(B_2) | ~v1_relat_1(B_2) | ~v1_funct_1(k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)) | ~v1_relat_1(B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_125])).
% 1.90/1.18  tff(c_136, plain, (![B_37, A_38, A_39]: (k1_funct_1(k5_relat_1(B_37, k6_relat_1(A_38)), A_39)=k1_funct_1(k6_relat_1(A_38), k1_funct_1(B_37, A_39)) | ~r2_hidden(A_39, k1_relat_1(k8_relat_1(A_38, B_37))) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6, c_132])).
% 1.90/1.18  tff(c_146, plain, (k1_funct_1(k5_relat_1('#skF_4', k6_relat_1('#skF_3')), '#skF_2')=k1_funct_1(k6_relat_1('#skF_3'), k1_funct_1('#skF_4', '#skF_2')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_136])).
% 1.90/1.18  tff(c_151, plain, (k1_funct_1(k5_relat_1('#skF_4', k6_relat_1('#skF_3')), '#skF_2')=k1_funct_1(k6_relat_1('#skF_3'), k1_funct_1('#skF_4', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_146])).
% 1.90/1.18  tff(c_156, plain, (k1_funct_1(k6_relat_1('#skF_3'), k1_funct_1('#skF_4', '#skF_2'))=k1_funct_1(k8_relat_1('#skF_3', '#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2, c_151])).
% 1.90/1.18  tff(c_160, plain, (k1_funct_1(k6_relat_1('#skF_3'), k1_funct_1('#skF_4', '#skF_2'))=k1_funct_1(k8_relat_1('#skF_3', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_156])).
% 1.90/1.18  tff(c_14, plain, (![A_8, C_12]: (k1_funct_1(k6_relat_1(A_8), C_12)=C_12 | ~r2_hidden(C_12, A_8) | ~v1_funct_1(k6_relat_1(A_8)) | ~v1_relat_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.90/1.18  tff(c_34, plain, (![A_8, C_12]: (k1_funct_1(k6_relat_1(A_8), C_12)=C_12 | ~r2_hidden(C_12, A_8) | ~v1_relat_1(k6_relat_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_14])).
% 1.90/1.18  tff(c_38, plain, (![A_8, C_12]: (k1_funct_1(k6_relat_1(A_8), C_12)=C_12 | ~r2_hidden(C_12, A_8))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_34])).
% 1.90/1.18  tff(c_165, plain, (k1_funct_1(k8_relat_1('#skF_3', '#skF_4'), '#skF_2')=k1_funct_1('#skF_4', '#skF_2') | ~r2_hidden(k1_funct_1('#skF_4', '#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_160, c_38])).
% 1.90/1.18  tff(c_172, plain, (k1_funct_1(k8_relat_1('#skF_3', '#skF_4'), '#skF_2')=k1_funct_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_165])).
% 1.90/1.18  tff(c_174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_172])).
% 1.90/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.18  
% 1.90/1.18  Inference rules
% 1.90/1.18  ----------------------
% 1.90/1.18  #Ref     : 0
% 1.90/1.18  #Sup     : 28
% 1.90/1.18  #Fact    : 0
% 1.90/1.18  #Define  : 0
% 1.90/1.18  #Split   : 0
% 1.90/1.18  #Chain   : 0
% 1.90/1.18  #Close   : 0
% 1.90/1.18  
% 1.90/1.18  Ordering : KBO
% 1.90/1.18  
% 1.90/1.18  Simplification rules
% 1.90/1.18  ----------------------
% 1.90/1.18  #Subsume      : 0
% 1.90/1.18  #Demod        : 31
% 1.90/1.18  #Tautology    : 15
% 1.90/1.18  #SimpNegUnit  : 1
% 1.90/1.18  #BackRed      : 1
% 1.90/1.18  
% 1.90/1.18  #Partial instantiations: 0
% 1.90/1.18  #Strategies tried      : 1
% 1.90/1.18  
% 1.90/1.18  Timing (in seconds)
% 1.90/1.18  ----------------------
% 1.90/1.19  Preprocessing        : 0.28
% 1.90/1.19  Parsing              : 0.15
% 1.90/1.19  CNF conversion       : 0.02
% 1.90/1.19  Main loop            : 0.16
% 1.90/1.19  Inferencing          : 0.06
% 1.90/1.19  Reduction            : 0.05
% 1.90/1.19  Demodulation         : 0.04
% 1.90/1.19  BG Simplification    : 0.01
% 1.90/1.19  Subsumption          : 0.02
% 1.90/1.19  Abstraction          : 0.01
% 1.90/1.19  MUC search           : 0.00
% 1.90/1.19  Cooper               : 0.00
% 1.90/1.19  Total                : 0.46
% 1.90/1.19  Index Insertion      : 0.00
% 2.01/1.19  Index Deletion       : 0.00
% 2.01/1.19  Index Matching       : 0.00
% 2.01/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
