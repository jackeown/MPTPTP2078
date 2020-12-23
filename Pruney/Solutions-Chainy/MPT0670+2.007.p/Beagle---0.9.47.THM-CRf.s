%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:20 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   45 (  66 expanded)
%              Number of leaves         :   21 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :   81 ( 136 expanded)
%              Number of equality atoms :   18 (  27 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

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

tff(c_4,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_3] : v1_funct_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k5_relat_1(B_2,k6_relat_1(A_1)) = k8_relat_1(A_1,B_2)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_68,plain,(
    ! [A_23,C_24,B_25] :
      ( r2_hidden(A_23,k1_relat_1(C_24))
      | ~ r2_hidden(A_23,k1_relat_1(k8_relat_1(B_25,C_24)))
      | ~ v1_funct_1(C_24)
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_71,plain,
    ( r2_hidden('#skF_2',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_68])).

tff(c_74,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_71])).

tff(c_125,plain,(
    ! [B_34,C_35,A_36] :
      ( k1_funct_1(k5_relat_1(B_34,C_35),A_36) = k1_funct_1(C_35,k1_funct_1(B_34,A_36))
      | ~ r2_hidden(A_36,k1_relat_1(B_34))
      | ~ v1_funct_1(C_35)
      | ~ v1_relat_1(C_35)
      | ~ v1_funct_1(B_34)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_131,plain,(
    ! [C_35] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_35),'#skF_2') = k1_funct_1(C_35,k1_funct_1('#skF_4','#skF_2'))
      | ~ v1_funct_1(C_35)
      | ~ v1_relat_1(C_35)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_74,c_125])).

tff(c_144,plain,(
    ! [C_37] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_37),'#skF_2') = k1_funct_1(C_37,k1_funct_1('#skF_4','#skF_2'))
      | ~ v1_funct_1(C_37)
      | ~ v1_relat_1(C_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_131])).

tff(c_154,plain,(
    ! [A_1] :
      ( k1_funct_1(k6_relat_1(A_1),k1_funct_1('#skF_4','#skF_2')) = k1_funct_1(k8_relat_1(A_1,'#skF_4'),'#skF_2')
      | ~ v1_funct_1(k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_144])).

tff(c_159,plain,(
    ! [A_38] : k1_funct_1(k6_relat_1(A_38),k1_funct_1('#skF_4','#skF_2')) = k1_funct_1(k8_relat_1(A_38,'#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_4,c_6,c_154])).

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

tff(c_176,plain,(
    ! [A_39] :
      ( k1_funct_1(k8_relat_1(A_39,'#skF_4'),'#skF_2') = k1_funct_1('#skF_4','#skF_2')
      | ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_38])).

tff(c_183,plain,(
    k1_funct_1(k8_relat_1('#skF_3','#skF_4'),'#skF_2') = k1_funct_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_102,c_176])).

tff(c_188,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_183])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:06:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.25  
% 2.00/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.25  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k8_relat_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.00/1.25  
% 2.00/1.25  %Foreground sorts:
% 2.00/1.25  
% 2.00/1.25  
% 2.00/1.25  %Background operators:
% 2.00/1.25  
% 2.00/1.25  
% 2.00/1.25  %Foreground operators:
% 2.00/1.25  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.00/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.00/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.00/1.25  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.00/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.00/1.25  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.00/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.00/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.00/1.25  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.00/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.00/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.00/1.25  
% 2.00/1.27  tff(f_78, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k8_relat_1(B, C))) => (k1_funct_1(k8_relat_1(B, C), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_1)).
% 2.00/1.27  tff(f_69, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k8_relat_1(B, C))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_funct_1)).
% 2.00/1.27  tff(f_33, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.00/1.27  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 2.00/1.27  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 2.00/1.27  tff(f_59, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 2.00/1.27  tff(c_24, plain, (k1_funct_1(k8_relat_1('#skF_3', '#skF_4'), '#skF_2')!=k1_funct_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.00/1.27  tff(c_30, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.00/1.27  tff(c_28, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.00/1.27  tff(c_26, plain, (r2_hidden('#skF_2', k1_relat_1(k8_relat_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.00/1.27  tff(c_91, plain, (![C_27, A_28, B_29]: (r2_hidden(k1_funct_1(C_27, A_28), B_29) | ~r2_hidden(A_28, k1_relat_1(k8_relat_1(B_29, C_27))) | ~v1_funct_1(C_27) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.00/1.27  tff(c_98, plain, (r2_hidden(k1_funct_1('#skF_4', '#skF_2'), '#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_91])).
% 2.00/1.27  tff(c_102, plain, (r2_hidden(k1_funct_1('#skF_4', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_98])).
% 2.00/1.27  tff(c_4, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.00/1.27  tff(c_6, plain, (![A_3]: (v1_funct_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.00/1.27  tff(c_2, plain, (![B_2, A_1]: (k5_relat_1(B_2, k6_relat_1(A_1))=k8_relat_1(A_1, B_2) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.00/1.27  tff(c_68, plain, (![A_23, C_24, B_25]: (r2_hidden(A_23, k1_relat_1(C_24)) | ~r2_hidden(A_23, k1_relat_1(k8_relat_1(B_25, C_24))) | ~v1_funct_1(C_24) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.00/1.27  tff(c_71, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_68])).
% 2.00/1.27  tff(c_74, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_71])).
% 2.00/1.27  tff(c_125, plain, (![B_34, C_35, A_36]: (k1_funct_1(k5_relat_1(B_34, C_35), A_36)=k1_funct_1(C_35, k1_funct_1(B_34, A_36)) | ~r2_hidden(A_36, k1_relat_1(B_34)) | ~v1_funct_1(C_35) | ~v1_relat_1(C_35) | ~v1_funct_1(B_34) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.00/1.27  tff(c_131, plain, (![C_35]: (k1_funct_1(k5_relat_1('#skF_4', C_35), '#skF_2')=k1_funct_1(C_35, k1_funct_1('#skF_4', '#skF_2')) | ~v1_funct_1(C_35) | ~v1_relat_1(C_35) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_74, c_125])).
% 2.00/1.27  tff(c_144, plain, (![C_37]: (k1_funct_1(k5_relat_1('#skF_4', C_37), '#skF_2')=k1_funct_1(C_37, k1_funct_1('#skF_4', '#skF_2')) | ~v1_funct_1(C_37) | ~v1_relat_1(C_37))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_131])).
% 2.00/1.27  tff(c_154, plain, (![A_1]: (k1_funct_1(k6_relat_1(A_1), k1_funct_1('#skF_4', '#skF_2'))=k1_funct_1(k8_relat_1(A_1, '#skF_4'), '#skF_2') | ~v1_funct_1(k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_144])).
% 2.00/1.27  tff(c_159, plain, (![A_38]: (k1_funct_1(k6_relat_1(A_38), k1_funct_1('#skF_4', '#skF_2'))=k1_funct_1(k8_relat_1(A_38, '#skF_4'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_4, c_6, c_154])).
% 2.00/1.27  tff(c_14, plain, (![A_8, C_12]: (k1_funct_1(k6_relat_1(A_8), C_12)=C_12 | ~r2_hidden(C_12, A_8) | ~v1_funct_1(k6_relat_1(A_8)) | ~v1_relat_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.00/1.27  tff(c_34, plain, (![A_8, C_12]: (k1_funct_1(k6_relat_1(A_8), C_12)=C_12 | ~r2_hidden(C_12, A_8) | ~v1_relat_1(k6_relat_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_14])).
% 2.00/1.27  tff(c_38, plain, (![A_8, C_12]: (k1_funct_1(k6_relat_1(A_8), C_12)=C_12 | ~r2_hidden(C_12, A_8))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_34])).
% 2.00/1.27  tff(c_176, plain, (![A_39]: (k1_funct_1(k8_relat_1(A_39, '#skF_4'), '#skF_2')=k1_funct_1('#skF_4', '#skF_2') | ~r2_hidden(k1_funct_1('#skF_4', '#skF_2'), A_39))), inference(superposition, [status(thm), theory('equality')], [c_159, c_38])).
% 2.00/1.27  tff(c_183, plain, (k1_funct_1(k8_relat_1('#skF_3', '#skF_4'), '#skF_2')=k1_funct_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_102, c_176])).
% 2.00/1.27  tff(c_188, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_183])).
% 2.00/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.27  
% 2.00/1.27  Inference rules
% 2.00/1.27  ----------------------
% 2.00/1.27  #Ref     : 0
% 2.00/1.27  #Sup     : 30
% 2.00/1.27  #Fact    : 0
% 2.00/1.27  #Define  : 0
% 2.00/1.27  #Split   : 1
% 2.00/1.27  #Chain   : 0
% 2.00/1.27  #Close   : 0
% 2.00/1.27  
% 2.00/1.27  Ordering : KBO
% 2.00/1.27  
% 2.00/1.27  Simplification rules
% 2.00/1.27  ----------------------
% 2.00/1.27  #Subsume      : 0
% 2.00/1.27  #Demod        : 31
% 2.00/1.27  #Tautology    : 16
% 2.00/1.27  #SimpNegUnit  : 1
% 2.00/1.27  #BackRed      : 0
% 2.00/1.27  
% 2.00/1.27  #Partial instantiations: 0
% 2.00/1.27  #Strategies tried      : 1
% 2.00/1.27  
% 2.00/1.27  Timing (in seconds)
% 2.00/1.27  ----------------------
% 2.00/1.27  Preprocessing        : 0.30
% 2.00/1.27  Parsing              : 0.17
% 2.00/1.27  CNF conversion       : 0.02
% 2.00/1.27  Main loop            : 0.19
% 2.00/1.27  Inferencing          : 0.07
% 2.00/1.27  Reduction            : 0.06
% 2.00/1.27  Demodulation         : 0.05
% 2.00/1.27  BG Simplification    : 0.01
% 2.00/1.27  Subsumption          : 0.03
% 2.00/1.27  Abstraction          : 0.01
% 2.00/1.27  MUC search           : 0.00
% 2.00/1.27  Cooper               : 0.00
% 2.00/1.27  Total                : 0.51
% 2.00/1.27  Index Insertion      : 0.00
% 2.00/1.27  Index Deletion       : 0.00
% 2.00/1.27  Index Matching       : 0.00
% 2.00/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
