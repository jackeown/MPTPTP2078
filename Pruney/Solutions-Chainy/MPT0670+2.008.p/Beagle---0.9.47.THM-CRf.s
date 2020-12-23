%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:20 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   42 (  59 expanded)
%              Number of leaves         :   20 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :   70 ( 119 expanded)
%              Number of equality atoms :   14 (  23 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k8_relat_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k1_relat_1(k8_relat_1(B,C)))
         => k1_funct_1(k8_relat_1(B,C),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k1_relat_1(k8_relat_1(B,C)))
      <=> ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(k1_funct_1(C,A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k1_funct_1(k6_relat_1(B),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_1)).

tff(c_18,plain,(
    k1_funct_1(k8_relat_1('#skF_2','#skF_3'),'#skF_1') != k1_funct_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_22,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_20,plain,(
    r2_hidden('#skF_1',k1_relat_1(k8_relat_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_52,plain,(
    ! [C_22,A_23,B_24] :
      ( r2_hidden(k1_funct_1(C_22,A_23),B_24)
      | ~ r2_hidden(A_23,k1_relat_1(k8_relat_1(B_24,C_22)))
      | ~ v1_funct_1(C_22)
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_55,plain,
    ( r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_52])).

tff(c_58,plain,(
    r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_55])).

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

tff(c_45,plain,(
    ! [A_19,C_20,B_21] :
      ( r2_hidden(A_19,k1_relat_1(C_20))
      | ~ r2_hidden(A_19,k1_relat_1(k8_relat_1(B_21,C_20)))
      | ~ v1_funct_1(C_20)
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_48,plain,
    ( r2_hidden('#skF_1',k1_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_45])).

tff(c_51,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_48])).

tff(c_68,plain,(
    ! [B_28,C_29,A_30] :
      ( k1_funct_1(k5_relat_1(B_28,C_29),A_30) = k1_funct_1(C_29,k1_funct_1(B_28,A_30))
      | ~ r2_hidden(A_30,k1_relat_1(B_28))
      | ~ v1_funct_1(C_29)
      | ~ v1_relat_1(C_29)
      | ~ v1_funct_1(B_28)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_72,plain,(
    ! [C_29] :
      ( k1_funct_1(k5_relat_1('#skF_3',C_29),'#skF_1') = k1_funct_1(C_29,k1_funct_1('#skF_3','#skF_1'))
      | ~ v1_funct_1(C_29)
      | ~ v1_relat_1(C_29)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_51,c_68])).

tff(c_80,plain,(
    ! [C_31] :
      ( k1_funct_1(k5_relat_1('#skF_3',C_31),'#skF_1') = k1_funct_1(C_31,k1_funct_1('#skF_3','#skF_1'))
      | ~ v1_funct_1(C_31)
      | ~ v1_relat_1(C_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_72])).

tff(c_90,plain,(
    ! [A_1] :
      ( k1_funct_1(k6_relat_1(A_1),k1_funct_1('#skF_3','#skF_1')) = k1_funct_1(k8_relat_1(A_1,'#skF_3'),'#skF_1')
      | ~ v1_funct_1(k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_80])).

tff(c_96,plain,(
    ! [A_32] : k1_funct_1(k6_relat_1(A_32),k1_funct_1('#skF_3','#skF_1')) = k1_funct_1(k8_relat_1(A_32,'#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_4,c_6,c_90])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( k1_funct_1(k6_relat_1(B_9),A_8) = A_8
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_112,plain,(
    ! [A_33] :
      ( k1_funct_1(k8_relat_1(A_33,'#skF_3'),'#skF_1') = k1_funct_1('#skF_3','#skF_1')
      | ~ r2_hidden(k1_funct_1('#skF_3','#skF_1'),A_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_10])).

tff(c_119,plain,(
    k1_funct_1(k8_relat_1('#skF_2','#skF_3'),'#skF_1') = k1_funct_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_112])).

tff(c_124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_119])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n018.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 13:44:26 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.21  
% 1.95/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.21  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k8_relat_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.95/1.21  
% 1.95/1.21  %Foreground sorts:
% 1.95/1.21  
% 1.95/1.21  
% 1.95/1.21  %Background operators:
% 1.95/1.21  
% 1.95/1.21  
% 1.95/1.21  %Foreground operators:
% 1.95/1.21  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.95/1.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.95/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.95/1.21  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.95/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.95/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.21  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.95/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.95/1.21  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.95/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.95/1.21  
% 1.95/1.22  tff(f_69, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k8_relat_1(B, C))) => (k1_funct_1(k8_relat_1(B, C), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_1)).
% 1.95/1.22  tff(f_60, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k8_relat_1(B, C))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_funct_1)).
% 1.95/1.22  tff(f_33, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.95/1.22  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 1.95/1.22  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 1.95/1.22  tff(f_50, axiom, (![A, B]: (r2_hidden(A, B) => (k1_funct_1(k6_relat_1(B), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_1)).
% 1.95/1.22  tff(c_18, plain, (k1_funct_1(k8_relat_1('#skF_2', '#skF_3'), '#skF_1')!=k1_funct_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.95/1.22  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.95/1.22  tff(c_22, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.95/1.22  tff(c_20, plain, (r2_hidden('#skF_1', k1_relat_1(k8_relat_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.95/1.22  tff(c_52, plain, (![C_22, A_23, B_24]: (r2_hidden(k1_funct_1(C_22, A_23), B_24) | ~r2_hidden(A_23, k1_relat_1(k8_relat_1(B_24, C_22))) | ~v1_funct_1(C_22) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.95/1.22  tff(c_55, plain, (r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_52])).
% 1.95/1.22  tff(c_58, plain, (r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_55])).
% 1.95/1.22  tff(c_4, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.95/1.22  tff(c_6, plain, (![A_3]: (v1_funct_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.95/1.22  tff(c_2, plain, (![B_2, A_1]: (k5_relat_1(B_2, k6_relat_1(A_1))=k8_relat_1(A_1, B_2) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.95/1.22  tff(c_45, plain, (![A_19, C_20, B_21]: (r2_hidden(A_19, k1_relat_1(C_20)) | ~r2_hidden(A_19, k1_relat_1(k8_relat_1(B_21, C_20))) | ~v1_funct_1(C_20) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.95/1.22  tff(c_48, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_45])).
% 1.95/1.22  tff(c_51, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_48])).
% 1.95/1.22  tff(c_68, plain, (![B_28, C_29, A_30]: (k1_funct_1(k5_relat_1(B_28, C_29), A_30)=k1_funct_1(C_29, k1_funct_1(B_28, A_30)) | ~r2_hidden(A_30, k1_relat_1(B_28)) | ~v1_funct_1(C_29) | ~v1_relat_1(C_29) | ~v1_funct_1(B_28) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.95/1.22  tff(c_72, plain, (![C_29]: (k1_funct_1(k5_relat_1('#skF_3', C_29), '#skF_1')=k1_funct_1(C_29, k1_funct_1('#skF_3', '#skF_1')) | ~v1_funct_1(C_29) | ~v1_relat_1(C_29) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_51, c_68])).
% 1.95/1.22  tff(c_80, plain, (![C_31]: (k1_funct_1(k5_relat_1('#skF_3', C_31), '#skF_1')=k1_funct_1(C_31, k1_funct_1('#skF_3', '#skF_1')) | ~v1_funct_1(C_31) | ~v1_relat_1(C_31))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_72])).
% 1.95/1.22  tff(c_90, plain, (![A_1]: (k1_funct_1(k6_relat_1(A_1), k1_funct_1('#skF_3', '#skF_1'))=k1_funct_1(k8_relat_1(A_1, '#skF_3'), '#skF_1') | ~v1_funct_1(k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_80])).
% 1.95/1.22  tff(c_96, plain, (![A_32]: (k1_funct_1(k6_relat_1(A_32), k1_funct_1('#skF_3', '#skF_1'))=k1_funct_1(k8_relat_1(A_32, '#skF_3'), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_4, c_6, c_90])).
% 1.95/1.22  tff(c_10, plain, (![B_9, A_8]: (k1_funct_1(k6_relat_1(B_9), A_8)=A_8 | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.95/1.22  tff(c_112, plain, (![A_33]: (k1_funct_1(k8_relat_1(A_33, '#skF_3'), '#skF_1')=k1_funct_1('#skF_3', '#skF_1') | ~r2_hidden(k1_funct_1('#skF_3', '#skF_1'), A_33))), inference(superposition, [status(thm), theory('equality')], [c_96, c_10])).
% 1.95/1.22  tff(c_119, plain, (k1_funct_1(k8_relat_1('#skF_2', '#skF_3'), '#skF_1')=k1_funct_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_58, c_112])).
% 1.95/1.22  tff(c_124, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_119])).
% 1.95/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.22  
% 1.95/1.22  Inference rules
% 1.95/1.22  ----------------------
% 1.95/1.22  #Ref     : 0
% 1.95/1.22  #Sup     : 20
% 1.95/1.22  #Fact    : 0
% 1.95/1.22  #Define  : 0
% 1.95/1.22  #Split   : 1
% 1.95/1.22  #Chain   : 0
% 1.95/1.22  #Close   : 0
% 1.95/1.22  
% 1.95/1.22  Ordering : KBO
% 1.95/1.22  
% 1.95/1.22  Simplification rules
% 1.95/1.22  ----------------------
% 1.95/1.22  #Subsume      : 0
% 1.95/1.22  #Demod        : 9
% 1.95/1.22  #Tautology    : 10
% 1.95/1.22  #SimpNegUnit  : 1
% 1.95/1.22  #BackRed      : 0
% 1.95/1.22  
% 1.95/1.22  #Partial instantiations: 0
% 1.95/1.22  #Strategies tried      : 1
% 1.95/1.22  
% 1.95/1.22  Timing (in seconds)
% 1.95/1.22  ----------------------
% 1.95/1.23  Preprocessing        : 0.29
% 1.95/1.23  Parsing              : 0.16
% 1.95/1.23  CNF conversion       : 0.02
% 1.95/1.23  Main loop            : 0.16
% 1.95/1.23  Inferencing          : 0.07
% 1.95/1.23  Reduction            : 0.04
% 1.95/1.23  Demodulation         : 0.03
% 1.95/1.23  BG Simplification    : 0.01
% 1.95/1.23  Subsumption          : 0.03
% 1.95/1.23  Abstraction          : 0.01
% 1.95/1.23  MUC search           : 0.00
% 1.95/1.23  Cooper               : 0.00
% 1.95/1.23  Total                : 0.48
% 1.95/1.23  Index Insertion      : 0.00
% 1.95/1.23  Index Deletion       : 0.00
% 1.95/1.23  Index Matching       : 0.00
% 1.95/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
