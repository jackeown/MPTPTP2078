%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:20 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   41 (  55 expanded)
%              Number of leaves         :   20 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :   67 ( 105 expanded)
%              Number of equality atoms :   16 (  25 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_1)).

tff(f_60,axiom,(
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

tff(f_50,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k1_funct_1(k6_relat_1(B),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_1)).

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

tff(c_68,plain,(
    ! [C_28,B_29,A_30] :
      ( k1_funct_1(k5_relat_1(C_28,B_29),A_30) = k1_funct_1(B_29,k1_funct_1(C_28,A_30))
      | ~ r2_hidden(A_30,k1_relat_1(k5_relat_1(C_28,B_29)))
      | ~ v1_funct_1(C_28)
      | ~ v1_relat_1(C_28)
      | ~ v1_funct_1(B_29)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_71,plain,(
    ! [B_2,A_1,A_30] :
      ( k1_funct_1(k5_relat_1(B_2,k6_relat_1(A_1)),A_30) = k1_funct_1(k6_relat_1(A_1),k1_funct_1(B_2,A_30))
      | ~ r2_hidden(A_30,k1_relat_1(k8_relat_1(A_1,B_2)))
      | ~ v1_funct_1(B_2)
      | ~ v1_relat_1(B_2)
      | ~ v1_funct_1(k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1))
      | ~ v1_relat_1(B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_68])).

tff(c_74,plain,(
    ! [B_31,A_32,A_33] :
      ( k1_funct_1(k5_relat_1(B_31,k6_relat_1(A_32)),A_33) = k1_funct_1(k6_relat_1(A_32),k1_funct_1(B_31,A_33))
      | ~ r2_hidden(A_33,k1_relat_1(k8_relat_1(A_32,B_31)))
      | ~ v1_funct_1(B_31)
      | ~ v1_relat_1(B_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6,c_71])).

tff(c_80,plain,
    ( k1_funct_1(k5_relat_1('#skF_3',k6_relat_1('#skF_2')),'#skF_1') = k1_funct_1(k6_relat_1('#skF_2'),k1_funct_1('#skF_3','#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_74])).

tff(c_84,plain,(
    k1_funct_1(k5_relat_1('#skF_3',k6_relat_1('#skF_2')),'#skF_1') = k1_funct_1(k6_relat_1('#skF_2'),k1_funct_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_80])).

tff(c_89,plain,
    ( k1_funct_1(k6_relat_1('#skF_2'),k1_funct_1('#skF_3','#skF_1')) = k1_funct_1(k8_relat_1('#skF_2','#skF_3'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_84])).

tff(c_93,plain,(
    k1_funct_1(k6_relat_1('#skF_2'),k1_funct_1('#skF_3','#skF_1')) = k1_funct_1(k8_relat_1('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_89])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( k1_funct_1(k6_relat_1(B_9),A_8) = A_8
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_98,plain,
    ( k1_funct_1(k8_relat_1('#skF_2','#skF_3'),'#skF_1') = k1_funct_1('#skF_3','#skF_1')
    | ~ r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_10])).

tff(c_105,plain,(
    k1_funct_1(k8_relat_1('#skF_2','#skF_3'),'#skF_1') = k1_funct_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_98])).

tff(c_107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_105])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:56:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.16  
% 1.81/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.17  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k8_relat_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.81/1.17  
% 1.81/1.17  %Foreground sorts:
% 1.81/1.17  
% 1.81/1.17  
% 1.81/1.17  %Background operators:
% 1.81/1.17  
% 1.81/1.17  
% 1.81/1.17  %Foreground operators:
% 1.81/1.17  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.81/1.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.81/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.81/1.17  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.81/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.81/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.81/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.81/1.17  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.81/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.81/1.17  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.81/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.81/1.17  
% 1.81/1.18  tff(f_69, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k8_relat_1(B, C))) => (k1_funct_1(k8_relat_1(B, C), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_1)).
% 1.81/1.18  tff(f_60, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k8_relat_1(B, C))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_funct_1)).
% 1.81/1.18  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 1.81/1.18  tff(f_33, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.81/1.18  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) => (k1_funct_1(k5_relat_1(C, B), A) = k1_funct_1(B, k1_funct_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_funct_1)).
% 1.81/1.18  tff(f_50, axiom, (![A, B]: (r2_hidden(A, B) => (k1_funct_1(k6_relat_1(B), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_1)).
% 1.81/1.18  tff(c_18, plain, (k1_funct_1(k8_relat_1('#skF_2', '#skF_3'), '#skF_1')!=k1_funct_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.81/1.18  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.81/1.18  tff(c_22, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.81/1.18  tff(c_20, plain, (r2_hidden('#skF_1', k1_relat_1(k8_relat_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.81/1.18  tff(c_52, plain, (![C_22, A_23, B_24]: (r2_hidden(k1_funct_1(C_22, A_23), B_24) | ~r2_hidden(A_23, k1_relat_1(k8_relat_1(B_24, C_22))) | ~v1_funct_1(C_22) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.81/1.18  tff(c_55, plain, (r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_52])).
% 1.81/1.18  tff(c_58, plain, (r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_55])).
% 1.81/1.18  tff(c_2, plain, (![B_2, A_1]: (k5_relat_1(B_2, k6_relat_1(A_1))=k8_relat_1(A_1, B_2) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.81/1.18  tff(c_4, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.81/1.18  tff(c_6, plain, (![A_3]: (v1_funct_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.81/1.18  tff(c_68, plain, (![C_28, B_29, A_30]: (k1_funct_1(k5_relat_1(C_28, B_29), A_30)=k1_funct_1(B_29, k1_funct_1(C_28, A_30)) | ~r2_hidden(A_30, k1_relat_1(k5_relat_1(C_28, B_29))) | ~v1_funct_1(C_28) | ~v1_relat_1(C_28) | ~v1_funct_1(B_29) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.81/1.18  tff(c_71, plain, (![B_2, A_1, A_30]: (k1_funct_1(k5_relat_1(B_2, k6_relat_1(A_1)), A_30)=k1_funct_1(k6_relat_1(A_1), k1_funct_1(B_2, A_30)) | ~r2_hidden(A_30, k1_relat_1(k8_relat_1(A_1, B_2))) | ~v1_funct_1(B_2) | ~v1_relat_1(B_2) | ~v1_funct_1(k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)) | ~v1_relat_1(B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_68])).
% 1.81/1.18  tff(c_74, plain, (![B_31, A_32, A_33]: (k1_funct_1(k5_relat_1(B_31, k6_relat_1(A_32)), A_33)=k1_funct_1(k6_relat_1(A_32), k1_funct_1(B_31, A_33)) | ~r2_hidden(A_33, k1_relat_1(k8_relat_1(A_32, B_31))) | ~v1_funct_1(B_31) | ~v1_relat_1(B_31))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6, c_71])).
% 1.81/1.18  tff(c_80, plain, (k1_funct_1(k5_relat_1('#skF_3', k6_relat_1('#skF_2')), '#skF_1')=k1_funct_1(k6_relat_1('#skF_2'), k1_funct_1('#skF_3', '#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_74])).
% 1.81/1.18  tff(c_84, plain, (k1_funct_1(k5_relat_1('#skF_3', k6_relat_1('#skF_2')), '#skF_1')=k1_funct_1(k6_relat_1('#skF_2'), k1_funct_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_80])).
% 1.81/1.18  tff(c_89, plain, (k1_funct_1(k6_relat_1('#skF_2'), k1_funct_1('#skF_3', '#skF_1'))=k1_funct_1(k8_relat_1('#skF_2', '#skF_3'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2, c_84])).
% 1.81/1.18  tff(c_93, plain, (k1_funct_1(k6_relat_1('#skF_2'), k1_funct_1('#skF_3', '#skF_1'))=k1_funct_1(k8_relat_1('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_89])).
% 1.81/1.18  tff(c_10, plain, (![B_9, A_8]: (k1_funct_1(k6_relat_1(B_9), A_8)=A_8 | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.81/1.18  tff(c_98, plain, (k1_funct_1(k8_relat_1('#skF_2', '#skF_3'), '#skF_1')=k1_funct_1('#skF_3', '#skF_1') | ~r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_93, c_10])).
% 1.81/1.18  tff(c_105, plain, (k1_funct_1(k8_relat_1('#skF_2', '#skF_3'), '#skF_1')=k1_funct_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_98])).
% 1.81/1.18  tff(c_107, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_105])).
% 1.81/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.18  
% 1.81/1.18  Inference rules
% 1.81/1.18  ----------------------
% 1.81/1.18  #Ref     : 0
% 1.81/1.18  #Sup     : 18
% 1.81/1.18  #Fact    : 0
% 1.81/1.18  #Define  : 0
% 1.81/1.18  #Split   : 0
% 1.81/1.18  #Chain   : 0
% 1.81/1.18  #Close   : 0
% 1.81/1.18  
% 1.81/1.18  Ordering : KBO
% 1.81/1.18  
% 1.81/1.18  Simplification rules
% 1.81/1.18  ----------------------
% 1.81/1.18  #Subsume      : 0
% 1.81/1.18  #Demod        : 11
% 1.81/1.18  #Tautology    : 9
% 1.81/1.18  #SimpNegUnit  : 1
% 1.81/1.18  #BackRed      : 1
% 1.81/1.18  
% 1.81/1.18  #Partial instantiations: 0
% 1.81/1.18  #Strategies tried      : 1
% 1.81/1.18  
% 1.81/1.18  Timing (in seconds)
% 1.81/1.18  ----------------------
% 1.81/1.18  Preprocessing        : 0.28
% 1.81/1.18  Parsing              : 0.16
% 1.81/1.18  CNF conversion       : 0.02
% 1.81/1.18  Main loop            : 0.13
% 1.81/1.18  Inferencing          : 0.06
% 1.81/1.18  Reduction            : 0.04
% 1.81/1.18  Demodulation         : 0.03
% 1.81/1.18  BG Simplification    : 0.01
% 1.81/1.18  Subsumption          : 0.02
% 1.81/1.18  Abstraction          : 0.01
% 1.81/1.18  MUC search           : 0.00
% 1.81/1.18  Cooper               : 0.00
% 1.81/1.18  Total                : 0.44
% 1.81/1.18  Index Insertion      : 0.00
% 1.81/1.18  Index Deletion       : 0.00
% 1.81/1.18  Index Matching       : 0.00
% 1.81/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
