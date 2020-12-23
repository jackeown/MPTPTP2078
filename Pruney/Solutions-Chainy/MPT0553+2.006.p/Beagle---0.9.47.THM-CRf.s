%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:02 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   43 (  80 expanded)
%              Number of leaves         :   21 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :   69 ( 158 expanded)
%              Number of equality atoms :    6 (  20 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k6_subset_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_57,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k6_subset_1(k9_relat_1(C,A),k9_relat_1(C,B)),k9_relat_1(C,k6_subset_1(A,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_relat_1)).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k6_subset_1(k2_relat_1(A),k2_relat_1(B)),k2_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relat_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28,plain,(
    ! [A_19,B_20] :
      ( k5_relat_1(k6_relat_1(A_19),B_20) = k7_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k5_relat_1(A_1,B_2))
      | ~ v1_relat_1(B_2)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    ! [B_20,A_19] :
      ( v1_relat_1(k7_relat_1(B_20,A_19))
      | ~ v1_relat_1(B_20)
      | ~ v1_relat_1(k6_relat_1(A_19))
      | ~ v1_relat_1(B_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2])).

tff(c_40,plain,(
    ! [B_20,A_19] :
      ( v1_relat_1(k7_relat_1(B_20,A_19))
      | ~ v1_relat_1(B_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_34])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( k2_relat_1(k7_relat_1(B_8,A_7)) = k9_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [C_6,A_4,B_5] :
      ( k6_subset_1(k7_relat_1(C_6,A_4),k7_relat_1(C_6,B_5)) = k7_relat_1(C_6,k6_subset_1(A_4,B_5))
      | ~ v1_relat_1(C_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_43,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(k6_subset_1(k2_relat_1(A_23),k2_relat_1(B_24)),k2_relat_1(k6_subset_1(A_23,B_24)))
      | ~ v1_relat_1(B_24)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_62,plain,(
    ! [A_28,B_29,A_30] :
      ( r1_tarski(k6_subset_1(k2_relat_1(A_28),k9_relat_1(B_29,A_30)),k2_relat_1(k6_subset_1(A_28,k7_relat_1(B_29,A_30))))
      | ~ v1_relat_1(k7_relat_1(B_29,A_30))
      | ~ v1_relat_1(A_28)
      | ~ v1_relat_1(B_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_43])).

tff(c_111,plain,(
    ! [C_43,A_44,B_45] :
      ( r1_tarski(k6_subset_1(k2_relat_1(k7_relat_1(C_43,A_44)),k9_relat_1(C_43,B_45)),k2_relat_1(k7_relat_1(C_43,k6_subset_1(A_44,B_45))))
      | ~ v1_relat_1(k7_relat_1(C_43,B_45))
      | ~ v1_relat_1(k7_relat_1(C_43,A_44))
      | ~ v1_relat_1(C_43)
      | ~ v1_relat_1(C_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_62])).

tff(c_126,plain,(
    ! [B_50,A_51,B_52] :
      ( r1_tarski(k6_subset_1(k9_relat_1(B_50,A_51),k9_relat_1(B_50,B_52)),k2_relat_1(k7_relat_1(B_50,k6_subset_1(A_51,B_52))))
      | ~ v1_relat_1(k7_relat_1(B_50,B_52))
      | ~ v1_relat_1(k7_relat_1(B_50,A_51))
      | ~ v1_relat_1(B_50)
      | ~ v1_relat_1(B_50)
      | ~ v1_relat_1(B_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_111])).

tff(c_164,plain,(
    ! [B_63,A_64,B_65] :
      ( r1_tarski(k6_subset_1(k9_relat_1(B_63,A_64),k9_relat_1(B_63,B_65)),k9_relat_1(B_63,k6_subset_1(A_64,B_65)))
      | ~ v1_relat_1(k7_relat_1(B_63,B_65))
      | ~ v1_relat_1(k7_relat_1(B_63,A_64))
      | ~ v1_relat_1(B_63)
      | ~ v1_relat_1(B_63)
      | ~ v1_relat_1(B_63)
      | ~ v1_relat_1(B_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_126])).

tff(c_14,plain,(
    ~ r1_tarski(k6_subset_1(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')),k9_relat_1('#skF_3',k6_subset_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_167,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_164,c_14])).

tff(c_173,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_167])).

tff(c_174,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_173])).

tff(c_177,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_174])).

tff(c_181,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_177])).

tff(c_182,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_173])).

tff(c_186,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_182])).

tff(c_190,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_186])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:52:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.30  
% 2.19/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.31  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k6_subset_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.19/1.31  
% 2.19/1.31  %Foreground sorts:
% 2.19/1.31  
% 2.19/1.31  
% 2.19/1.31  %Background operators:
% 2.19/1.31  
% 2.19/1.31  
% 2.19/1.31  %Foreground operators:
% 2.19/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.31  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.19/1.31  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.19/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.19/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.19/1.31  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.19/1.31  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.19/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.19/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.19/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.19/1.31  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.19/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.31  
% 2.19/1.32  tff(f_57, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k6_subset_1(k9_relat_1(C, A), k9_relat_1(C, B)), k9_relat_1(C, k6_subset_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_relat_1)).
% 2.19/1.32  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.19/1.32  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.19/1.32  tff(f_31, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.19/1.32  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.19/1.32  tff(f_37, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_relat_1)).
% 2.19/1.32  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k2_relat_1(A), k2_relat_1(B)), k2_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_relat_1)).
% 2.19/1.32  tff(c_16, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.19/1.32  tff(c_4, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.19/1.32  tff(c_28, plain, (![A_19, B_20]: (k5_relat_1(k6_relat_1(A_19), B_20)=k7_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.19/1.32  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k5_relat_1(A_1, B_2)) | ~v1_relat_1(B_2) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.19/1.32  tff(c_34, plain, (![B_20, A_19]: (v1_relat_1(k7_relat_1(B_20, A_19)) | ~v1_relat_1(B_20) | ~v1_relat_1(k6_relat_1(A_19)) | ~v1_relat_1(B_20))), inference(superposition, [status(thm), theory('equality')], [c_28, c_2])).
% 2.19/1.32  tff(c_40, plain, (![B_20, A_19]: (v1_relat_1(k7_relat_1(B_20, A_19)) | ~v1_relat_1(B_20))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_34])).
% 2.19/1.32  tff(c_8, plain, (![B_8, A_7]: (k2_relat_1(k7_relat_1(B_8, A_7))=k9_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.19/1.32  tff(c_6, plain, (![C_6, A_4, B_5]: (k6_subset_1(k7_relat_1(C_6, A_4), k7_relat_1(C_6, B_5))=k7_relat_1(C_6, k6_subset_1(A_4, B_5)) | ~v1_relat_1(C_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.19/1.32  tff(c_43, plain, (![A_23, B_24]: (r1_tarski(k6_subset_1(k2_relat_1(A_23), k2_relat_1(B_24)), k2_relat_1(k6_subset_1(A_23, B_24))) | ~v1_relat_1(B_24) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.19/1.32  tff(c_62, plain, (![A_28, B_29, A_30]: (r1_tarski(k6_subset_1(k2_relat_1(A_28), k9_relat_1(B_29, A_30)), k2_relat_1(k6_subset_1(A_28, k7_relat_1(B_29, A_30)))) | ~v1_relat_1(k7_relat_1(B_29, A_30)) | ~v1_relat_1(A_28) | ~v1_relat_1(B_29))), inference(superposition, [status(thm), theory('equality')], [c_8, c_43])).
% 2.19/1.32  tff(c_111, plain, (![C_43, A_44, B_45]: (r1_tarski(k6_subset_1(k2_relat_1(k7_relat_1(C_43, A_44)), k9_relat_1(C_43, B_45)), k2_relat_1(k7_relat_1(C_43, k6_subset_1(A_44, B_45)))) | ~v1_relat_1(k7_relat_1(C_43, B_45)) | ~v1_relat_1(k7_relat_1(C_43, A_44)) | ~v1_relat_1(C_43) | ~v1_relat_1(C_43))), inference(superposition, [status(thm), theory('equality')], [c_6, c_62])).
% 2.19/1.32  tff(c_126, plain, (![B_50, A_51, B_52]: (r1_tarski(k6_subset_1(k9_relat_1(B_50, A_51), k9_relat_1(B_50, B_52)), k2_relat_1(k7_relat_1(B_50, k6_subset_1(A_51, B_52)))) | ~v1_relat_1(k7_relat_1(B_50, B_52)) | ~v1_relat_1(k7_relat_1(B_50, A_51)) | ~v1_relat_1(B_50) | ~v1_relat_1(B_50) | ~v1_relat_1(B_50))), inference(superposition, [status(thm), theory('equality')], [c_8, c_111])).
% 2.19/1.32  tff(c_164, plain, (![B_63, A_64, B_65]: (r1_tarski(k6_subset_1(k9_relat_1(B_63, A_64), k9_relat_1(B_63, B_65)), k9_relat_1(B_63, k6_subset_1(A_64, B_65))) | ~v1_relat_1(k7_relat_1(B_63, B_65)) | ~v1_relat_1(k7_relat_1(B_63, A_64)) | ~v1_relat_1(B_63) | ~v1_relat_1(B_63) | ~v1_relat_1(B_63) | ~v1_relat_1(B_63))), inference(superposition, [status(thm), theory('equality')], [c_8, c_126])).
% 2.19/1.32  tff(c_14, plain, (~r1_tarski(k6_subset_1(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2')), k9_relat_1('#skF_3', k6_subset_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.19/1.32  tff(c_167, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_164, c_14])).
% 2.19/1.32  tff(c_173, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_167])).
% 2.19/1.32  tff(c_174, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_173])).
% 2.19/1.32  tff(c_177, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_174])).
% 2.19/1.32  tff(c_181, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_177])).
% 2.19/1.32  tff(c_182, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_173])).
% 2.19/1.32  tff(c_186, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_182])).
% 2.19/1.32  tff(c_190, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_186])).
% 2.19/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.32  
% 2.19/1.32  Inference rules
% 2.19/1.32  ----------------------
% 2.19/1.32  #Ref     : 0
% 2.19/1.32  #Sup     : 42
% 2.19/1.32  #Fact    : 0
% 2.19/1.32  #Define  : 0
% 2.19/1.32  #Split   : 1
% 2.19/1.32  #Chain   : 0
% 2.19/1.32  #Close   : 0
% 2.19/1.32  
% 2.19/1.32  Ordering : KBO
% 2.19/1.32  
% 2.19/1.32  Simplification rules
% 2.19/1.32  ----------------------
% 2.19/1.32  #Subsume      : 7
% 2.19/1.32  #Demod        : 4
% 2.19/1.32  #Tautology    : 6
% 2.19/1.32  #SimpNegUnit  : 0
% 2.19/1.32  #BackRed      : 0
% 2.19/1.32  
% 2.19/1.32  #Partial instantiations: 0
% 2.19/1.32  #Strategies tried      : 1
% 2.19/1.32  
% 2.19/1.32  Timing (in seconds)
% 2.19/1.32  ----------------------
% 2.19/1.32  Preprocessing        : 0.26
% 2.19/1.32  Parsing              : 0.15
% 2.19/1.32  CNF conversion       : 0.02
% 2.19/1.32  Main loop            : 0.24
% 2.19/1.32  Inferencing          : 0.10
% 2.19/1.32  Reduction            : 0.06
% 2.19/1.32  Demodulation         : 0.05
% 2.19/1.32  BG Simplification    : 0.01
% 2.19/1.32  Subsumption          : 0.05
% 2.19/1.32  Abstraction          : 0.01
% 2.19/1.32  MUC search           : 0.00
% 2.19/1.32  Cooper               : 0.00
% 2.19/1.32  Total                : 0.53
% 2.19/1.32  Index Insertion      : 0.00
% 2.19/1.32  Index Deletion       : 0.00
% 2.19/1.32  Index Matching       : 0.00
% 2.19/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
