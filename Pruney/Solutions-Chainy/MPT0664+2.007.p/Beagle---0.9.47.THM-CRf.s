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
% DateTime   : Thu Dec  3 10:04:14 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   40 (  53 expanded)
%              Number of leaves         :   20 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :   74 ( 106 expanded)
%              Number of equality atoms :   19 (  25 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,B)
         => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

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

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

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

tff(c_20,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_22,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_3] : v1_funct_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_8,C_12] :
      ( k1_funct_1(k6_relat_1(A_8),C_12) = C_12
      | ~ r2_hidden(C_12,A_8)
      | ~ v1_funct_1(k6_relat_1(A_8))
      | ~ v1_relat_1(k6_relat_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_28,plain,(
    ! [A_8,C_12] :
      ( k1_funct_1(k6_relat_1(A_8),C_12) = C_12
      | ~ r2_hidden(C_12,A_8)
      | ~ v1_relat_1(k6_relat_1(A_8)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14])).

tff(c_30,plain,(
    ! [A_8,C_12] :
      ( k1_funct_1(k6_relat_1(A_8),C_12) = C_12
      | ~ r2_hidden(C_12,A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_28])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k5_relat_1(k6_relat_1(A_1),B_2) = k7_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [A_8] :
      ( k1_relat_1(k6_relat_1(A_8)) = A_8
      | ~ v1_funct_1(k6_relat_1(A_8))
      | ~ v1_relat_1(k6_relat_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_26,plain,(
    ! [A_8] :
      ( k1_relat_1(k6_relat_1(A_8)) = A_8
      | ~ v1_relat_1(k6_relat_1(A_8)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_16])).

tff(c_32,plain,(
    ! [A_8] : k1_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_26])).

tff(c_86,plain,(
    ! [B_22,C_23,A_24] :
      ( k1_funct_1(k5_relat_1(B_22,C_23),A_24) = k1_funct_1(C_23,k1_funct_1(B_22,A_24))
      | ~ r2_hidden(A_24,k1_relat_1(B_22))
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23)
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_90,plain,(
    ! [A_8,C_23,A_24] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_8),C_23),A_24) = k1_funct_1(C_23,k1_funct_1(k6_relat_1(A_8),A_24))
      | ~ r2_hidden(A_24,A_8)
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23)
      | ~ v1_funct_1(k6_relat_1(A_8))
      | ~ v1_relat_1(k6_relat_1(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_86])).

tff(c_94,plain,(
    ! [A_25,C_26,A_27] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_25),C_26),A_27) = k1_funct_1(C_26,k1_funct_1(k6_relat_1(A_25),A_27))
      | ~ r2_hidden(A_27,A_25)
      | ~ v1_funct_1(C_26)
      | ~ v1_relat_1(C_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6,c_90])).

tff(c_110,plain,(
    ! [B_28,A_29,A_30] :
      ( k1_funct_1(B_28,k1_funct_1(k6_relat_1(A_29),A_30)) = k1_funct_1(k7_relat_1(B_28,A_29),A_30)
      | ~ r2_hidden(A_30,A_29)
      | ~ v1_funct_1(B_28)
      | ~ v1_relat_1(B_28)
      | ~ v1_relat_1(B_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_94])).

tff(c_216,plain,(
    ! [B_39,A_40,C_41] :
      ( k1_funct_1(k7_relat_1(B_39,A_40),C_41) = k1_funct_1(B_39,C_41)
      | ~ r2_hidden(C_41,A_40)
      | ~ v1_funct_1(B_39)
      | ~ v1_relat_1(B_39)
      | ~ v1_relat_1(B_39)
      | ~ r2_hidden(C_41,A_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_110])).

tff(c_18,plain,(
    k1_funct_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2') != k1_funct_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_234,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ r2_hidden('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_18])).

tff(c_251,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_24,c_22,c_234])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:41:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.25  
% 2.11/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.25  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.11/1.25  
% 2.11/1.25  %Foreground sorts:
% 2.11/1.25  
% 2.11/1.25  
% 2.11/1.25  %Background operators:
% 2.11/1.25  
% 2.11/1.25  
% 2.11/1.25  %Foreground operators:
% 2.11/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.11/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.25  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.11/1.25  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.11/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.11/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.11/1.25  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.11/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.11/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.11/1.25  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.11/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.11/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.11/1.25  
% 2.11/1.26  tff(f_68, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, B) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_funct_1)).
% 2.11/1.26  tff(f_33, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.11/1.26  tff(f_59, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 2.11/1.26  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.11/1.26  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 2.11/1.26  tff(c_20, plain, (r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.11/1.26  tff(c_24, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.11/1.26  tff(c_22, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.11/1.26  tff(c_4, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.11/1.26  tff(c_6, plain, (![A_3]: (v1_funct_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.11/1.26  tff(c_14, plain, (![A_8, C_12]: (k1_funct_1(k6_relat_1(A_8), C_12)=C_12 | ~r2_hidden(C_12, A_8) | ~v1_funct_1(k6_relat_1(A_8)) | ~v1_relat_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.11/1.26  tff(c_28, plain, (![A_8, C_12]: (k1_funct_1(k6_relat_1(A_8), C_12)=C_12 | ~r2_hidden(C_12, A_8) | ~v1_relat_1(k6_relat_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_14])).
% 2.11/1.26  tff(c_30, plain, (![A_8, C_12]: (k1_funct_1(k6_relat_1(A_8), C_12)=C_12 | ~r2_hidden(C_12, A_8))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_28])).
% 2.11/1.26  tff(c_2, plain, (![A_1, B_2]: (k5_relat_1(k6_relat_1(A_1), B_2)=k7_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.11/1.26  tff(c_16, plain, (![A_8]: (k1_relat_1(k6_relat_1(A_8))=A_8 | ~v1_funct_1(k6_relat_1(A_8)) | ~v1_relat_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.11/1.26  tff(c_26, plain, (![A_8]: (k1_relat_1(k6_relat_1(A_8))=A_8 | ~v1_relat_1(k6_relat_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_16])).
% 2.11/1.26  tff(c_32, plain, (![A_8]: (k1_relat_1(k6_relat_1(A_8))=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_26])).
% 2.11/1.26  tff(c_86, plain, (![B_22, C_23, A_24]: (k1_funct_1(k5_relat_1(B_22, C_23), A_24)=k1_funct_1(C_23, k1_funct_1(B_22, A_24)) | ~r2_hidden(A_24, k1_relat_1(B_22)) | ~v1_funct_1(C_23) | ~v1_relat_1(C_23) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.11/1.26  tff(c_90, plain, (![A_8, C_23, A_24]: (k1_funct_1(k5_relat_1(k6_relat_1(A_8), C_23), A_24)=k1_funct_1(C_23, k1_funct_1(k6_relat_1(A_8), A_24)) | ~r2_hidden(A_24, A_8) | ~v1_funct_1(C_23) | ~v1_relat_1(C_23) | ~v1_funct_1(k6_relat_1(A_8)) | ~v1_relat_1(k6_relat_1(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_86])).
% 2.11/1.26  tff(c_94, plain, (![A_25, C_26, A_27]: (k1_funct_1(k5_relat_1(k6_relat_1(A_25), C_26), A_27)=k1_funct_1(C_26, k1_funct_1(k6_relat_1(A_25), A_27)) | ~r2_hidden(A_27, A_25) | ~v1_funct_1(C_26) | ~v1_relat_1(C_26))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6, c_90])).
% 2.11/1.26  tff(c_110, plain, (![B_28, A_29, A_30]: (k1_funct_1(B_28, k1_funct_1(k6_relat_1(A_29), A_30))=k1_funct_1(k7_relat_1(B_28, A_29), A_30) | ~r2_hidden(A_30, A_29) | ~v1_funct_1(B_28) | ~v1_relat_1(B_28) | ~v1_relat_1(B_28))), inference(superposition, [status(thm), theory('equality')], [c_2, c_94])).
% 2.11/1.26  tff(c_216, plain, (![B_39, A_40, C_41]: (k1_funct_1(k7_relat_1(B_39, A_40), C_41)=k1_funct_1(B_39, C_41) | ~r2_hidden(C_41, A_40) | ~v1_funct_1(B_39) | ~v1_relat_1(B_39) | ~v1_relat_1(B_39) | ~r2_hidden(C_41, A_40))), inference(superposition, [status(thm), theory('equality')], [c_30, c_110])).
% 2.11/1.26  tff(c_18, plain, (k1_funct_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2')!=k1_funct_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.11/1.26  tff(c_234, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~r2_hidden('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_216, c_18])).
% 2.11/1.26  tff(c_251, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_24, c_22, c_234])).
% 2.11/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.26  
% 2.11/1.26  Inference rules
% 2.11/1.26  ----------------------
% 2.11/1.26  #Ref     : 0
% 2.11/1.26  #Sup     : 46
% 2.11/1.26  #Fact    : 0
% 2.11/1.26  #Define  : 0
% 2.11/1.26  #Split   : 0
% 2.11/1.26  #Chain   : 0
% 2.11/1.26  #Close   : 0
% 2.11/1.26  
% 2.11/1.26  Ordering : KBO
% 2.11/1.26  
% 2.11/1.26  Simplification rules
% 2.11/1.26  ----------------------
% 2.11/1.26  #Subsume      : 1
% 2.11/1.26  #Demod        : 64
% 2.11/1.26  #Tautology    : 23
% 2.11/1.26  #SimpNegUnit  : 0
% 2.11/1.26  #BackRed      : 0
% 2.11/1.26  
% 2.11/1.26  #Partial instantiations: 0
% 2.11/1.26  #Strategies tried      : 1
% 2.11/1.26  
% 2.11/1.26  Timing (in seconds)
% 2.11/1.26  ----------------------
% 2.11/1.27  Preprocessing        : 0.27
% 2.11/1.27  Parsing              : 0.15
% 2.11/1.27  CNF conversion       : 0.02
% 2.11/1.27  Main loop            : 0.21
% 2.11/1.27  Inferencing          : 0.09
% 2.11/1.27  Reduction            : 0.06
% 2.11/1.27  Demodulation         : 0.05
% 2.11/1.27  BG Simplification    : 0.02
% 2.11/1.27  Subsumption          : 0.03
% 2.11/1.27  Abstraction          : 0.02
% 2.11/1.27  MUC search           : 0.00
% 2.11/1.27  Cooper               : 0.00
% 2.11/1.27  Total                : 0.50
% 2.11/1.27  Index Insertion      : 0.00
% 2.11/1.27  Index Deletion       : 0.00
% 2.11/1.27  Index Matching       : 0.00
% 2.11/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
