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
% DateTime   : Thu Dec  3 10:05:36 EST 2020

% Result     : Theorem 16.80s
% Output     : CNFRefutation 16.80s
% Verified   : 
% Statistics : Number of formulae       :   43 (  77 expanded)
%              Number of leaves         :   21 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :   72 ( 177 expanded)
%              Number of equality atoms :   19 (  44 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] : k5_relat_1(k7_relat_1(A,C),k7_relat_1(B,k9_relat_1(A,C))) = k7_relat_1(k5_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_funct_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4,plain,(
    ! [B_4,C_6,A_3] :
      ( k7_relat_1(k5_relat_1(B_4,C_6),A_3) = k5_relat_1(k7_relat_1(B_4,A_3),C_6)
      | ~ v1_relat_1(C_6)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k7_relat_1(A_1,B_2))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [B_8,A_7] :
      ( k2_relat_1(k7_relat_1(B_8,A_7)) = k9_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_12,plain,(
    ! [A_17,B_18] :
      ( k5_relat_1(k6_relat_1(A_17),B_18) = k7_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_14,plain,(
    ! [A_19] : v1_relat_1(k6_relat_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_10,plain,(
    ! [A_16] :
      ( k5_relat_1(A_16,k6_relat_1(k2_relat_1(A_16))) = A_16
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_126,plain,(
    ! [A_38,B_39,C_40] :
      ( k5_relat_1(k5_relat_1(A_38,B_39),C_40) = k5_relat_1(A_38,k5_relat_1(B_39,C_40))
      | ~ v1_relat_1(C_40)
      | ~ v1_relat_1(B_39)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_151,plain,(
    ! [A_16,C_40] :
      ( k5_relat_1(A_16,k5_relat_1(k6_relat_1(k2_relat_1(A_16)),C_40)) = k5_relat_1(A_16,C_40)
      | ~ v1_relat_1(C_40)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(A_16)))
      | ~ v1_relat_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_126])).

tff(c_356,plain,(
    ! [A_57,C_58] :
      ( k5_relat_1(A_57,k5_relat_1(k6_relat_1(k2_relat_1(A_57)),C_58)) = k5_relat_1(A_57,C_58)
      | ~ v1_relat_1(C_58)
      | ~ v1_relat_1(A_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_151])).

tff(c_900,plain,(
    ! [A_76,B_77] :
      ( k5_relat_1(A_76,k7_relat_1(B_77,k2_relat_1(A_76))) = k5_relat_1(A_76,B_77)
      | ~ v1_relat_1(B_77)
      | ~ v1_relat_1(A_76)
      | ~ v1_relat_1(B_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_356])).

tff(c_37435,plain,(
    ! [B_524,A_525,B_526] :
      ( k5_relat_1(k7_relat_1(B_524,A_525),k7_relat_1(B_526,k9_relat_1(B_524,A_525))) = k5_relat_1(k7_relat_1(B_524,A_525),B_526)
      | ~ v1_relat_1(B_526)
      | ~ v1_relat_1(k7_relat_1(B_524,A_525))
      | ~ v1_relat_1(B_526)
      | ~ v1_relat_1(B_524) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_900])).

tff(c_18,plain,(
    k5_relat_1(k7_relat_1('#skF_1','#skF_3'),k7_relat_1('#skF_2',k9_relat_1('#skF_1','#skF_3'))) != k7_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_37555,plain,
    ( k7_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_3') != k5_relat_1(k7_relat_1('#skF_1','#skF_3'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_3'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_37435,c_18])).

tff(c_37940,plain,
    ( k7_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_3') != k5_relat_1(k7_relat_1('#skF_1','#skF_3'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_22,c_37555])).

tff(c_38103,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_37940])).

tff(c_38106,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_38103])).

tff(c_38110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_38106])).

tff(c_38111,plain,(
    k7_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_3') != k5_relat_1(k7_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_37940])).

tff(c_38115,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_38111])).

tff(c_38119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_38115])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:02:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.80/7.99  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.80/7.99  
% 16.80/7.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.80/7.99  %$ v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 16.80/7.99  
% 16.80/7.99  %Foreground sorts:
% 16.80/7.99  
% 16.80/7.99  
% 16.80/7.99  %Background operators:
% 16.80/7.99  
% 16.80/7.99  
% 16.80/7.99  %Foreground operators:
% 16.80/7.99  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 16.80/7.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.80/7.99  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 16.80/7.99  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 16.80/7.99  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 16.80/7.99  tff('#skF_2', type, '#skF_2': $i).
% 16.80/7.99  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 16.80/7.99  tff('#skF_3', type, '#skF_3': $i).
% 16.80/7.99  tff('#skF_1', type, '#skF_1': $i).
% 16.80/7.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.80/7.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 16.80/7.99  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 16.80/7.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.80/7.99  
% 16.80/8.00  tff(f_75, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: (k5_relat_1(k7_relat_1(A, C), k7_relat_1(B, k9_relat_1(A, C))) = k7_relat_1(k5_relat_1(A, B), C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_funct_1)).
% 16.80/8.00  tff(f_36, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_relat_1)).
% 16.80/8.00  tff(f_29, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 16.80/8.00  tff(f_40, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 16.80/8.00  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 16.80/8.00  tff(f_62, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 16.80/8.00  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 16.80/8.00  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 16.80/8.00  tff(c_26, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 16.80/8.00  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 16.80/8.00  tff(c_4, plain, (![B_4, C_6, A_3]: (k7_relat_1(k5_relat_1(B_4, C_6), A_3)=k5_relat_1(k7_relat_1(B_4, A_3), C_6) | ~v1_relat_1(C_6) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 16.80/8.00  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k7_relat_1(A_1, B_2)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 16.80/8.00  tff(c_6, plain, (![B_8, A_7]: (k2_relat_1(k7_relat_1(B_8, A_7))=k9_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 16.80/8.00  tff(c_12, plain, (![A_17, B_18]: (k5_relat_1(k6_relat_1(A_17), B_18)=k7_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_58])).
% 16.80/8.00  tff(c_14, plain, (![A_19]: (v1_relat_1(k6_relat_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 16.80/8.00  tff(c_10, plain, (![A_16]: (k5_relat_1(A_16, k6_relat_1(k2_relat_1(A_16)))=A_16 | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 16.80/8.00  tff(c_126, plain, (![A_38, B_39, C_40]: (k5_relat_1(k5_relat_1(A_38, B_39), C_40)=k5_relat_1(A_38, k5_relat_1(B_39, C_40)) | ~v1_relat_1(C_40) | ~v1_relat_1(B_39) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_50])).
% 16.80/8.00  tff(c_151, plain, (![A_16, C_40]: (k5_relat_1(A_16, k5_relat_1(k6_relat_1(k2_relat_1(A_16)), C_40))=k5_relat_1(A_16, C_40) | ~v1_relat_1(C_40) | ~v1_relat_1(k6_relat_1(k2_relat_1(A_16))) | ~v1_relat_1(A_16) | ~v1_relat_1(A_16))), inference(superposition, [status(thm), theory('equality')], [c_10, c_126])).
% 16.80/8.00  tff(c_356, plain, (![A_57, C_58]: (k5_relat_1(A_57, k5_relat_1(k6_relat_1(k2_relat_1(A_57)), C_58))=k5_relat_1(A_57, C_58) | ~v1_relat_1(C_58) | ~v1_relat_1(A_57))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_151])).
% 16.80/8.00  tff(c_900, plain, (![A_76, B_77]: (k5_relat_1(A_76, k7_relat_1(B_77, k2_relat_1(A_76)))=k5_relat_1(A_76, B_77) | ~v1_relat_1(B_77) | ~v1_relat_1(A_76) | ~v1_relat_1(B_77))), inference(superposition, [status(thm), theory('equality')], [c_12, c_356])).
% 16.80/8.00  tff(c_37435, plain, (![B_524, A_525, B_526]: (k5_relat_1(k7_relat_1(B_524, A_525), k7_relat_1(B_526, k9_relat_1(B_524, A_525)))=k5_relat_1(k7_relat_1(B_524, A_525), B_526) | ~v1_relat_1(B_526) | ~v1_relat_1(k7_relat_1(B_524, A_525)) | ~v1_relat_1(B_526) | ~v1_relat_1(B_524))), inference(superposition, [status(thm), theory('equality')], [c_6, c_900])).
% 16.80/8.00  tff(c_18, plain, (k5_relat_1(k7_relat_1('#skF_1', '#skF_3'), k7_relat_1('#skF_2', k9_relat_1('#skF_1', '#skF_3')))!=k7_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 16.80/8.00  tff(c_37555, plain, (k7_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k5_relat_1(k7_relat_1('#skF_1', '#skF_3'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_3')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_37435, c_18])).
% 16.80/8.00  tff(c_37940, plain, (k7_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k5_relat_1(k7_relat_1('#skF_1', '#skF_3'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_22, c_37555])).
% 16.80/8.00  tff(c_38103, plain, (~v1_relat_1(k7_relat_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_37940])).
% 16.80/8.00  tff(c_38106, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_2, c_38103])).
% 16.80/8.00  tff(c_38110, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_38106])).
% 16.80/8.00  tff(c_38111, plain, (k7_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k5_relat_1(k7_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_37940])).
% 16.80/8.00  tff(c_38115, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4, c_38111])).
% 16.80/8.00  tff(c_38119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_38115])).
% 16.80/8.00  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.80/8.00  
% 16.80/8.00  Inference rules
% 16.80/8.00  ----------------------
% 16.80/8.00  #Ref     : 0
% 16.80/8.00  #Sup     : 8020
% 16.80/8.00  #Fact    : 0
% 16.80/8.00  #Define  : 0
% 16.80/8.00  #Split   : 1
% 16.80/8.00  #Chain   : 0
% 16.80/8.00  #Close   : 0
% 16.80/8.00  
% 16.80/8.00  Ordering : KBO
% 16.80/8.00  
% 16.80/8.00  Simplification rules
% 16.80/8.00  ----------------------
% 16.80/8.00  #Subsume      : 395
% 16.80/8.00  #Demod        : 19655
% 16.80/8.00  #Tautology    : 3171
% 16.80/8.00  #SimpNegUnit  : 0
% 16.80/8.00  #BackRed      : 1
% 16.80/8.00  
% 16.80/8.00  #Partial instantiations: 0
% 16.80/8.00  #Strategies tried      : 1
% 16.80/8.00  
% 16.80/8.00  Timing (in seconds)
% 16.80/8.00  ----------------------
% 16.80/8.01  Preprocessing        : 0.27
% 16.80/8.01  Parsing              : 0.14
% 16.80/8.01  CNF conversion       : 0.02
% 16.80/8.01  Main loop            : 6.94
% 16.80/8.01  Inferencing          : 1.46
% 16.80/8.01  Reduction            : 3.81
% 16.80/8.01  Demodulation         : 3.41
% 16.80/8.01  BG Simplification    : 0.22
% 16.80/8.01  Subsumption          : 1.20
% 16.80/8.01  Abstraction          : 0.47
% 16.80/8.01  MUC search           : 0.00
% 16.80/8.01  Cooper               : 0.00
% 16.80/8.01  Total                : 7.24
% 16.80/8.01  Index Insertion      : 0.00
% 16.80/8.01  Index Deletion       : 0.00
% 16.80/8.01  Index Matching       : 0.00
% 16.80/8.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
