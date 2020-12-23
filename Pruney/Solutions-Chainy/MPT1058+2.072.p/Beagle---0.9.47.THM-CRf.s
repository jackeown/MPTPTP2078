%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:31 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :   50 (  68 expanded)
%              Number of leaves         :   24 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :   77 ( 110 expanded)
%              Number of equality atoms :   26 (  36 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > r1_tarski > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_55,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

tff(c_22,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_28,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_24,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_12,plain,(
    ! [A_12] : k1_relat_1(k6_relat_1(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18,plain,(
    ! [A_15] : v1_relat_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_58,plain,(
    ! [B_24,A_25] :
      ( v4_relat_1(B_24,A_25)
      | ~ r1_tarski(k1_relat_1(B_24),A_25)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_61,plain,(
    ! [A_12,A_25] :
      ( v4_relat_1(k6_relat_1(A_12),A_25)
      | ~ r1_tarski(A_12,A_25)
      | ~ v1_relat_1(k6_relat_1(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_58])).

tff(c_63,plain,(
    ! [A_12,A_25] :
      ( v4_relat_1(k6_relat_1(A_12),A_25)
      | ~ r1_tarski(A_12,A_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_61])).

tff(c_65,plain,(
    ! [B_28,A_29] :
      ( k7_relat_1(B_28,A_29) = B_28
      | ~ v4_relat_1(B_28,A_29)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_68,plain,(
    ! [A_12,A_25] :
      ( k7_relat_1(k6_relat_1(A_12),A_25) = k6_relat_1(A_12)
      | ~ v1_relat_1(k6_relat_1(A_12))
      | ~ r1_tarski(A_12,A_25) ) ),
    inference(resolution,[status(thm)],[c_63,c_65])).

tff(c_71,plain,(
    ! [A_12,A_25] :
      ( k7_relat_1(k6_relat_1(A_12),A_25) = k6_relat_1(A_12)
      | ~ r1_tarski(A_12,A_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_68])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( k5_relat_1(k6_relat_1(A_13),B_14) = k7_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_96,plain,(
    ! [A_36,B_37] :
      ( k10_relat_1(A_36,k1_relat_1(B_37)) = k1_relat_1(k5_relat_1(A_36,B_37))
      | ~ v1_relat_1(B_37)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_105,plain,(
    ! [A_36,A_12] :
      ( k1_relat_1(k5_relat_1(A_36,k6_relat_1(A_12))) = k10_relat_1(A_36,A_12)
      | ~ v1_relat_1(k6_relat_1(A_12))
      | ~ v1_relat_1(A_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_96])).

tff(c_110,plain,(
    ! [A_38,A_39] :
      ( k1_relat_1(k5_relat_1(A_38,k6_relat_1(A_39))) = k10_relat_1(A_38,A_39)
      | ~ v1_relat_1(A_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_105])).

tff(c_129,plain,(
    ! [A_39,A_13] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_39),A_13)) = k10_relat_1(k6_relat_1(A_13),A_39)
      | ~ v1_relat_1(k6_relat_1(A_13))
      | ~ v1_relat_1(k6_relat_1(A_39)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_110])).

tff(c_134,plain,(
    ! [A_40,A_41] : k1_relat_1(k7_relat_1(k6_relat_1(A_40),A_41)) = k10_relat_1(k6_relat_1(A_41),A_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_129])).

tff(c_152,plain,(
    ! [A_25,A_12] :
      ( k10_relat_1(k6_relat_1(A_25),A_12) = k1_relat_1(k6_relat_1(A_12))
      | ~ r1_tarski(A_12,A_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_134])).

tff(c_155,plain,(
    ! [A_25,A_12] :
      ( k10_relat_1(k6_relat_1(A_25),A_12) = A_12
      | ~ r1_tarski(A_12,A_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_152])).

tff(c_177,plain,(
    ! [B_44,C_45,A_46] :
      ( k10_relat_1(k5_relat_1(B_44,C_45),A_46) = k10_relat_1(B_44,k10_relat_1(C_45,A_46))
      | ~ v1_relat_1(C_45)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_194,plain,(
    ! [A_13,B_14,A_46] :
      ( k10_relat_1(k6_relat_1(A_13),k10_relat_1(B_14,A_46)) = k10_relat_1(k7_relat_1(B_14,A_13),A_46)
      | ~ v1_relat_1(B_14)
      | ~ v1_relat_1(k6_relat_1(A_13))
      | ~ v1_relat_1(B_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_177])).

tff(c_199,plain,(
    ! [A_47,B_48,A_49] :
      ( k10_relat_1(k6_relat_1(A_47),k10_relat_1(B_48,A_49)) = k10_relat_1(k7_relat_1(B_48,A_47),A_49)
      | ~ v1_relat_1(B_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_194])).

tff(c_455,plain,(
    ! [B_70,A_71,A_72] :
      ( k10_relat_1(k7_relat_1(B_70,A_71),A_72) = k10_relat_1(B_70,A_72)
      | ~ v1_relat_1(B_70)
      | ~ r1_tarski(k10_relat_1(B_70,A_72),A_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_199])).

tff(c_476,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_455])).

tff(c_483,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_476])).

tff(c_485,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_483])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:44:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.39/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.28  
% 2.39/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.28  %$ v4_relat_1 > r1_tarski > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.39/1.28  
% 2.39/1.28  %Foreground sorts:
% 2.39/1.28  
% 2.39/1.28  
% 2.39/1.28  %Background operators:
% 2.39/1.28  
% 2.39/1.28  
% 2.39/1.28  %Foreground operators:
% 2.39/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.39/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.39/1.28  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.39/1.28  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.39/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.39/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.39/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.39/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.39/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.39/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.39/1.28  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.39/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.39/1.28  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.39/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.39/1.28  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.39/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.39/1.28  
% 2.39/1.30  tff(f_73, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 2.39/1.30  tff(f_55, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.39/1.30  tff(f_63, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.39/1.30  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.39/1.30  tff(f_51, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.39/1.30  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.39/1.30  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 2.39/1.30  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t181_relat_1)).
% 2.39/1.30  tff(c_22, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.39/1.30  tff(c_28, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.39/1.30  tff(c_24, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.39/1.30  tff(c_12, plain, (![A_12]: (k1_relat_1(k6_relat_1(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.39/1.30  tff(c_18, plain, (![A_15]: (v1_relat_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.39/1.30  tff(c_58, plain, (![B_24, A_25]: (v4_relat_1(B_24, A_25) | ~r1_tarski(k1_relat_1(B_24), A_25) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.39/1.30  tff(c_61, plain, (![A_12, A_25]: (v4_relat_1(k6_relat_1(A_12), A_25) | ~r1_tarski(A_12, A_25) | ~v1_relat_1(k6_relat_1(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_58])).
% 2.39/1.30  tff(c_63, plain, (![A_12, A_25]: (v4_relat_1(k6_relat_1(A_12), A_25) | ~r1_tarski(A_12, A_25))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_61])).
% 2.39/1.30  tff(c_65, plain, (![B_28, A_29]: (k7_relat_1(B_28, A_29)=B_28 | ~v4_relat_1(B_28, A_29) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.39/1.30  tff(c_68, plain, (![A_12, A_25]: (k7_relat_1(k6_relat_1(A_12), A_25)=k6_relat_1(A_12) | ~v1_relat_1(k6_relat_1(A_12)) | ~r1_tarski(A_12, A_25))), inference(resolution, [status(thm)], [c_63, c_65])).
% 2.39/1.30  tff(c_71, plain, (![A_12, A_25]: (k7_relat_1(k6_relat_1(A_12), A_25)=k6_relat_1(A_12) | ~r1_tarski(A_12, A_25))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_68])).
% 2.39/1.30  tff(c_16, plain, (![A_13, B_14]: (k5_relat_1(k6_relat_1(A_13), B_14)=k7_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.39/1.30  tff(c_96, plain, (![A_36, B_37]: (k10_relat_1(A_36, k1_relat_1(B_37))=k1_relat_1(k5_relat_1(A_36, B_37)) | ~v1_relat_1(B_37) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.39/1.30  tff(c_105, plain, (![A_36, A_12]: (k1_relat_1(k5_relat_1(A_36, k6_relat_1(A_12)))=k10_relat_1(A_36, A_12) | ~v1_relat_1(k6_relat_1(A_12)) | ~v1_relat_1(A_36))), inference(superposition, [status(thm), theory('equality')], [c_12, c_96])).
% 2.39/1.30  tff(c_110, plain, (![A_38, A_39]: (k1_relat_1(k5_relat_1(A_38, k6_relat_1(A_39)))=k10_relat_1(A_38, A_39) | ~v1_relat_1(A_38))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_105])).
% 2.39/1.30  tff(c_129, plain, (![A_39, A_13]: (k1_relat_1(k7_relat_1(k6_relat_1(A_39), A_13))=k10_relat_1(k6_relat_1(A_13), A_39) | ~v1_relat_1(k6_relat_1(A_13)) | ~v1_relat_1(k6_relat_1(A_39)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_110])).
% 2.39/1.30  tff(c_134, plain, (![A_40, A_41]: (k1_relat_1(k7_relat_1(k6_relat_1(A_40), A_41))=k10_relat_1(k6_relat_1(A_41), A_40))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_129])).
% 2.39/1.30  tff(c_152, plain, (![A_25, A_12]: (k10_relat_1(k6_relat_1(A_25), A_12)=k1_relat_1(k6_relat_1(A_12)) | ~r1_tarski(A_12, A_25))), inference(superposition, [status(thm), theory('equality')], [c_71, c_134])).
% 2.39/1.30  tff(c_155, plain, (![A_25, A_12]: (k10_relat_1(k6_relat_1(A_25), A_12)=A_12 | ~r1_tarski(A_12, A_25))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_152])).
% 2.39/1.30  tff(c_177, plain, (![B_44, C_45, A_46]: (k10_relat_1(k5_relat_1(B_44, C_45), A_46)=k10_relat_1(B_44, k10_relat_1(C_45, A_46)) | ~v1_relat_1(C_45) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.39/1.30  tff(c_194, plain, (![A_13, B_14, A_46]: (k10_relat_1(k6_relat_1(A_13), k10_relat_1(B_14, A_46))=k10_relat_1(k7_relat_1(B_14, A_13), A_46) | ~v1_relat_1(B_14) | ~v1_relat_1(k6_relat_1(A_13)) | ~v1_relat_1(B_14))), inference(superposition, [status(thm), theory('equality')], [c_16, c_177])).
% 2.39/1.30  tff(c_199, plain, (![A_47, B_48, A_49]: (k10_relat_1(k6_relat_1(A_47), k10_relat_1(B_48, A_49))=k10_relat_1(k7_relat_1(B_48, A_47), A_49) | ~v1_relat_1(B_48))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_194])).
% 2.39/1.30  tff(c_455, plain, (![B_70, A_71, A_72]: (k10_relat_1(k7_relat_1(B_70, A_71), A_72)=k10_relat_1(B_70, A_72) | ~v1_relat_1(B_70) | ~r1_tarski(k10_relat_1(B_70, A_72), A_71))), inference(superposition, [status(thm), theory('equality')], [c_155, c_199])).
% 2.39/1.30  tff(c_476, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_24, c_455])).
% 2.39/1.30  tff(c_483, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_476])).
% 2.39/1.30  tff(c_485, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_483])).
% 2.39/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.30  
% 2.39/1.30  Inference rules
% 2.39/1.30  ----------------------
% 2.39/1.30  #Ref     : 0
% 2.39/1.30  #Sup     : 106
% 2.39/1.30  #Fact    : 0
% 2.39/1.30  #Define  : 0
% 2.39/1.30  #Split   : 0
% 2.39/1.30  #Chain   : 0
% 2.39/1.30  #Close   : 0
% 2.39/1.30  
% 2.39/1.30  Ordering : KBO
% 2.39/1.30  
% 2.39/1.30  Simplification rules
% 2.39/1.30  ----------------------
% 2.39/1.30  #Subsume      : 6
% 2.39/1.30  #Demod        : 42
% 2.39/1.30  #Tautology    : 31
% 2.39/1.30  #SimpNegUnit  : 1
% 2.39/1.30  #BackRed      : 0
% 2.39/1.30  
% 2.39/1.30  #Partial instantiations: 0
% 2.39/1.30  #Strategies tried      : 1
% 2.39/1.30  
% 2.39/1.30  Timing (in seconds)
% 2.39/1.30  ----------------------
% 2.39/1.30  Preprocessing        : 0.29
% 2.39/1.30  Parsing              : 0.15
% 2.39/1.30  CNF conversion       : 0.02
% 2.39/1.30  Main loop            : 0.27
% 2.39/1.30  Inferencing          : 0.11
% 2.39/1.30  Reduction            : 0.08
% 2.39/1.30  Demodulation         : 0.06
% 2.39/1.30  BG Simplification    : 0.02
% 2.39/1.30  Subsumption          : 0.04
% 2.39/1.30  Abstraction          : 0.02
% 2.39/1.30  MUC search           : 0.00
% 2.39/1.30  Cooper               : 0.00
% 2.39/1.30  Total                : 0.59
% 2.39/1.30  Index Insertion      : 0.00
% 2.39/1.30  Index Deletion       : 0.00
% 2.39/1.30  Index Matching       : 0.00
% 2.39/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
