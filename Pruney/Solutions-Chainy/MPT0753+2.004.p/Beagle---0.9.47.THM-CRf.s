%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:29 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   50 (  75 expanded)
%              Number of leaves         :   25 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :   64 ( 148 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > v5_ordinal1 > v3_ordinal1 > v1_relat_1 > v1_funct_1 > k7_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v3_ordinal1(k1_relat_1(A))
         => ( v1_relat_1(A)
            & v5_relat_1(A,k2_relat_1(A))
            & v1_funct_1(A)
            & v5_ordinal1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_ordinal1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v5_ordinal1(A)
    <=> v3_ordinal1(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_ordinal1)).

tff(c_40,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_18,plain,(
    ! [A_8] : v1_relat_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,(
    ! [A_8] : v1_funct_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_28,plain,(
    ! [A_9] :
      ( k1_relat_1(k6_relat_1(A_9)) = A_9
      | ~ v1_funct_1(k6_relat_1(A_9))
      | ~ v1_relat_1(k6_relat_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_44,plain,(
    ! [A_9] :
      ( k1_relat_1(k6_relat_1(A_9)) = A_9
      | ~ v1_relat_1(k6_relat_1(A_9)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_28])).

tff(c_48,plain,(
    ! [A_9] : k1_relat_1(k6_relat_1(A_9)) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_44])).

tff(c_89,plain,(
    ! [A_24] :
      ( k7_relat_1(A_24,k1_relat_1(A_24)) = A_24
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_98,plain,(
    ! [A_9] :
      ( k7_relat_1(k6_relat_1(A_9),A_9) = k6_relat_1(A_9)
      | ~ v1_relat_1(k6_relat_1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_89])).

tff(c_102,plain,(
    ! [A_9] : k7_relat_1(k6_relat_1(A_9),A_9) = k6_relat_1(A_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_98])).

tff(c_112,plain,(
    ! [B_26,A_27] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_26,A_27)),A_27)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_115,plain,(
    ! [A_9] :
      ( r1_tarski(k1_relat_1(k6_relat_1(A_9)),A_9)
      | ~ v1_relat_1(k6_relat_1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_112])).

tff(c_120,plain,(
    ! [A_9] : r1_tarski(A_9,A_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_48,c_115])).

tff(c_122,plain,(
    ! [B_29,A_30] :
      ( v5_relat_1(B_29,A_30)
      | ~ r1_tarski(k2_relat_1(B_29),A_30)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_128,plain,(
    ! [B_31] :
      ( v5_relat_1(B_31,k2_relat_1(B_31))
      | ~ v1_relat_1(B_31) ) ),
    inference(resolution,[status(thm)],[c_120,c_122])).

tff(c_38,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_34,plain,
    ( ~ v5_ordinal1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v5_relat_1('#skF_2',k2_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_42,plain,
    ( ~ v5_ordinal1('#skF_2')
    | ~ v5_relat_1('#skF_2',k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_34])).

tff(c_70,plain,(
    ~ v5_relat_1('#skF_2',k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_131,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_128,c_70])).

tff(c_135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_131])).

tff(c_136,plain,(
    ~ v5_ordinal1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_36,plain,(
    v3_ordinal1(k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_138,plain,(
    ! [A_32] :
      ( v5_ordinal1(A_32)
      | ~ v3_ordinal1(k1_relat_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_147,plain,(
    v5_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_138])).

tff(c_152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_147])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:53:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.20  
% 1.89/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.21  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > v5_ordinal1 > v3_ordinal1 > v1_relat_1 > v1_funct_1 > k7_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.89/1.21  
% 1.89/1.21  %Foreground sorts:
% 1.89/1.21  
% 1.89/1.21  
% 1.89/1.21  %Background operators:
% 1.89/1.21  
% 1.89/1.21  
% 1.89/1.21  %Foreground operators:
% 1.89/1.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.89/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.89/1.21  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.89/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.89/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.89/1.21  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 1.89/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.89/1.21  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 1.89/1.21  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.89/1.21  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.89/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.89/1.21  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.89/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.21  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.89/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.89/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.89/1.21  
% 1.96/1.22  tff(f_83, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v3_ordinal1(k1_relat_1(A)) => (((v1_relat_1(A) & v5_relat_1(A, k2_relat_1(A))) & v1_funct_1(A)) & v5_ordinal1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_ordinal1)).
% 1.96/1.22  tff(f_51, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.96/1.22  tff(f_64, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 1.96/1.22  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 1.96/1.22  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 1.96/1.22  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 1.96/1.22  tff(f_68, axiom, (![A]: (v5_ordinal1(A) <=> v3_ordinal1(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_ordinal1)).
% 1.96/1.22  tff(c_40, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.96/1.22  tff(c_18, plain, (![A_8]: (v1_relat_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.96/1.22  tff(c_20, plain, (![A_8]: (v1_funct_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.96/1.22  tff(c_28, plain, (![A_9]: (k1_relat_1(k6_relat_1(A_9))=A_9 | ~v1_funct_1(k6_relat_1(A_9)) | ~v1_relat_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.96/1.22  tff(c_44, plain, (![A_9]: (k1_relat_1(k6_relat_1(A_9))=A_9 | ~v1_relat_1(k6_relat_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_28])).
% 1.96/1.22  tff(c_48, plain, (![A_9]: (k1_relat_1(k6_relat_1(A_9))=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_44])).
% 1.96/1.22  tff(c_89, plain, (![A_24]: (k7_relat_1(A_24, k1_relat_1(A_24))=A_24 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.96/1.22  tff(c_98, plain, (![A_9]: (k7_relat_1(k6_relat_1(A_9), A_9)=k6_relat_1(A_9) | ~v1_relat_1(k6_relat_1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_89])).
% 1.96/1.22  tff(c_102, plain, (![A_9]: (k7_relat_1(k6_relat_1(A_9), A_9)=k6_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_98])).
% 1.96/1.22  tff(c_112, plain, (![B_26, A_27]: (r1_tarski(k1_relat_1(k7_relat_1(B_26, A_27)), A_27) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.96/1.22  tff(c_115, plain, (![A_9]: (r1_tarski(k1_relat_1(k6_relat_1(A_9)), A_9) | ~v1_relat_1(k6_relat_1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_102, c_112])).
% 1.96/1.22  tff(c_120, plain, (![A_9]: (r1_tarski(A_9, A_9))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_48, c_115])).
% 1.96/1.22  tff(c_122, plain, (![B_29, A_30]: (v5_relat_1(B_29, A_30) | ~r1_tarski(k2_relat_1(B_29), A_30) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.96/1.22  tff(c_128, plain, (![B_31]: (v5_relat_1(B_31, k2_relat_1(B_31)) | ~v1_relat_1(B_31))), inference(resolution, [status(thm)], [c_120, c_122])).
% 1.96/1.22  tff(c_38, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.96/1.22  tff(c_34, plain, (~v5_ordinal1('#skF_2') | ~v1_funct_1('#skF_2') | ~v5_relat_1('#skF_2', k2_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.96/1.22  tff(c_42, plain, (~v5_ordinal1('#skF_2') | ~v5_relat_1('#skF_2', k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_34])).
% 1.96/1.22  tff(c_70, plain, (~v5_relat_1('#skF_2', k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_42])).
% 1.96/1.22  tff(c_131, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_128, c_70])).
% 1.96/1.22  tff(c_135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_131])).
% 1.96/1.22  tff(c_136, plain, (~v5_ordinal1('#skF_2')), inference(splitRight, [status(thm)], [c_42])).
% 1.96/1.22  tff(c_36, plain, (v3_ordinal1(k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.96/1.22  tff(c_138, plain, (![A_32]: (v5_ordinal1(A_32) | ~v3_ordinal1(k1_relat_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.96/1.22  tff(c_147, plain, (v5_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_36, c_138])).
% 1.96/1.22  tff(c_152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_136, c_147])).
% 1.96/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.22  
% 1.96/1.22  Inference rules
% 1.96/1.22  ----------------------
% 1.96/1.22  #Ref     : 0
% 1.96/1.22  #Sup     : 19
% 1.96/1.22  #Fact    : 0
% 1.96/1.22  #Define  : 0
% 1.96/1.22  #Split   : 1
% 1.96/1.22  #Chain   : 0
% 1.96/1.22  #Close   : 0
% 1.96/1.22  
% 1.96/1.22  Ordering : KBO
% 1.96/1.22  
% 1.96/1.22  Simplification rules
% 1.96/1.22  ----------------------
% 1.96/1.22  #Subsume      : 0
% 1.96/1.22  #Demod        : 12
% 1.96/1.22  #Tautology    : 11
% 1.96/1.22  #SimpNegUnit  : 1
% 1.96/1.22  #BackRed      : 0
% 1.96/1.22  
% 1.96/1.22  #Partial instantiations: 0
% 1.96/1.22  #Strategies tried      : 1
% 1.96/1.22  
% 1.96/1.22  Timing (in seconds)
% 1.96/1.22  ----------------------
% 1.96/1.22  Preprocessing        : 0.27
% 1.96/1.22  Parsing              : 0.15
% 1.96/1.22  CNF conversion       : 0.02
% 1.96/1.22  Main loop            : 0.13
% 1.96/1.22  Inferencing          : 0.05
% 1.96/1.22  Reduction            : 0.04
% 1.96/1.22  Demodulation         : 0.03
% 1.96/1.22  BG Simplification    : 0.01
% 1.96/1.22  Subsumption          : 0.02
% 1.96/1.22  Abstraction          : 0.01
% 1.96/1.22  MUC search           : 0.00
% 1.96/1.22  Cooper               : 0.00
% 1.96/1.22  Total                : 0.43
% 1.96/1.22  Index Insertion      : 0.00
% 1.96/1.22  Index Deletion       : 0.00
% 1.96/1.22  Index Matching       : 0.00
% 1.96/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
