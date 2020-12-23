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
% DateTime   : Thu Dec  3 10:04:11 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   41 (  47 expanded)
%              Number of leaves         :   22 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   70 (  89 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
         => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_funct_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k1_funct_1(k6_relat_1(B),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_24,plain,(
    r2_hidden('#skF_1',k1_relat_1(k7_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_67,plain,(
    ! [A_22,B_23,C_24] :
      ( r2_hidden(A_22,B_23)
      | ~ r2_hidden(A_22,k1_relat_1(k7_relat_1(C_24,B_23)))
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_70,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_67])).

tff(c_73,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_70])).

tff(c_26,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,(
    ! [B_13,A_12] :
      ( k1_funct_1(k6_relat_1(B_13),A_12) = A_12
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( k5_relat_1(k6_relat_1(A_5),B_6) = k7_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_7] : v1_relat_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ! [A_7] : v1_funct_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [A_1] : k1_relat_1(k6_relat_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_90,plain,(
    ! [B_31,C_32,A_33] :
      ( k1_funct_1(k5_relat_1(B_31,C_32),A_33) = k1_funct_1(C_32,k1_funct_1(B_31,A_33))
      | ~ r2_hidden(A_33,k1_relat_1(B_31))
      | ~ v1_funct_1(C_32)
      | ~ v1_relat_1(C_32)
      | ~ v1_funct_1(B_31)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_98,plain,(
    ! [A_1,C_32,A_33] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_1),C_32),A_33) = k1_funct_1(C_32,k1_funct_1(k6_relat_1(A_1),A_33))
      | ~ r2_hidden(A_33,A_1)
      | ~ v1_funct_1(C_32)
      | ~ v1_relat_1(C_32)
      | ~ v1_funct_1(k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_90])).

tff(c_115,plain,(
    ! [A_35,C_36,A_37] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_35),C_36),A_37) = k1_funct_1(C_36,k1_funct_1(k6_relat_1(A_35),A_37))
      | ~ r2_hidden(A_37,A_35)
      | ~ v1_funct_1(C_36)
      | ~ v1_relat_1(C_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16,c_98])).

tff(c_127,plain,(
    ! [B_38,A_39,A_40] :
      ( k1_funct_1(B_38,k1_funct_1(k6_relat_1(A_39),A_40)) = k1_funct_1(k7_relat_1(B_38,A_39),A_40)
      | ~ r2_hidden(A_40,A_39)
      | ~ v1_funct_1(B_38)
      | ~ v1_relat_1(B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_115])).

tff(c_204,plain,(
    ! [B_47,B_48,A_49] :
      ( k1_funct_1(k7_relat_1(B_47,B_48),A_49) = k1_funct_1(B_47,A_49)
      | ~ r2_hidden(A_49,B_48)
      | ~ v1_funct_1(B_47)
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(B_47)
      | ~ r2_hidden(A_49,B_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_127])).

tff(c_22,plain,(
    k1_funct_1(k7_relat_1('#skF_3','#skF_2'),'#skF_1') != k1_funct_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_218,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_22])).

tff(c_235,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_28,c_26,c_218])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:38:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.24  
% 2.13/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.24  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.13/1.24  
% 2.13/1.24  %Foreground sorts:
% 2.13/1.24  
% 2.13/1.24  
% 2.13/1.24  %Background operators:
% 2.13/1.24  
% 2.13/1.24  
% 2.13/1.24  %Foreground operators:
% 2.13/1.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.13/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.24  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.13/1.24  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.13/1.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.13/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.13/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.13/1.24  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.13/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.13/1.24  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.13/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.13/1.24  
% 2.13/1.25  tff(f_71, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_funct_1)).
% 2.13/1.25  tff(f_37, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 2.13/1.25  tff(f_62, axiom, (![A, B]: (r2_hidden(A, B) => (k1_funct_1(k6_relat_1(B), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_1)).
% 2.13/1.25  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.13/1.25  tff(f_45, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.13/1.25  tff(f_29, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.13/1.25  tff(f_58, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 2.13/1.25  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.13/1.25  tff(c_24, plain, (r2_hidden('#skF_1', k1_relat_1(k7_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.13/1.25  tff(c_67, plain, (![A_22, B_23, C_24]: (r2_hidden(A_22, B_23) | ~r2_hidden(A_22, k1_relat_1(k7_relat_1(C_24, B_23))) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.13/1.25  tff(c_70, plain, (r2_hidden('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_67])).
% 2.13/1.25  tff(c_73, plain, (r2_hidden('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_70])).
% 2.13/1.25  tff(c_26, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.13/1.25  tff(c_20, plain, (![B_13, A_12]: (k1_funct_1(k6_relat_1(B_13), A_12)=A_12 | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.13/1.25  tff(c_12, plain, (![A_5, B_6]: (k5_relat_1(k6_relat_1(A_5), B_6)=k7_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.13/1.25  tff(c_14, plain, (![A_7]: (v1_relat_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.13/1.25  tff(c_16, plain, (![A_7]: (v1_funct_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.13/1.25  tff(c_2, plain, (![A_1]: (k1_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.13/1.25  tff(c_90, plain, (![B_31, C_32, A_33]: (k1_funct_1(k5_relat_1(B_31, C_32), A_33)=k1_funct_1(C_32, k1_funct_1(B_31, A_33)) | ~r2_hidden(A_33, k1_relat_1(B_31)) | ~v1_funct_1(C_32) | ~v1_relat_1(C_32) | ~v1_funct_1(B_31) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.13/1.25  tff(c_98, plain, (![A_1, C_32, A_33]: (k1_funct_1(k5_relat_1(k6_relat_1(A_1), C_32), A_33)=k1_funct_1(C_32, k1_funct_1(k6_relat_1(A_1), A_33)) | ~r2_hidden(A_33, A_1) | ~v1_funct_1(C_32) | ~v1_relat_1(C_32) | ~v1_funct_1(k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_90])).
% 2.13/1.25  tff(c_115, plain, (![A_35, C_36, A_37]: (k1_funct_1(k5_relat_1(k6_relat_1(A_35), C_36), A_37)=k1_funct_1(C_36, k1_funct_1(k6_relat_1(A_35), A_37)) | ~r2_hidden(A_37, A_35) | ~v1_funct_1(C_36) | ~v1_relat_1(C_36))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16, c_98])).
% 2.13/1.25  tff(c_127, plain, (![B_38, A_39, A_40]: (k1_funct_1(B_38, k1_funct_1(k6_relat_1(A_39), A_40))=k1_funct_1(k7_relat_1(B_38, A_39), A_40) | ~r2_hidden(A_40, A_39) | ~v1_funct_1(B_38) | ~v1_relat_1(B_38) | ~v1_relat_1(B_38))), inference(superposition, [status(thm), theory('equality')], [c_12, c_115])).
% 2.13/1.25  tff(c_204, plain, (![B_47, B_48, A_49]: (k1_funct_1(k7_relat_1(B_47, B_48), A_49)=k1_funct_1(B_47, A_49) | ~r2_hidden(A_49, B_48) | ~v1_funct_1(B_47) | ~v1_relat_1(B_47) | ~v1_relat_1(B_47) | ~r2_hidden(A_49, B_48))), inference(superposition, [status(thm), theory('equality')], [c_20, c_127])).
% 2.13/1.25  tff(c_22, plain, (k1_funct_1(k7_relat_1('#skF_3', '#skF_2'), '#skF_1')!=k1_funct_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.13/1.25  tff(c_218, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_204, c_22])).
% 2.13/1.25  tff(c_235, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_28, c_26, c_218])).
% 2.13/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.25  
% 2.13/1.25  Inference rules
% 2.13/1.25  ----------------------
% 2.13/1.25  #Ref     : 0
% 2.13/1.25  #Sup     : 44
% 2.13/1.25  #Fact    : 0
% 2.13/1.25  #Define  : 0
% 2.13/1.25  #Split   : 1
% 2.13/1.25  #Chain   : 0
% 2.13/1.25  #Close   : 0
% 2.13/1.25  
% 2.13/1.25  Ordering : KBO
% 2.13/1.25  
% 2.13/1.25  Simplification rules
% 2.13/1.25  ----------------------
% 2.13/1.25  #Subsume      : 1
% 2.13/1.25  #Demod        : 27
% 2.13/1.25  #Tautology    : 19
% 2.13/1.25  #SimpNegUnit  : 0
% 2.13/1.25  #BackRed      : 0
% 2.13/1.25  
% 2.13/1.25  #Partial instantiations: 0
% 2.13/1.25  #Strategies tried      : 1
% 2.13/1.25  
% 2.13/1.25  Timing (in seconds)
% 2.13/1.25  ----------------------
% 2.13/1.25  Preprocessing        : 0.29
% 2.13/1.26  Parsing              : 0.16
% 2.13/1.26  CNF conversion       : 0.02
% 2.13/1.26  Main loop            : 0.21
% 2.13/1.26  Inferencing          : 0.09
% 2.13/1.26  Reduction            : 0.06
% 2.13/1.26  Demodulation         : 0.04
% 2.13/1.26  BG Simplification    : 0.01
% 2.13/1.26  Subsumption          : 0.04
% 2.13/1.26  Abstraction          : 0.01
% 2.13/1.26  MUC search           : 0.00
% 2.13/1.26  Cooper               : 0.00
% 2.13/1.26  Total                : 0.52
% 2.13/1.26  Index Insertion      : 0.00
% 2.13/1.26  Index Deletion       : 0.00
% 2.13/1.26  Index Matching       : 0.00
% 2.13/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
