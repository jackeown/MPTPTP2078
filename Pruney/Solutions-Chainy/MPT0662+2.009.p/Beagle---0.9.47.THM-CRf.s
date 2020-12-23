%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:11 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   44 (  59 expanded)
%              Number of leaves         :   21 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   84 ( 121 expanded)
%              Number of equality atoms :   19 (  26 expanded)
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

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
         => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_funct_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_26,plain,(
    r2_hidden('#skF_2',k1_relat_1(k7_relat_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_68,plain,(
    ! [A_23,B_24,C_25] :
      ( r2_hidden(A_23,B_24)
      | ~ r2_hidden(A_23,k1_relat_1(k7_relat_1(C_25,B_24)))
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_71,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_68])).

tff(c_74,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_71])).

tff(c_28,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_10,plain,(
    ! [A_6] : v1_relat_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_6] : v1_funct_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_11,C_15] :
      ( k1_funct_1(k6_relat_1(A_11),C_15) = C_15
      | ~ r2_hidden(C_15,A_11)
      | ~ v1_funct_1(k6_relat_1(A_11))
      | ~ v1_relat_1(k6_relat_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_34,plain,(
    ! [A_11,C_15] :
      ( k1_funct_1(k6_relat_1(A_11),C_15) = C_15
      | ~ r2_hidden(C_15,A_11)
      | ~ v1_relat_1(k6_relat_1(A_11)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_20])).

tff(c_36,plain,(
    ! [A_11,C_15] :
      ( k1_funct_1(k6_relat_1(A_11),C_15) = C_15
      | ~ r2_hidden(C_15,A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_34])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( k5_relat_1(k6_relat_1(A_4),B_5) = k7_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    ! [A_11] :
      ( k1_relat_1(k6_relat_1(A_11)) = A_11
      | ~ v1_funct_1(k6_relat_1(A_11))
      | ~ v1_relat_1(k6_relat_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_32,plain,(
    ! [A_11] :
      ( k1_relat_1(k6_relat_1(A_11)) = A_11
      | ~ v1_relat_1(k6_relat_1(A_11)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_22])).

tff(c_38,plain,(
    ! [A_11] : k1_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_32])).

tff(c_125,plain,(
    ! [B_34,C_35,A_36] :
      ( k1_funct_1(k5_relat_1(B_34,C_35),A_36) = k1_funct_1(C_35,k1_funct_1(B_34,A_36))
      | ~ r2_hidden(A_36,k1_relat_1(B_34))
      | ~ v1_funct_1(C_35)
      | ~ v1_relat_1(C_35)
      | ~ v1_funct_1(B_34)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_135,plain,(
    ! [A_11,C_35,A_36] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_11),C_35),A_36) = k1_funct_1(C_35,k1_funct_1(k6_relat_1(A_11),A_36))
      | ~ r2_hidden(A_36,A_11)
      | ~ v1_funct_1(C_35)
      | ~ v1_relat_1(C_35)
      | ~ v1_funct_1(k6_relat_1(A_11))
      | ~ v1_relat_1(k6_relat_1(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_125])).

tff(c_153,plain,(
    ! [A_38,C_39,A_40] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_38),C_39),A_40) = k1_funct_1(C_39,k1_funct_1(k6_relat_1(A_38),A_40))
      | ~ r2_hidden(A_40,A_38)
      | ~ v1_funct_1(C_39)
      | ~ v1_relat_1(C_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12,c_135])).

tff(c_170,plain,(
    ! [B_41,A_42,A_43] :
      ( k1_funct_1(B_41,k1_funct_1(k6_relat_1(A_42),A_43)) = k1_funct_1(k7_relat_1(B_41,A_42),A_43)
      | ~ r2_hidden(A_43,A_42)
      | ~ v1_funct_1(B_41)
      | ~ v1_relat_1(B_41)
      | ~ v1_relat_1(B_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_153])).

tff(c_265,plain,(
    ! [B_52,A_53,C_54] :
      ( k1_funct_1(k7_relat_1(B_52,A_53),C_54) = k1_funct_1(B_52,C_54)
      | ~ r2_hidden(C_54,A_53)
      | ~ v1_funct_1(B_52)
      | ~ v1_relat_1(B_52)
      | ~ v1_relat_1(B_52)
      | ~ r2_hidden(C_54,A_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_170])).

tff(c_24,plain,(
    k1_funct_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2') != k1_funct_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_283,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ r2_hidden('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_24])).

tff(c_300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_30,c_28,c_283])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:24:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.28  
% 2.09/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.28  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.09/1.28  
% 2.09/1.28  %Foreground sorts:
% 2.09/1.28  
% 2.09/1.28  
% 2.09/1.28  %Background operators:
% 2.09/1.28  
% 2.09/1.28  
% 2.09/1.28  %Foreground operators:
% 2.09/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.09/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.28  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.09/1.28  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.09/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.28  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.09/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.09/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.09/1.28  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.09/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.09/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.09/1.28  
% 2.09/1.29  tff(f_76, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_funct_1)).
% 2.09/1.29  tff(f_33, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 2.09/1.29  tff(f_41, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.09/1.29  tff(f_67, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 2.09/1.29  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.09/1.29  tff(f_54, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 2.09/1.29  tff(c_30, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.09/1.29  tff(c_26, plain, (r2_hidden('#skF_2', k1_relat_1(k7_relat_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.09/1.29  tff(c_68, plain, (![A_23, B_24, C_25]: (r2_hidden(A_23, B_24) | ~r2_hidden(A_23, k1_relat_1(k7_relat_1(C_25, B_24))) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.09/1.29  tff(c_71, plain, (r2_hidden('#skF_2', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_68])).
% 2.09/1.29  tff(c_74, plain, (r2_hidden('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_71])).
% 2.09/1.29  tff(c_28, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.09/1.29  tff(c_10, plain, (![A_6]: (v1_relat_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.09/1.29  tff(c_12, plain, (![A_6]: (v1_funct_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.09/1.29  tff(c_20, plain, (![A_11, C_15]: (k1_funct_1(k6_relat_1(A_11), C_15)=C_15 | ~r2_hidden(C_15, A_11) | ~v1_funct_1(k6_relat_1(A_11)) | ~v1_relat_1(k6_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.09/1.29  tff(c_34, plain, (![A_11, C_15]: (k1_funct_1(k6_relat_1(A_11), C_15)=C_15 | ~r2_hidden(C_15, A_11) | ~v1_relat_1(k6_relat_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_20])).
% 2.09/1.29  tff(c_36, plain, (![A_11, C_15]: (k1_funct_1(k6_relat_1(A_11), C_15)=C_15 | ~r2_hidden(C_15, A_11))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_34])).
% 2.09/1.29  tff(c_8, plain, (![A_4, B_5]: (k5_relat_1(k6_relat_1(A_4), B_5)=k7_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.09/1.29  tff(c_22, plain, (![A_11]: (k1_relat_1(k6_relat_1(A_11))=A_11 | ~v1_funct_1(k6_relat_1(A_11)) | ~v1_relat_1(k6_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.09/1.29  tff(c_32, plain, (![A_11]: (k1_relat_1(k6_relat_1(A_11))=A_11 | ~v1_relat_1(k6_relat_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_22])).
% 2.09/1.29  tff(c_38, plain, (![A_11]: (k1_relat_1(k6_relat_1(A_11))=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_32])).
% 2.09/1.29  tff(c_125, plain, (![B_34, C_35, A_36]: (k1_funct_1(k5_relat_1(B_34, C_35), A_36)=k1_funct_1(C_35, k1_funct_1(B_34, A_36)) | ~r2_hidden(A_36, k1_relat_1(B_34)) | ~v1_funct_1(C_35) | ~v1_relat_1(C_35) | ~v1_funct_1(B_34) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.09/1.29  tff(c_135, plain, (![A_11, C_35, A_36]: (k1_funct_1(k5_relat_1(k6_relat_1(A_11), C_35), A_36)=k1_funct_1(C_35, k1_funct_1(k6_relat_1(A_11), A_36)) | ~r2_hidden(A_36, A_11) | ~v1_funct_1(C_35) | ~v1_relat_1(C_35) | ~v1_funct_1(k6_relat_1(A_11)) | ~v1_relat_1(k6_relat_1(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_125])).
% 2.09/1.29  tff(c_153, plain, (![A_38, C_39, A_40]: (k1_funct_1(k5_relat_1(k6_relat_1(A_38), C_39), A_40)=k1_funct_1(C_39, k1_funct_1(k6_relat_1(A_38), A_40)) | ~r2_hidden(A_40, A_38) | ~v1_funct_1(C_39) | ~v1_relat_1(C_39))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12, c_135])).
% 2.09/1.29  tff(c_170, plain, (![B_41, A_42, A_43]: (k1_funct_1(B_41, k1_funct_1(k6_relat_1(A_42), A_43))=k1_funct_1(k7_relat_1(B_41, A_42), A_43) | ~r2_hidden(A_43, A_42) | ~v1_funct_1(B_41) | ~v1_relat_1(B_41) | ~v1_relat_1(B_41))), inference(superposition, [status(thm), theory('equality')], [c_8, c_153])).
% 2.09/1.29  tff(c_265, plain, (![B_52, A_53, C_54]: (k1_funct_1(k7_relat_1(B_52, A_53), C_54)=k1_funct_1(B_52, C_54) | ~r2_hidden(C_54, A_53) | ~v1_funct_1(B_52) | ~v1_relat_1(B_52) | ~v1_relat_1(B_52) | ~r2_hidden(C_54, A_53))), inference(superposition, [status(thm), theory('equality')], [c_36, c_170])).
% 2.09/1.29  tff(c_24, plain, (k1_funct_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2')!=k1_funct_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.09/1.29  tff(c_283, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~r2_hidden('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_265, c_24])).
% 2.09/1.29  tff(c_300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_30, c_28, c_283])).
% 2.09/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.29  
% 2.09/1.29  Inference rules
% 2.09/1.29  ----------------------
% 2.09/1.29  #Ref     : 0
% 2.09/1.29  #Sup     : 55
% 2.09/1.29  #Fact    : 0
% 2.09/1.29  #Define  : 0
% 2.09/1.29  #Split   : 1
% 2.09/1.29  #Chain   : 0
% 2.09/1.29  #Close   : 0
% 2.09/1.29  
% 2.09/1.29  Ordering : KBO
% 2.09/1.29  
% 2.09/1.29  Simplification rules
% 2.09/1.29  ----------------------
% 2.09/1.29  #Subsume      : 1
% 2.09/1.29  #Demod        : 47
% 2.09/1.29  #Tautology    : 21
% 2.09/1.29  #SimpNegUnit  : 0
% 2.09/1.29  #BackRed      : 0
% 2.09/1.29  
% 2.09/1.29  #Partial instantiations: 0
% 2.09/1.29  #Strategies tried      : 1
% 2.09/1.29  
% 2.09/1.29  Timing (in seconds)
% 2.09/1.29  ----------------------
% 2.09/1.29  Preprocessing        : 0.29
% 2.09/1.29  Parsing              : 0.16
% 2.09/1.29  CNF conversion       : 0.02
% 2.09/1.29  Main loop            : 0.24
% 2.09/1.29  Inferencing          : 0.09
% 2.09/1.29  Reduction            : 0.07
% 2.09/1.29  Demodulation         : 0.05
% 2.09/1.29  BG Simplification    : 0.02
% 2.09/1.29  Subsumption          : 0.04
% 2.09/1.29  Abstraction          : 0.01
% 2.09/1.29  MUC search           : 0.00
% 2.09/1.29  Cooper               : 0.00
% 2.09/1.29  Total                : 0.55
% 2.09/1.29  Index Insertion      : 0.00
% 2.09/1.29  Index Deletion       : 0.00
% 2.09/1.29  Index Matching       : 0.00
% 2.09/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
