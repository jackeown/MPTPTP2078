%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:36 EST 2020

% Result     : Theorem 19.24s
% Output     : CNFRefutation 19.36s
% Verified   : 
% Statistics : Number of formulae       :   44 (  79 expanded)
%              Number of leaves         :   21 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :   77 ( 187 expanded)
%              Number of equality atoms :   19 (  45 expanded)
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

tff(f_79,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] : k5_relat_1(k7_relat_1(A,C),k7_relat_1(B,k9_relat_1(A,C))) = k7_relat_1(k5_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_24,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2,plain,(
    ! [B_2,C_4,A_1] :
      ( k7_relat_1(k5_relat_1(B_2,C_4),A_1) = k5_relat_1(k7_relat_1(B_2,A_1),C_4)
      | ~ v1_relat_1(C_4)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_18,plain,(
    ! [A_18,B_19] :
      ( v1_relat_1(k7_relat_1(A_18,B_19))
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_10,plain,(
    ! [A_15,B_16] :
      ( k5_relat_1(k6_relat_1(A_15),B_16) = k7_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4,plain,(
    ! [B_6,A_5] :
      ( k2_relat_1(k7_relat_1(B_6,A_5)) = k9_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_12,plain,(
    ! [A_17] : v1_relat_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [A_14] :
      ( k5_relat_1(A_14,k6_relat_1(k2_relat_1(A_14))) = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_216,plain,(
    ! [A_44,B_45,C_46] :
      ( k5_relat_1(k5_relat_1(A_44,B_45),C_46) = k5_relat_1(A_44,k5_relat_1(B_45,C_46))
      | ~ v1_relat_1(C_46)
      | ~ v1_relat_1(B_45)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_247,plain,(
    ! [A_14,C_46] :
      ( k5_relat_1(A_14,k5_relat_1(k6_relat_1(k2_relat_1(A_14)),C_46)) = k5_relat_1(A_14,C_46)
      | ~ v1_relat_1(C_46)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(A_14)))
      | ~ v1_relat_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_216])).

tff(c_396,plain,(
    ! [A_54,C_55] :
      ( k5_relat_1(A_54,k5_relat_1(k6_relat_1(k2_relat_1(A_54)),C_55)) = k5_relat_1(A_54,C_55)
      | ~ v1_relat_1(C_55)
      | ~ v1_relat_1(A_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_247])).

tff(c_26289,plain,(
    ! [B_401,A_402,C_403] :
      ( k5_relat_1(k7_relat_1(B_401,A_402),k5_relat_1(k6_relat_1(k9_relat_1(B_401,A_402)),C_403)) = k5_relat_1(k7_relat_1(B_401,A_402),C_403)
      | ~ v1_relat_1(C_403)
      | ~ v1_relat_1(k7_relat_1(B_401,A_402))
      | ~ v1_relat_1(B_401) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_396])).

tff(c_46965,plain,(
    ! [B_514,A_515,B_516] :
      ( k5_relat_1(k7_relat_1(B_514,A_515),k7_relat_1(B_516,k9_relat_1(B_514,A_515))) = k5_relat_1(k7_relat_1(B_514,A_515),B_516)
      | ~ v1_relat_1(B_516)
      | ~ v1_relat_1(k7_relat_1(B_514,A_515))
      | ~ v1_relat_1(B_514)
      | ~ v1_relat_1(B_516) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_26289])).

tff(c_20,plain,(
    k5_relat_1(k7_relat_1('#skF_1','#skF_3'),k7_relat_1('#skF_2',k9_relat_1('#skF_1','#skF_3'))) != k7_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_47076,plain,
    ( k7_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_3') != k5_relat_1(k7_relat_1('#skF_1','#skF_3'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_3'))
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_46965,c_20])).

tff(c_47596,plain,
    ( k7_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_3') != k5_relat_1(k7_relat_1('#skF_1','#skF_3'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28,c_24,c_47076])).

tff(c_47815,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_47596])).

tff(c_47818,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_47815])).

tff(c_47822,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_47818])).

tff(c_47823,plain,(
    k7_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_3') != k5_relat_1(k7_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_47596])).

tff(c_47827,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_47823])).

tff(c_47831,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_47827])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:39:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.24/10.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.31/10.42  
% 19.31/10.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.31/10.43  %$ v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 19.31/10.43  
% 19.31/10.43  %Foreground sorts:
% 19.31/10.43  
% 19.31/10.43  
% 19.31/10.43  %Background operators:
% 19.31/10.43  
% 19.31/10.43  
% 19.31/10.43  %Foreground operators:
% 19.31/10.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 19.31/10.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.31/10.43  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 19.31/10.43  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 19.31/10.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 19.31/10.43  tff('#skF_2', type, '#skF_2': $i).
% 19.31/10.43  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 19.31/10.43  tff('#skF_3', type, '#skF_3': $i).
% 19.31/10.43  tff('#skF_1', type, '#skF_1': $i).
% 19.31/10.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.31/10.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 19.31/10.43  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 19.31/10.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.31/10.43  
% 19.36/10.44  tff(f_79, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: (k5_relat_1(k7_relat_1(A, C), k7_relat_1(B, k9_relat_1(A, C))) = k7_relat_1(k5_relat_1(A, B), C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_funct_1)).
% 19.36/10.44  tff(f_32, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_relat_1)).
% 19.36/10.44  tff(f_66, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 19.36/10.44  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 19.36/10.44  tff(f_36, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 19.36/10.44  tff(f_58, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 19.36/10.44  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 19.36/10.44  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 19.36/10.44  tff(c_28, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_79])).
% 19.36/10.44  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 19.36/10.44  tff(c_2, plain, (![B_2, C_4, A_1]: (k7_relat_1(k5_relat_1(B_2, C_4), A_1)=k5_relat_1(k7_relat_1(B_2, A_1), C_4) | ~v1_relat_1(C_4) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 19.36/10.44  tff(c_26, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_79])).
% 19.36/10.44  tff(c_18, plain, (![A_18, B_19]: (v1_relat_1(k7_relat_1(A_18, B_19)) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_66])).
% 19.36/10.44  tff(c_10, plain, (![A_15, B_16]: (k5_relat_1(k6_relat_1(A_15), B_16)=k7_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 19.36/10.44  tff(c_4, plain, (![B_6, A_5]: (k2_relat_1(k7_relat_1(B_6, A_5))=k9_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 19.36/10.44  tff(c_12, plain, (![A_17]: (v1_relat_1(k6_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 19.36/10.44  tff(c_8, plain, (![A_14]: (k5_relat_1(A_14, k6_relat_1(k2_relat_1(A_14)))=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 19.36/10.44  tff(c_216, plain, (![A_44, B_45, C_46]: (k5_relat_1(k5_relat_1(A_44, B_45), C_46)=k5_relat_1(A_44, k5_relat_1(B_45, C_46)) | ~v1_relat_1(C_46) | ~v1_relat_1(B_45) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_46])).
% 19.36/10.44  tff(c_247, plain, (![A_14, C_46]: (k5_relat_1(A_14, k5_relat_1(k6_relat_1(k2_relat_1(A_14)), C_46))=k5_relat_1(A_14, C_46) | ~v1_relat_1(C_46) | ~v1_relat_1(k6_relat_1(k2_relat_1(A_14))) | ~v1_relat_1(A_14) | ~v1_relat_1(A_14))), inference(superposition, [status(thm), theory('equality')], [c_8, c_216])).
% 19.36/10.44  tff(c_396, plain, (![A_54, C_55]: (k5_relat_1(A_54, k5_relat_1(k6_relat_1(k2_relat_1(A_54)), C_55))=k5_relat_1(A_54, C_55) | ~v1_relat_1(C_55) | ~v1_relat_1(A_54))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_247])).
% 19.36/10.44  tff(c_26289, plain, (![B_401, A_402, C_403]: (k5_relat_1(k7_relat_1(B_401, A_402), k5_relat_1(k6_relat_1(k9_relat_1(B_401, A_402)), C_403))=k5_relat_1(k7_relat_1(B_401, A_402), C_403) | ~v1_relat_1(C_403) | ~v1_relat_1(k7_relat_1(B_401, A_402)) | ~v1_relat_1(B_401))), inference(superposition, [status(thm), theory('equality')], [c_4, c_396])).
% 19.36/10.44  tff(c_46965, plain, (![B_514, A_515, B_516]: (k5_relat_1(k7_relat_1(B_514, A_515), k7_relat_1(B_516, k9_relat_1(B_514, A_515)))=k5_relat_1(k7_relat_1(B_514, A_515), B_516) | ~v1_relat_1(B_516) | ~v1_relat_1(k7_relat_1(B_514, A_515)) | ~v1_relat_1(B_514) | ~v1_relat_1(B_516))), inference(superposition, [status(thm), theory('equality')], [c_10, c_26289])).
% 19.36/10.44  tff(c_20, plain, (k5_relat_1(k7_relat_1('#skF_1', '#skF_3'), k7_relat_1('#skF_2', k9_relat_1('#skF_1', '#skF_3')))!=k7_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 19.36/10.44  tff(c_47076, plain, (k7_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k5_relat_1(k7_relat_1('#skF_1', '#skF_3'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_3')) | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_46965, c_20])).
% 19.36/10.44  tff(c_47596, plain, (k7_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k5_relat_1(k7_relat_1('#skF_1', '#skF_3'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28, c_24, c_47076])).
% 19.36/10.44  tff(c_47815, plain, (~v1_relat_1(k7_relat_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_47596])).
% 19.36/10.44  tff(c_47818, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_18, c_47815])).
% 19.36/10.44  tff(c_47822, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_47818])).
% 19.36/10.44  tff(c_47823, plain, (k7_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k5_relat_1(k7_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_47596])).
% 19.36/10.44  tff(c_47827, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2, c_47823])).
% 19.36/10.44  tff(c_47831, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_47827])).
% 19.36/10.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.36/10.44  
% 19.36/10.44  Inference rules
% 19.36/10.44  ----------------------
% 19.36/10.44  #Ref     : 0
% 19.36/10.44  #Sup     : 9955
% 19.36/10.44  #Fact    : 0
% 19.36/10.44  #Define  : 0
% 19.36/10.44  #Split   : 1
% 19.36/10.44  #Chain   : 0
% 19.36/10.44  #Close   : 0
% 19.36/10.44  
% 19.36/10.44  Ordering : KBO
% 19.36/10.44  
% 19.36/10.44  Simplification rules
% 19.36/10.44  ----------------------
% 19.36/10.44  #Subsume      : 284
% 19.36/10.44  #Demod        : 27205
% 19.36/10.44  #Tautology    : 3943
% 19.36/10.44  #SimpNegUnit  : 0
% 19.36/10.44  #BackRed      : 3
% 19.36/10.44  
% 19.36/10.44  #Partial instantiations: 0
% 19.36/10.44  #Strategies tried      : 1
% 19.36/10.44  
% 19.36/10.44  Timing (in seconds)
% 19.36/10.44  ----------------------
% 19.36/10.44  Preprocessing        : 0.32
% 19.36/10.44  Parsing              : 0.17
% 19.36/10.44  CNF conversion       : 0.02
% 19.36/10.44  Main loop            : 9.32
% 19.36/10.44  Inferencing          : 1.87
% 19.36/10.44  Reduction            : 5.24
% 19.36/10.44  Demodulation         : 4.71
% 19.36/10.44  BG Simplification    : 0.29
% 19.36/10.44  Subsumption          : 1.61
% 19.36/10.44  Abstraction          : 0.64
% 19.36/10.44  MUC search           : 0.00
% 19.36/10.44  Cooper               : 0.00
% 19.36/10.44  Total                : 9.67
% 19.36/10.44  Index Insertion      : 0.00
% 19.36/10.44  Index Deletion       : 0.00
% 19.36/10.44  Index Matching       : 0.00
% 19.36/10.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
