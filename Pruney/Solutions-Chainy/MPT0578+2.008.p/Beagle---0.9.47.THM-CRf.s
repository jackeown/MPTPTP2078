%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:56 EST 2020

% Result     : Theorem 47.99s
% Output     : CNFRefutation 47.99s
% Verified   : 
% Statistics : Number of formulae       :   47 (  58 expanded)
%              Number of leaves         :   21 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :   95 ( 119 expanded)
%              Number of equality atoms :   18 (  26 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k5_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_28,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k5_relat_1(A_7,B_8))
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_64,plain,(
    ! [B_31,A_32] :
      ( r1_tarski(k10_relat_1(B_31,A_32),k1_relat_1(B_31))
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_71,plain,(
    ! [B_31,A_32] :
      ( k2_xboole_0(k10_relat_1(B_31,A_32),k1_relat_1(B_31)) = k1_relat_1(B_31)
      | ~ v1_relat_1(B_31) ) ),
    inference(resolution,[status(thm)],[c_64,c_8])).

tff(c_152,plain,(
    ! [B_44,C_45,A_46] :
      ( k10_relat_1(k5_relat_1(B_44,C_45),A_46) = k10_relat_1(B_44,k10_relat_1(C_45,A_46))
      | ~ v1_relat_1(C_45)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_16,plain,(
    ! [A_11] :
      ( k10_relat_1(A_11,k2_relat_1(A_11)) = k1_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1990,plain,(
    ! [B_127,C_128] :
      ( k10_relat_1(B_127,k10_relat_1(C_128,k2_relat_1(k5_relat_1(B_127,C_128)))) = k1_relat_1(k5_relat_1(B_127,C_128))
      | ~ v1_relat_1(k5_relat_1(B_127,C_128))
      | ~ v1_relat_1(C_128)
      | ~ v1_relat_1(B_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_16])).

tff(c_203,plain,(
    ! [C_51,A_52,B_53] :
      ( k2_xboole_0(k10_relat_1(C_51,A_52),k10_relat_1(C_51,B_53)) = k10_relat_1(C_51,k2_xboole_0(A_52,B_53))
      | ~ v1_relat_1(C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(A_5,k2_xboole_0(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_219,plain,(
    ! [C_51,A_52,B_53] :
      ( r1_tarski(k10_relat_1(C_51,A_52),k10_relat_1(C_51,k2_xboole_0(A_52,B_53)))
      | ~ v1_relat_1(C_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_10])).

tff(c_22818,plain,(
    ! [B_426,C_427,B_428] :
      ( r1_tarski(k1_relat_1(k5_relat_1(B_426,C_427)),k10_relat_1(B_426,k2_xboole_0(k10_relat_1(C_427,k2_relat_1(k5_relat_1(B_426,C_427))),B_428)))
      | ~ v1_relat_1(B_426)
      | ~ v1_relat_1(k5_relat_1(B_426,C_427))
      | ~ v1_relat_1(C_427)
      | ~ v1_relat_1(B_426) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1990,c_219])).

tff(c_125356,plain,(
    ! [B_1019,B_1020] :
      ( r1_tarski(k1_relat_1(k5_relat_1(B_1019,B_1020)),k10_relat_1(B_1019,k1_relat_1(B_1020)))
      | ~ v1_relat_1(B_1019)
      | ~ v1_relat_1(k5_relat_1(B_1019,B_1020))
      | ~ v1_relat_1(B_1020)
      | ~ v1_relat_1(B_1019)
      | ~ v1_relat_1(B_1020) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_22818])).

tff(c_137696,plain,(
    ! [B_1084,B_1085] :
      ( k2_xboole_0(k1_relat_1(k5_relat_1(B_1084,B_1085)),k10_relat_1(B_1084,k1_relat_1(B_1085))) = k10_relat_1(B_1084,k1_relat_1(B_1085))
      | ~ v1_relat_1(k5_relat_1(B_1084,B_1085))
      | ~ v1_relat_1(B_1084)
      | ~ v1_relat_1(B_1085) ) ),
    inference(resolution,[status(thm)],[c_125356,c_8])).

tff(c_137750,plain,(
    ! [B_1084,B_1085] :
      ( r1_tarski(k1_relat_1(k5_relat_1(B_1084,B_1085)),k10_relat_1(B_1084,k1_relat_1(B_1085)))
      | ~ v1_relat_1(k5_relat_1(B_1084,B_1085))
      | ~ v1_relat_1(B_1084)
      | ~ v1_relat_1(B_1085) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137696,c_10])).

tff(c_14,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k10_relat_1(B_10,A_9),k1_relat_1(B_10))
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1386,plain,(
    ! [B_108,C_109,A_110] :
      ( r1_tarski(k10_relat_1(B_108,k10_relat_1(C_109,A_110)),k1_relat_1(k5_relat_1(B_108,C_109)))
      | ~ v1_relat_1(k5_relat_1(B_108,C_109))
      | ~ v1_relat_1(C_109)
      | ~ v1_relat_1(B_108) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_14])).

tff(c_8378,plain,(
    ! [B_253,A_254] :
      ( r1_tarski(k10_relat_1(B_253,k1_relat_1(A_254)),k1_relat_1(k5_relat_1(B_253,A_254)))
      | ~ v1_relat_1(k5_relat_1(B_253,A_254))
      | ~ v1_relat_1(A_254)
      | ~ v1_relat_1(B_253)
      | ~ v1_relat_1(A_254) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1386])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_204526,plain,(
    ! [B_1373,A_1374] :
      ( k10_relat_1(B_1373,k1_relat_1(A_1374)) = k1_relat_1(k5_relat_1(B_1373,A_1374))
      | ~ r1_tarski(k1_relat_1(k5_relat_1(B_1373,A_1374)),k10_relat_1(B_1373,k1_relat_1(A_1374)))
      | ~ v1_relat_1(k5_relat_1(B_1373,A_1374))
      | ~ v1_relat_1(B_1373)
      | ~ v1_relat_1(A_1374) ) ),
    inference(resolution,[status(thm)],[c_8378,c_2])).

tff(c_204535,plain,(
    ! [B_1375,B_1376] :
      ( k10_relat_1(B_1375,k1_relat_1(B_1376)) = k1_relat_1(k5_relat_1(B_1375,B_1376))
      | ~ v1_relat_1(k5_relat_1(B_1375,B_1376))
      | ~ v1_relat_1(B_1375)
      | ~ v1_relat_1(B_1376) ) ),
    inference(resolution,[status(thm)],[c_137750,c_204526])).

tff(c_204540,plain,(
    ! [A_1377,B_1378] :
      ( k10_relat_1(A_1377,k1_relat_1(B_1378)) = k1_relat_1(k5_relat_1(A_1377,B_1378))
      | ~ v1_relat_1(B_1378)
      | ~ v1_relat_1(A_1377) ) ),
    inference(resolution,[status(thm)],[c_12,c_204535])).

tff(c_24,plain,(
    k10_relat_1('#skF_1',k1_relat_1('#skF_2')) != k1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_205474,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_204540,c_24])).

tff(c_205490,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_205474])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:25:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 47.99/35.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 47.99/35.35  
% 47.99/35.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 47.99/35.35  %$ r1_tarski > v1_relat_1 > k5_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 47.99/35.35  
% 47.99/35.35  %Foreground sorts:
% 47.99/35.35  
% 47.99/35.35  
% 47.99/35.35  %Background operators:
% 47.99/35.35  
% 47.99/35.35  
% 47.99/35.35  %Foreground operators:
% 47.99/35.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 47.99/35.35  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 47.99/35.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 47.99/35.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 47.99/35.35  tff('#skF_2', type, '#skF_2': $i).
% 47.99/35.35  tff('#skF_1', type, '#skF_1': $i).
% 47.99/35.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 47.99/35.35  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 47.99/35.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 47.99/35.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 47.99/35.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 47.99/35.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 47.99/35.35  
% 47.99/35.36  tff(f_77, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 47.99/35.36  tff(f_43, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 47.99/35.36  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 47.99/35.36  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 47.99/35.36  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t181_relat_1)).
% 47.99/35.36  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 47.99/35.36  tff(f_55, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 47.99/35.36  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 47.99/35.36  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 47.99/35.36  tff(c_28, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 47.99/35.36  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_77])).
% 47.99/35.36  tff(c_12, plain, (![A_7, B_8]: (v1_relat_1(k5_relat_1(A_7, B_8)) | ~v1_relat_1(B_8) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 47.99/35.36  tff(c_64, plain, (![B_31, A_32]: (r1_tarski(k10_relat_1(B_31, A_32), k1_relat_1(B_31)) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_47])).
% 47.99/35.36  tff(c_8, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 47.99/35.36  tff(c_71, plain, (![B_31, A_32]: (k2_xboole_0(k10_relat_1(B_31, A_32), k1_relat_1(B_31))=k1_relat_1(B_31) | ~v1_relat_1(B_31))), inference(resolution, [status(thm)], [c_64, c_8])).
% 47.99/35.36  tff(c_152, plain, (![B_44, C_45, A_46]: (k10_relat_1(k5_relat_1(B_44, C_45), A_46)=k10_relat_1(B_44, k10_relat_1(C_45, A_46)) | ~v1_relat_1(C_45) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_62])).
% 47.99/35.36  tff(c_16, plain, (![A_11]: (k10_relat_1(A_11, k2_relat_1(A_11))=k1_relat_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 47.99/35.36  tff(c_1990, plain, (![B_127, C_128]: (k10_relat_1(B_127, k10_relat_1(C_128, k2_relat_1(k5_relat_1(B_127, C_128))))=k1_relat_1(k5_relat_1(B_127, C_128)) | ~v1_relat_1(k5_relat_1(B_127, C_128)) | ~v1_relat_1(C_128) | ~v1_relat_1(B_127))), inference(superposition, [status(thm), theory('equality')], [c_152, c_16])).
% 47.99/35.36  tff(c_203, plain, (![C_51, A_52, B_53]: (k2_xboole_0(k10_relat_1(C_51, A_52), k10_relat_1(C_51, B_53))=k10_relat_1(C_51, k2_xboole_0(A_52, B_53)) | ~v1_relat_1(C_51))), inference(cnfTransformation, [status(thm)], [f_55])).
% 47.99/35.36  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, k2_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 47.99/35.36  tff(c_219, plain, (![C_51, A_52, B_53]: (r1_tarski(k10_relat_1(C_51, A_52), k10_relat_1(C_51, k2_xboole_0(A_52, B_53))) | ~v1_relat_1(C_51))), inference(superposition, [status(thm), theory('equality')], [c_203, c_10])).
% 47.99/35.36  tff(c_22818, plain, (![B_426, C_427, B_428]: (r1_tarski(k1_relat_1(k5_relat_1(B_426, C_427)), k10_relat_1(B_426, k2_xboole_0(k10_relat_1(C_427, k2_relat_1(k5_relat_1(B_426, C_427))), B_428))) | ~v1_relat_1(B_426) | ~v1_relat_1(k5_relat_1(B_426, C_427)) | ~v1_relat_1(C_427) | ~v1_relat_1(B_426))), inference(superposition, [status(thm), theory('equality')], [c_1990, c_219])).
% 47.99/35.36  tff(c_125356, plain, (![B_1019, B_1020]: (r1_tarski(k1_relat_1(k5_relat_1(B_1019, B_1020)), k10_relat_1(B_1019, k1_relat_1(B_1020))) | ~v1_relat_1(B_1019) | ~v1_relat_1(k5_relat_1(B_1019, B_1020)) | ~v1_relat_1(B_1020) | ~v1_relat_1(B_1019) | ~v1_relat_1(B_1020))), inference(superposition, [status(thm), theory('equality')], [c_71, c_22818])).
% 47.99/35.36  tff(c_137696, plain, (![B_1084, B_1085]: (k2_xboole_0(k1_relat_1(k5_relat_1(B_1084, B_1085)), k10_relat_1(B_1084, k1_relat_1(B_1085)))=k10_relat_1(B_1084, k1_relat_1(B_1085)) | ~v1_relat_1(k5_relat_1(B_1084, B_1085)) | ~v1_relat_1(B_1084) | ~v1_relat_1(B_1085))), inference(resolution, [status(thm)], [c_125356, c_8])).
% 47.99/35.36  tff(c_137750, plain, (![B_1084, B_1085]: (r1_tarski(k1_relat_1(k5_relat_1(B_1084, B_1085)), k10_relat_1(B_1084, k1_relat_1(B_1085))) | ~v1_relat_1(k5_relat_1(B_1084, B_1085)) | ~v1_relat_1(B_1084) | ~v1_relat_1(B_1085))), inference(superposition, [status(thm), theory('equality')], [c_137696, c_10])).
% 47.99/35.36  tff(c_14, plain, (![B_10, A_9]: (r1_tarski(k10_relat_1(B_10, A_9), k1_relat_1(B_10)) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 47.99/35.36  tff(c_1386, plain, (![B_108, C_109, A_110]: (r1_tarski(k10_relat_1(B_108, k10_relat_1(C_109, A_110)), k1_relat_1(k5_relat_1(B_108, C_109))) | ~v1_relat_1(k5_relat_1(B_108, C_109)) | ~v1_relat_1(C_109) | ~v1_relat_1(B_108))), inference(superposition, [status(thm), theory('equality')], [c_152, c_14])).
% 47.99/35.36  tff(c_8378, plain, (![B_253, A_254]: (r1_tarski(k10_relat_1(B_253, k1_relat_1(A_254)), k1_relat_1(k5_relat_1(B_253, A_254))) | ~v1_relat_1(k5_relat_1(B_253, A_254)) | ~v1_relat_1(A_254) | ~v1_relat_1(B_253) | ~v1_relat_1(A_254))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1386])).
% 47.99/35.36  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 47.99/35.36  tff(c_204526, plain, (![B_1373, A_1374]: (k10_relat_1(B_1373, k1_relat_1(A_1374))=k1_relat_1(k5_relat_1(B_1373, A_1374)) | ~r1_tarski(k1_relat_1(k5_relat_1(B_1373, A_1374)), k10_relat_1(B_1373, k1_relat_1(A_1374))) | ~v1_relat_1(k5_relat_1(B_1373, A_1374)) | ~v1_relat_1(B_1373) | ~v1_relat_1(A_1374))), inference(resolution, [status(thm)], [c_8378, c_2])).
% 47.99/35.36  tff(c_204535, plain, (![B_1375, B_1376]: (k10_relat_1(B_1375, k1_relat_1(B_1376))=k1_relat_1(k5_relat_1(B_1375, B_1376)) | ~v1_relat_1(k5_relat_1(B_1375, B_1376)) | ~v1_relat_1(B_1375) | ~v1_relat_1(B_1376))), inference(resolution, [status(thm)], [c_137750, c_204526])).
% 47.99/35.36  tff(c_204540, plain, (![A_1377, B_1378]: (k10_relat_1(A_1377, k1_relat_1(B_1378))=k1_relat_1(k5_relat_1(A_1377, B_1378)) | ~v1_relat_1(B_1378) | ~v1_relat_1(A_1377))), inference(resolution, [status(thm)], [c_12, c_204535])).
% 47.99/35.36  tff(c_24, plain, (k10_relat_1('#skF_1', k1_relat_1('#skF_2'))!=k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 47.99/35.36  tff(c_205474, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_204540, c_24])).
% 47.99/35.36  tff(c_205490, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_205474])).
% 47.99/35.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 47.99/35.36  
% 47.99/35.36  Inference rules
% 47.99/35.36  ----------------------
% 47.99/35.36  #Ref     : 0
% 47.99/35.36  #Sup     : 60185
% 47.99/35.36  #Fact    : 0
% 47.99/35.36  #Define  : 0
% 47.99/35.36  #Split   : 0
% 47.99/35.36  #Chain   : 0
% 47.99/35.36  #Close   : 0
% 47.99/35.36  
% 47.99/35.36  Ordering : KBO
% 47.99/35.36  
% 47.99/35.36  Simplification rules
% 47.99/35.36  ----------------------
% 47.99/35.36  #Subsume      : 31819
% 47.99/35.36  #Demod        : 9035
% 47.99/35.36  #Tautology    : 3803
% 47.99/35.36  #SimpNegUnit  : 0
% 47.99/35.36  #BackRed      : 0
% 47.99/35.36  
% 47.99/35.36  #Partial instantiations: 0
% 47.99/35.36  #Strategies tried      : 1
% 47.99/35.36  
% 47.99/35.36  Timing (in seconds)
% 47.99/35.36  ----------------------
% 47.99/35.36  Preprocessing        : 0.29
% 47.99/35.36  Parsing              : 0.15
% 47.99/35.36  CNF conversion       : 0.02
% 47.99/35.36  Main loop            : 34.32
% 47.99/35.36  Inferencing          : 8.15
% 47.99/35.36  Reduction            : 5.39
% 47.99/35.36  Demodulation         : 3.69
% 47.99/35.36  BG Simplification    : 1.08
% 47.99/35.36  Subsumption          : 18.25
% 47.99/35.36  Abstraction          : 1.76
% 47.99/35.36  MUC search           : 0.00
% 47.99/35.36  Cooper               : 0.00
% 47.99/35.36  Total                : 34.63
% 47.99/35.36  Index Insertion      : 0.00
% 47.99/35.37  Index Deletion       : 0.00
% 47.99/35.37  Index Matching       : 0.00
% 47.99/35.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
