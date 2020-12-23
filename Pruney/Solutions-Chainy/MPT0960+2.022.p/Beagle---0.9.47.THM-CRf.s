%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:39 EST 2020

% Result     : Theorem 9.83s
% Output     : CNFRefutation 9.83s
% Verified   : 
% Statistics : Number of formulae       :   57 (  74 expanded)
%              Number of leaves         :   27 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :   70 ( 100 expanded)
%              Number of equality atoms :   16 (  25 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_wellord2 > k1_relat_1 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_74,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_77,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_wellord2(A),k2_zfmisc_1(A,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_wellord2)).

tff(c_42,plain,(
    ! [A_26] : v1_relat_1(k1_wellord2(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_36,plain,(
    ! [A_18] :
      ( k3_relat_1(k1_wellord2(A_18)) = A_18
      | ~ v1_relat_1(k1_wellord2(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_50,plain,(
    ! [A_18] : k3_relat_1(k1_wellord2(A_18)) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36])).

tff(c_20,plain,(
    ! [A_16] :
      ( k2_xboole_0(k1_relat_1(A_16),k2_relat_1(A_16)) = k3_relat_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18,plain,(
    ! [C_15,A_13,B_14] : k2_xboole_0(k2_zfmisc_1(C_15,A_13),k2_zfmisc_1(C_15,B_14)) = k2_zfmisc_1(C_15,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_189,plain,(
    ! [A_48] :
      ( k2_xboole_0(k1_relat_1(A_48),k2_relat_1(A_48)) = k3_relat_1(A_48)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_213,plain,(
    ! [A_49] :
      ( r1_tarski(k1_relat_1(A_49),k3_relat_1(A_49))
      | ~ v1_relat_1(A_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_14])).

tff(c_221,plain,(
    ! [A_18] :
      ( r1_tarski(k1_relat_1(k1_wellord2(A_18)),A_18)
      | ~ v1_relat_1(k1_wellord2(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_213])).

tff(c_226,plain,(
    ! [A_50] : r1_tarski(k1_relat_1(k1_wellord2(A_50)),A_50) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_221])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_233,plain,(
    ! [A_50] : k2_xboole_0(k1_relat_1(k1_wellord2(A_50)),A_50) = A_50 ),
    inference(resolution,[status(thm)],[c_226,c_12])).

tff(c_16,plain,(
    ! [A_13,C_15,B_14] : k2_xboole_0(k2_zfmisc_1(A_13,C_15),k2_zfmisc_1(B_14,C_15)) = k2_zfmisc_1(k2_xboole_0(A_13,B_14),C_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_133,plain,(
    ! [A_43,C_44,B_45] :
      ( r1_tarski(A_43,k2_xboole_0(C_44,B_45))
      | ~ r1_tarski(A_43,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(k2_xboole_0(A_6,B_7),C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1775,plain,(
    ! [A_142,C_143,B_144,B_145] :
      ( r1_tarski(A_142,k2_xboole_0(C_143,B_144))
      | ~ r1_tarski(k2_xboole_0(A_142,B_145),B_144) ) ),
    inference(resolution,[status(thm)],[c_133,c_10])).

tff(c_1832,plain,(
    ! [A_146,C_147,B_148] : r1_tarski(A_146,k2_xboole_0(C_147,k2_xboole_0(A_146,B_148))) ),
    inference(resolution,[status(thm)],[c_6,c_1775])).

tff(c_17822,plain,(
    ! [A_447,C_448,C_449,B_450] : r1_tarski(k2_zfmisc_1(A_447,C_448),k2_xboole_0(C_449,k2_zfmisc_1(k2_xboole_0(A_447,B_450),C_448))) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1832])).

tff(c_20958,plain,(
    ! [A_500,C_501,C_502] : r1_tarski(k2_zfmisc_1(k1_relat_1(k1_wellord2(A_500)),C_501),k2_xboole_0(C_502,k2_zfmisc_1(A_500,C_501))) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_17822])).

tff(c_234,plain,(
    ! [A_51] :
      ( r1_tarski(A_51,k2_zfmisc_1(k1_relat_1(A_51),k2_relat_1(A_51)))
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6338,plain,(
    ! [A_259] :
      ( k2_xboole_0(A_259,k2_zfmisc_1(k1_relat_1(A_259),k2_relat_1(A_259))) = k2_zfmisc_1(k1_relat_1(A_259),k2_relat_1(A_259))
      | ~ v1_relat_1(A_259) ) ),
    inference(resolution,[status(thm)],[c_234,c_12])).

tff(c_6562,plain,(
    ! [A_259,C_8] :
      ( r1_tarski(A_259,C_8)
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(A_259),k2_relat_1(A_259)),C_8)
      | ~ v1_relat_1(A_259) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6338,c_10])).

tff(c_20962,plain,(
    ! [A_500,C_502] :
      ( r1_tarski(k1_wellord2(A_500),k2_xboole_0(C_502,k2_zfmisc_1(A_500,k2_relat_1(k1_wellord2(A_500)))))
      | ~ v1_relat_1(k1_wellord2(A_500)) ) ),
    inference(resolution,[status(thm)],[c_20958,c_6562])).

tff(c_21083,plain,(
    ! [A_503,C_504] : r1_tarski(k1_wellord2(A_503),k2_xboole_0(C_504,k2_zfmisc_1(A_503,k2_relat_1(k1_wellord2(A_503))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_20962])).

tff(c_21188,plain,(
    ! [C_505,A_506] : r1_tarski(k1_wellord2(C_505),k2_zfmisc_1(C_505,k2_xboole_0(A_506,k2_relat_1(k1_wellord2(C_505))))) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_21083])).

tff(c_21267,plain,(
    ! [C_505] :
      ( r1_tarski(k1_wellord2(C_505),k2_zfmisc_1(C_505,k3_relat_1(k1_wellord2(C_505))))
      | ~ v1_relat_1(k1_wellord2(C_505)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_21188])).

tff(c_21293,plain,(
    ! [C_505] : r1_tarski(k1_wellord2(C_505),k2_zfmisc_1(C_505,C_505)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_50,c_21267])).

tff(c_44,plain,(
    ~ r1_tarski(k1_wellord2('#skF_3'),k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_21423,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21293,c_44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:57:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.83/4.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.83/4.19  
% 9.83/4.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.83/4.19  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_wellord2 > k1_relat_1 > #skF_3 > #skF_2 > #skF_1
% 9.83/4.19  
% 9.83/4.19  %Foreground sorts:
% 9.83/4.19  
% 9.83/4.19  
% 9.83/4.19  %Background operators:
% 9.83/4.19  
% 9.83/4.19  
% 9.83/4.19  %Foreground operators:
% 9.83/4.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.83/4.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.83/4.19  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.83/4.19  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 9.83/4.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.83/4.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.83/4.19  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 9.83/4.19  tff('#skF_3', type, '#skF_3': $i).
% 9.83/4.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.83/4.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.83/4.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.83/4.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.83/4.19  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.83/4.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.83/4.19  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.83/4.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.83/4.19  
% 9.83/4.20  tff(f_74, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 9.83/4.20  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 9.83/4.20  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 9.83/4.20  tff(f_49, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 9.83/4.20  tff(f_45, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 9.83/4.20  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 9.83/4.20  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.83/4.20  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 9.83/4.20  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 9.83/4.20  tff(f_57, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 9.83/4.20  tff(f_77, negated_conjecture, ~(![A]: r1_tarski(k1_wellord2(A), k2_zfmisc_1(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_wellord2)).
% 9.83/4.20  tff(c_42, plain, (![A_26]: (v1_relat_1(k1_wellord2(A_26)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.83/4.20  tff(c_36, plain, (![A_18]: (k3_relat_1(k1_wellord2(A_18))=A_18 | ~v1_relat_1(k1_wellord2(A_18)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.83/4.20  tff(c_50, plain, (![A_18]: (k3_relat_1(k1_wellord2(A_18))=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36])).
% 9.83/4.20  tff(c_20, plain, (![A_16]: (k2_xboole_0(k1_relat_1(A_16), k2_relat_1(A_16))=k3_relat_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.83/4.20  tff(c_18, plain, (![C_15, A_13, B_14]: (k2_xboole_0(k2_zfmisc_1(C_15, A_13), k2_zfmisc_1(C_15, B_14))=k2_zfmisc_1(C_15, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.83/4.20  tff(c_189, plain, (![A_48]: (k2_xboole_0(k1_relat_1(A_48), k2_relat_1(A_48))=k3_relat_1(A_48) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.83/4.20  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.83/4.20  tff(c_213, plain, (![A_49]: (r1_tarski(k1_relat_1(A_49), k3_relat_1(A_49)) | ~v1_relat_1(A_49))), inference(superposition, [status(thm), theory('equality')], [c_189, c_14])).
% 9.83/4.20  tff(c_221, plain, (![A_18]: (r1_tarski(k1_relat_1(k1_wellord2(A_18)), A_18) | ~v1_relat_1(k1_wellord2(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_213])).
% 9.83/4.20  tff(c_226, plain, (![A_50]: (r1_tarski(k1_relat_1(k1_wellord2(A_50)), A_50))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_221])).
% 9.83/4.20  tff(c_12, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.83/4.20  tff(c_233, plain, (![A_50]: (k2_xboole_0(k1_relat_1(k1_wellord2(A_50)), A_50)=A_50)), inference(resolution, [status(thm)], [c_226, c_12])).
% 9.83/4.20  tff(c_16, plain, (![A_13, C_15, B_14]: (k2_xboole_0(k2_zfmisc_1(A_13, C_15), k2_zfmisc_1(B_14, C_15))=k2_zfmisc_1(k2_xboole_0(A_13, B_14), C_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.83/4.20  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.83/4.20  tff(c_133, plain, (![A_43, C_44, B_45]: (r1_tarski(A_43, k2_xboole_0(C_44, B_45)) | ~r1_tarski(A_43, B_45))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.83/4.20  tff(c_10, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(k2_xboole_0(A_6, B_7), C_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.83/4.20  tff(c_1775, plain, (![A_142, C_143, B_144, B_145]: (r1_tarski(A_142, k2_xboole_0(C_143, B_144)) | ~r1_tarski(k2_xboole_0(A_142, B_145), B_144))), inference(resolution, [status(thm)], [c_133, c_10])).
% 9.83/4.20  tff(c_1832, plain, (![A_146, C_147, B_148]: (r1_tarski(A_146, k2_xboole_0(C_147, k2_xboole_0(A_146, B_148))))), inference(resolution, [status(thm)], [c_6, c_1775])).
% 9.83/4.20  tff(c_17822, plain, (![A_447, C_448, C_449, B_450]: (r1_tarski(k2_zfmisc_1(A_447, C_448), k2_xboole_0(C_449, k2_zfmisc_1(k2_xboole_0(A_447, B_450), C_448))))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1832])).
% 9.83/4.20  tff(c_20958, plain, (![A_500, C_501, C_502]: (r1_tarski(k2_zfmisc_1(k1_relat_1(k1_wellord2(A_500)), C_501), k2_xboole_0(C_502, k2_zfmisc_1(A_500, C_501))))), inference(superposition, [status(thm), theory('equality')], [c_233, c_17822])).
% 9.83/4.20  tff(c_234, plain, (![A_51]: (r1_tarski(A_51, k2_zfmisc_1(k1_relat_1(A_51), k2_relat_1(A_51))) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.83/4.20  tff(c_6338, plain, (![A_259]: (k2_xboole_0(A_259, k2_zfmisc_1(k1_relat_1(A_259), k2_relat_1(A_259)))=k2_zfmisc_1(k1_relat_1(A_259), k2_relat_1(A_259)) | ~v1_relat_1(A_259))), inference(resolution, [status(thm)], [c_234, c_12])).
% 9.83/4.20  tff(c_6562, plain, (![A_259, C_8]: (r1_tarski(A_259, C_8) | ~r1_tarski(k2_zfmisc_1(k1_relat_1(A_259), k2_relat_1(A_259)), C_8) | ~v1_relat_1(A_259))), inference(superposition, [status(thm), theory('equality')], [c_6338, c_10])).
% 9.83/4.20  tff(c_20962, plain, (![A_500, C_502]: (r1_tarski(k1_wellord2(A_500), k2_xboole_0(C_502, k2_zfmisc_1(A_500, k2_relat_1(k1_wellord2(A_500))))) | ~v1_relat_1(k1_wellord2(A_500)))), inference(resolution, [status(thm)], [c_20958, c_6562])).
% 9.83/4.20  tff(c_21083, plain, (![A_503, C_504]: (r1_tarski(k1_wellord2(A_503), k2_xboole_0(C_504, k2_zfmisc_1(A_503, k2_relat_1(k1_wellord2(A_503))))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_20962])).
% 9.83/4.20  tff(c_21188, plain, (![C_505, A_506]: (r1_tarski(k1_wellord2(C_505), k2_zfmisc_1(C_505, k2_xboole_0(A_506, k2_relat_1(k1_wellord2(C_505))))))), inference(superposition, [status(thm), theory('equality')], [c_18, c_21083])).
% 9.83/4.20  tff(c_21267, plain, (![C_505]: (r1_tarski(k1_wellord2(C_505), k2_zfmisc_1(C_505, k3_relat_1(k1_wellord2(C_505)))) | ~v1_relat_1(k1_wellord2(C_505)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_21188])).
% 9.83/4.20  tff(c_21293, plain, (![C_505]: (r1_tarski(k1_wellord2(C_505), k2_zfmisc_1(C_505, C_505)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_50, c_21267])).
% 9.83/4.20  tff(c_44, plain, (~r1_tarski(k1_wellord2('#skF_3'), k2_zfmisc_1('#skF_3', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.83/4.20  tff(c_21423, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21293, c_44])).
% 9.83/4.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.83/4.20  
% 9.83/4.20  Inference rules
% 9.83/4.20  ----------------------
% 9.83/4.20  #Ref     : 0
% 9.83/4.20  #Sup     : 5539
% 9.83/4.20  #Fact    : 0
% 9.83/4.20  #Define  : 0
% 9.83/4.20  #Split   : 0
% 9.83/4.20  #Chain   : 0
% 9.83/4.20  #Close   : 0
% 9.83/4.20  
% 9.83/4.20  Ordering : KBO
% 9.83/4.20  
% 9.83/4.20  Simplification rules
% 9.83/4.20  ----------------------
% 9.83/4.20  #Subsume      : 640
% 9.83/4.20  #Demod        : 2112
% 9.83/4.20  #Tautology    : 1886
% 9.83/4.20  #SimpNegUnit  : 0
% 9.83/4.20  #BackRed      : 1
% 9.83/4.20  
% 9.83/4.20  #Partial instantiations: 0
% 9.83/4.20  #Strategies tried      : 1
% 9.83/4.20  
% 9.83/4.20  Timing (in seconds)
% 9.83/4.20  ----------------------
% 9.83/4.21  Preprocessing        : 0.32
% 9.83/4.21  Parsing              : 0.17
% 9.83/4.21  CNF conversion       : 0.02
% 9.83/4.21  Main loop            : 3.09
% 9.83/4.21  Inferencing          : 0.61
% 9.83/4.21  Reduction            : 1.33
% 9.83/4.21  Demodulation         : 1.14
% 9.83/4.21  BG Simplification    : 0.09
% 9.83/4.21  Subsumption          : 0.86
% 9.83/4.21  Abstraction          : 0.10
% 9.83/4.21  MUC search           : 0.00
% 9.83/4.21  Cooper               : 0.00
% 9.83/4.21  Total                : 3.43
% 9.83/4.21  Index Insertion      : 0.00
% 9.83/4.21  Index Deletion       : 0.00
% 9.83/4.21  Index Matching       : 0.00
% 9.83/4.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
