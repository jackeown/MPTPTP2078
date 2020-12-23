%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:34 EST 2020

% Result     : Theorem 6.19s
% Output     : CNFRefutation 6.49s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 129 expanded)
%              Number of leaves         :   20 (  52 expanded)
%              Depth                    :   14
%              Number of atoms          :   96 ( 253 expanded)
%              Number of equality atoms :    9 (  25 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_24,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_16,plain,(
    ! [A_16,B_18] :
      ( r1_tarski(k2_relat_1(A_16),k2_relat_1(B_18))
      | ~ r1_tarski(A_16,B_18)
      | ~ v1_relat_1(B_18)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_18,plain,(
    ! [A_16,B_18] :
      ( r1_tarski(k1_relat_1(A_16),k1_relat_1(B_18))
      | ~ r1_tarski(A_16,B_18)
      | ~ v1_relat_1(B_18)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_14,plain,(
    ! [A_15] :
      ( k2_xboole_0(k1_relat_1(A_15),k2_relat_1(A_15)) = k3_relat_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_391,plain,(
    ! [A_55,C_56,B_57] :
      ( r1_tarski(k2_xboole_0(A_55,C_56),k2_xboole_0(B_57,C_56))
      | ~ r1_tarski(A_55,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_874,plain,(
    ! [A_75,B_76,C_77] :
      ( r1_tarski(A_75,k2_xboole_0(B_76,C_77))
      | ~ r1_tarski(A_75,B_76) ) ),
    inference(resolution,[status(thm)],[c_391,c_2])).

tff(c_7700,plain,(
    ! [A_221,A_222] :
      ( r1_tarski(A_221,k3_relat_1(A_222))
      | ~ r1_tarski(A_221,k1_relat_1(A_222))
      | ~ v1_relat_1(A_222) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_874])).

tff(c_722,plain,(
    ! [A_66,C_67,B_68] :
      ( r1_tarski(k2_xboole_0(A_66,C_67),B_68)
      | ~ r1_tarski(C_67,B_68)
      | ~ r1_tarski(A_66,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6696,plain,(
    ! [A_208,B_209] :
      ( r1_tarski(k3_relat_1(A_208),B_209)
      | ~ r1_tarski(k2_relat_1(A_208),B_209)
      | ~ r1_tarski(k1_relat_1(A_208),B_209)
      | ~ v1_relat_1(A_208) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_722])).

tff(c_20,plain,(
    ~ r1_tarski(k3_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6712,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k3_relat_1('#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k3_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6696,c_20])).

tff(c_6719,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k3_relat_1('#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_6712])).

tff(c_7045,plain,(
    ~ r1_tarski(k1_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_6719])).

tff(c_7706,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_7700,c_7045])).

tff(c_7740,plain,(
    ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_7706])).

tff(c_7759,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_7740])).

tff(c_7763,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_7759])).

tff(c_7765,plain,(
    r1_tarski(k1_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_6719])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_7769,plain,(
    k2_xboole_0(k1_relat_1('#skF_1'),k3_relat_1('#skF_2')) = k3_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_7765,c_4])).

tff(c_6,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_29,plain,(
    ! [A_23,B_24] :
      ( k2_xboole_0(A_23,B_24) = B_24
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_41,plain,(
    ! [A_6] : k2_xboole_0(k1_xboole_0,A_6) = A_6 ),
    inference(resolution,[status(thm)],[c_6,c_29])).

tff(c_434,plain,(
    ! [A_6,B_57] :
      ( r1_tarski(A_6,k2_xboole_0(B_57,A_6))
      | ~ r1_tarski(k1_xboole_0,B_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_391])).

tff(c_449,plain,(
    ! [A_58,B_59] : r1_tarski(A_58,k2_xboole_0(B_59,A_58)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_434])).

tff(c_762,plain,(
    ! [A_69] :
      ( r1_tarski(k2_relat_1(A_69),k3_relat_1(A_69))
      | ~ v1_relat_1(A_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_449])).

tff(c_3921,plain,(
    ! [A_159] :
      ( k2_xboole_0(k2_relat_1(A_159),k3_relat_1(A_159)) = k3_relat_1(A_159)
      | ~ v1_relat_1(A_159) ) ),
    inference(resolution,[status(thm)],[c_762,c_4])).

tff(c_488,plain,(
    ! [A_1,B_59,B_2] : r1_tarski(A_1,k2_xboole_0(B_59,k2_xboole_0(A_1,B_2))) ),
    inference(resolution,[status(thm)],[c_449,c_2])).

tff(c_3988,plain,(
    ! [A_159,B_59] :
      ( r1_tarski(k2_relat_1(A_159),k2_xboole_0(B_59,k3_relat_1(A_159)))
      | ~ v1_relat_1(A_159) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3921,c_488])).

tff(c_7788,plain,
    ( r1_tarski(k2_relat_1('#skF_2'),k3_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_7769,c_3988])).

tff(c_7891,plain,(
    r1_tarski(k2_relat_1('#skF_2'),k3_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_7788])).

tff(c_7916,plain,(
    k2_xboole_0(k2_relat_1('#skF_2'),k3_relat_1('#skF_2')) = k3_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_7891,c_4])).

tff(c_445,plain,(
    ! [A_55,B_57,C_56] :
      ( r1_tarski(A_55,k2_xboole_0(B_57,C_56))
      | ~ r1_tarski(A_55,B_57) ) ),
    inference(resolution,[status(thm)],[c_391,c_2])).

tff(c_9262,plain,(
    ! [A_245] :
      ( r1_tarski(A_245,k3_relat_1('#skF_2'))
      | ~ r1_tarski(A_245,k2_relat_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7916,c_445])).

tff(c_7764,plain,(
    ~ r1_tarski(k2_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_6719])).

tff(c_9312,plain,(
    ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_9262,c_7764])).

tff(c_9323,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_9312])).

tff(c_9327,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_9323])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:58:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.19/2.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.19/2.28  
% 6.19/2.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.19/2.28  %$ r1_tarski > v1_relat_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 6.19/2.28  
% 6.19/2.28  %Foreground sorts:
% 6.19/2.28  
% 6.19/2.28  
% 6.19/2.28  %Background operators:
% 6.19/2.28  
% 6.19/2.28  
% 6.19/2.28  %Foreground operators:
% 6.19/2.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.19/2.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.19/2.28  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 6.19/2.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.19/2.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.19/2.28  tff('#skF_2', type, '#skF_2': $i).
% 6.19/2.28  tff('#skF_1', type, '#skF_1': $i).
% 6.19/2.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.19/2.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.19/2.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.19/2.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.19/2.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.19/2.28  
% 6.49/2.29  tff(f_72, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 6.49/2.29  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 6.49/2.29  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 6.49/2.29  tff(f_47, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_xboole_1)).
% 6.49/2.29  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 6.49/2.29  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 6.49/2.29  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 6.49/2.29  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.49/2.29  tff(c_26, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.49/2.29  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.49/2.29  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.49/2.29  tff(c_16, plain, (![A_16, B_18]: (r1_tarski(k2_relat_1(A_16), k2_relat_1(B_18)) | ~r1_tarski(A_16, B_18) | ~v1_relat_1(B_18) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.49/2.29  tff(c_18, plain, (![A_16, B_18]: (r1_tarski(k1_relat_1(A_16), k1_relat_1(B_18)) | ~r1_tarski(A_16, B_18) | ~v1_relat_1(B_18) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.49/2.29  tff(c_14, plain, (![A_15]: (k2_xboole_0(k1_relat_1(A_15), k2_relat_1(A_15))=k3_relat_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.49/2.29  tff(c_391, plain, (![A_55, C_56, B_57]: (r1_tarski(k2_xboole_0(A_55, C_56), k2_xboole_0(B_57, C_56)) | ~r1_tarski(A_55, B_57))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.49/2.29  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.49/2.29  tff(c_874, plain, (![A_75, B_76, C_77]: (r1_tarski(A_75, k2_xboole_0(B_76, C_77)) | ~r1_tarski(A_75, B_76))), inference(resolution, [status(thm)], [c_391, c_2])).
% 6.49/2.29  tff(c_7700, plain, (![A_221, A_222]: (r1_tarski(A_221, k3_relat_1(A_222)) | ~r1_tarski(A_221, k1_relat_1(A_222)) | ~v1_relat_1(A_222))), inference(superposition, [status(thm), theory('equality')], [c_14, c_874])).
% 6.49/2.29  tff(c_722, plain, (![A_66, C_67, B_68]: (r1_tarski(k2_xboole_0(A_66, C_67), B_68) | ~r1_tarski(C_67, B_68) | ~r1_tarski(A_66, B_68))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.49/2.29  tff(c_6696, plain, (![A_208, B_209]: (r1_tarski(k3_relat_1(A_208), B_209) | ~r1_tarski(k2_relat_1(A_208), B_209) | ~r1_tarski(k1_relat_1(A_208), B_209) | ~v1_relat_1(A_208))), inference(superposition, [status(thm), theory('equality')], [c_14, c_722])).
% 6.49/2.29  tff(c_20, plain, (~r1_tarski(k3_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.49/2.29  tff(c_6712, plain, (~r1_tarski(k2_relat_1('#skF_1'), k3_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1('#skF_1'), k3_relat_1('#skF_2')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_6696, c_20])).
% 6.49/2.29  tff(c_6719, plain, (~r1_tarski(k2_relat_1('#skF_1'), k3_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_6712])).
% 6.49/2.29  tff(c_7045, plain, (~r1_tarski(k1_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_6719])).
% 6.49/2.29  tff(c_7706, plain, (~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_7700, c_7045])).
% 6.49/2.29  tff(c_7740, plain, (~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_7706])).
% 6.49/2.29  tff(c_7759, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_18, c_7740])).
% 6.49/2.29  tff(c_7763, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_7759])).
% 6.49/2.29  tff(c_7765, plain, (r1_tarski(k1_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_6719])).
% 6.49/2.29  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.49/2.29  tff(c_7769, plain, (k2_xboole_0(k1_relat_1('#skF_1'), k3_relat_1('#skF_2'))=k3_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_7765, c_4])).
% 6.49/2.29  tff(c_6, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.49/2.29  tff(c_29, plain, (![A_23, B_24]: (k2_xboole_0(A_23, B_24)=B_24 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.49/2.29  tff(c_41, plain, (![A_6]: (k2_xboole_0(k1_xboole_0, A_6)=A_6)), inference(resolution, [status(thm)], [c_6, c_29])).
% 6.49/2.29  tff(c_434, plain, (![A_6, B_57]: (r1_tarski(A_6, k2_xboole_0(B_57, A_6)) | ~r1_tarski(k1_xboole_0, B_57))), inference(superposition, [status(thm), theory('equality')], [c_41, c_391])).
% 6.49/2.29  tff(c_449, plain, (![A_58, B_59]: (r1_tarski(A_58, k2_xboole_0(B_59, A_58)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_434])).
% 6.49/2.29  tff(c_762, plain, (![A_69]: (r1_tarski(k2_relat_1(A_69), k3_relat_1(A_69)) | ~v1_relat_1(A_69))), inference(superposition, [status(thm), theory('equality')], [c_14, c_449])).
% 6.49/2.29  tff(c_3921, plain, (![A_159]: (k2_xboole_0(k2_relat_1(A_159), k3_relat_1(A_159))=k3_relat_1(A_159) | ~v1_relat_1(A_159))), inference(resolution, [status(thm)], [c_762, c_4])).
% 6.49/2.29  tff(c_488, plain, (![A_1, B_59, B_2]: (r1_tarski(A_1, k2_xboole_0(B_59, k2_xboole_0(A_1, B_2))))), inference(resolution, [status(thm)], [c_449, c_2])).
% 6.49/2.29  tff(c_3988, plain, (![A_159, B_59]: (r1_tarski(k2_relat_1(A_159), k2_xboole_0(B_59, k3_relat_1(A_159))) | ~v1_relat_1(A_159))), inference(superposition, [status(thm), theory('equality')], [c_3921, c_488])).
% 6.49/2.29  tff(c_7788, plain, (r1_tarski(k2_relat_1('#skF_2'), k3_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_7769, c_3988])).
% 6.49/2.29  tff(c_7891, plain, (r1_tarski(k2_relat_1('#skF_2'), k3_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_7788])).
% 6.49/2.29  tff(c_7916, plain, (k2_xboole_0(k2_relat_1('#skF_2'), k3_relat_1('#skF_2'))=k3_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_7891, c_4])).
% 6.49/2.29  tff(c_445, plain, (![A_55, B_57, C_56]: (r1_tarski(A_55, k2_xboole_0(B_57, C_56)) | ~r1_tarski(A_55, B_57))), inference(resolution, [status(thm)], [c_391, c_2])).
% 6.49/2.29  tff(c_9262, plain, (![A_245]: (r1_tarski(A_245, k3_relat_1('#skF_2')) | ~r1_tarski(A_245, k2_relat_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_7916, c_445])).
% 6.49/2.29  tff(c_7764, plain, (~r1_tarski(k2_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_6719])).
% 6.49/2.29  tff(c_9312, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_9262, c_7764])).
% 6.49/2.29  tff(c_9323, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_16, c_9312])).
% 6.49/2.29  tff(c_9327, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_9323])).
% 6.49/2.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.49/2.29  
% 6.49/2.29  Inference rules
% 6.49/2.29  ----------------------
% 6.49/2.29  #Ref     : 0
% 6.49/2.29  #Sup     : 2227
% 6.49/2.29  #Fact    : 0
% 6.49/2.29  #Define  : 0
% 6.49/2.29  #Split   : 10
% 6.49/2.29  #Chain   : 0
% 6.49/2.29  #Close   : 0
% 6.49/2.29  
% 6.49/2.29  Ordering : KBO
% 6.49/2.29  
% 6.49/2.29  Simplification rules
% 6.49/2.29  ----------------------
% 6.49/2.29  #Subsume      : 367
% 6.49/2.29  #Demod        : 1259
% 6.49/2.29  #Tautology    : 1248
% 6.49/2.29  #SimpNegUnit  : 0
% 6.49/2.29  #BackRed      : 0
% 6.49/2.29  
% 6.49/2.29  #Partial instantiations: 0
% 6.49/2.29  #Strategies tried      : 1
% 6.49/2.29  
% 6.49/2.29  Timing (in seconds)
% 6.49/2.29  ----------------------
% 6.49/2.30  Preprocessing        : 0.28
% 6.49/2.30  Parsing              : 0.16
% 6.49/2.30  CNF conversion       : 0.02
% 6.49/2.30  Main loop            : 1.26
% 6.49/2.30  Inferencing          : 0.40
% 6.49/2.30  Reduction            : 0.48
% 6.49/2.30  Demodulation         : 0.38
% 6.49/2.30  BG Simplification    : 0.04
% 6.49/2.30  Subsumption          : 0.26
% 6.49/2.30  Abstraction          : 0.05
% 6.49/2.30  MUC search           : 0.00
% 6.49/2.30  Cooper               : 0.00
% 6.49/2.30  Total                : 1.57
% 6.49/2.30  Index Insertion      : 0.00
% 6.49/2.30  Index Deletion       : 0.00
% 6.49/2.30  Index Matching       : 0.00
% 6.49/2.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
