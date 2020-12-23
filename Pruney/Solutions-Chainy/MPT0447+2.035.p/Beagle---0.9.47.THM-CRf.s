%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:32 EST 2020

% Result     : Theorem 6.79s
% Output     : CNFRefutation 7.05s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 112 expanded)
%              Number of leaves         :   21 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :  104 ( 222 expanded)
%              Number of equality atoms :   16 (  32 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_79,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k2_relat_1(A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k1_relat_1(A),k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_30,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_26,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [A_13,C_15,B_14] :
      ( r1_tarski(k2_xboole_0(A_13,C_15),B_14)
      | ~ r1_tarski(C_15,B_14)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_83,plain,(
    ! [B_31,A_32] :
      ( B_31 = A_32
      | ~ r1_tarski(B_31,A_32)
      | ~ r1_tarski(A_32,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_284,plain,(
    ! [A_56,B_57] :
      ( k2_xboole_0(A_56,B_57) = A_56
      | ~ r1_tarski(k2_xboole_0(A_56,B_57),A_56) ) ),
    inference(resolution,[status(thm)],[c_14,c_83])).

tff(c_288,plain,(
    ! [B_14,C_15] :
      ( k2_xboole_0(B_14,C_15) = B_14
      | ~ r1_tarski(C_15,B_14)
      | ~ r1_tarski(B_14,B_14) ) ),
    inference(resolution,[status(thm)],[c_16,c_284])).

tff(c_316,plain,(
    ! [B_58,C_59] :
      ( k2_xboole_0(B_58,C_59) = B_58
      | ~ r1_tarski(C_59,B_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_288])).

tff(c_358,plain,(
    k2_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_26,c_316])).

tff(c_396,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_358])).

tff(c_478,plain,(
    ! [A_61,B_62] :
      ( k2_xboole_0(k2_relat_1(A_61),k2_relat_1(B_62)) = k2_relat_1(k2_xboole_0(A_61,B_62))
      | ~ v1_relat_1(B_62)
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2239,plain,(
    ! [A_98,B_99] :
      ( r1_tarski(k2_relat_1(A_98),k2_relat_1(k2_xboole_0(A_98,B_99)))
      | ~ v1_relat_1(B_99)
      | ~ v1_relat_1(A_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_478,c_14])).

tff(c_2286,plain,
    ( r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_396,c_2239])).

tff(c_2312,plain,(
    r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_2286])).

tff(c_171,plain,(
    ! [A_44] :
      ( k2_xboole_0(k1_relat_1(A_44),k2_relat_1(A_44)) = k3_relat_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,k2_xboole_0(C_7,B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_180,plain,(
    ! [A_5,A_44] :
      ( r1_tarski(A_5,k3_relat_1(A_44))
      | ~ r1_tarski(A_5,k2_relat_1(A_44))
      | ~ v1_relat_1(A_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_10])).

tff(c_955,plain,(
    ! [A_73,B_74] :
      ( k2_xboole_0(k1_relat_1(A_73),k1_relat_1(B_74)) = k1_relat_1(k2_xboole_0(A_73,B_74))
      | ~ v1_relat_1(B_74)
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1719,plain,(
    ! [A_87,B_88] :
      ( r1_tarski(k1_relat_1(A_87),k1_relat_1(k2_xboole_0(A_87,B_88)))
      | ~ v1_relat_1(B_88)
      | ~ v1_relat_1(A_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_955,c_14])).

tff(c_1758,plain,
    ( r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_396,c_1719])).

tff(c_1782,plain,(
    r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_1758])).

tff(c_215,plain,(
    ! [A_47] :
      ( r1_tarski(k1_relat_1(A_47),k3_relat_1(A_47))
      | ~ v1_relat_1(A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_14])).

tff(c_12,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_tarski(A_8,C_10)
      | ~ r1_tarski(B_9,C_10)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_7695,plain,(
    ! [A_171,A_172] :
      ( r1_tarski(A_171,k3_relat_1(A_172))
      | ~ r1_tarski(A_171,k1_relat_1(A_172))
      | ~ v1_relat_1(A_172) ) ),
    inference(resolution,[status(thm)],[c_215,c_12])).

tff(c_18,plain,(
    ! [A_16] :
      ( k2_xboole_0(k1_relat_1(A_16),k2_relat_1(A_16)) = k3_relat_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_255,plain,(
    ! [A_53,C_54,B_55] :
      ( r1_tarski(k2_xboole_0(A_53,C_54),B_55)
      | ~ r1_tarski(C_54,B_55)
      | ~ r1_tarski(A_53,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_5130,plain,(
    ! [A_132,B_133] :
      ( r1_tarski(k3_relat_1(A_132),B_133)
      | ~ r1_tarski(k2_relat_1(A_132),B_133)
      | ~ r1_tarski(k1_relat_1(A_132),B_133)
      | ~ v1_relat_1(A_132) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_255])).

tff(c_24,plain,(
    ~ r1_tarski(k3_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_5157,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k3_relat_1('#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k3_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_5130,c_24])).

tff(c_5173,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k3_relat_1('#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_5157])).

tff(c_5178,plain,(
    ~ r1_tarski(k1_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_5173])).

tff(c_7720,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_7695,c_5178])).

tff(c_7759,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1782,c_7720])).

tff(c_7760,plain,(
    ~ r1_tarski(k2_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_5173])).

tff(c_7764,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_180,c_7760])).

tff(c_7768,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2312,c_7764])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n020.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 15:16:07 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.79/2.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.79/2.59  
% 6.79/2.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.79/2.59  %$ r1_tarski > v1_relat_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 6.79/2.59  
% 6.79/2.59  %Foreground sorts:
% 6.79/2.59  
% 6.79/2.59  
% 6.79/2.59  %Background operators:
% 6.79/2.59  
% 6.79/2.59  
% 6.79/2.59  %Foreground operators:
% 6.79/2.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.79/2.59  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 6.79/2.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.79/2.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.79/2.59  tff('#skF_2', type, '#skF_2': $i).
% 6.79/2.59  tff('#skF_1', type, '#skF_1': $i).
% 6.79/2.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.79/2.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.79/2.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.79/2.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.79/2.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.79/2.59  
% 7.05/2.60  tff(f_79, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 7.05/2.60  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 7.05/2.60  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.05/2.60  tff(f_51, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 7.05/2.60  tff(f_45, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.05/2.60  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_relat_1)).
% 7.05/2.60  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 7.05/2.60  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 7.05/2.60  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relat_1)).
% 7.05/2.60  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 7.05/2.60  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.05/2.60  tff(c_30, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.05/2.60  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.05/2.60  tff(c_26, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.05/2.60  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.05/2.60  tff(c_16, plain, (![A_13, C_15, B_14]: (r1_tarski(k2_xboole_0(A_13, C_15), B_14) | ~r1_tarski(C_15, B_14) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.05/2.60  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.05/2.60  tff(c_83, plain, (![B_31, A_32]: (B_31=A_32 | ~r1_tarski(B_31, A_32) | ~r1_tarski(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.05/2.60  tff(c_284, plain, (![A_56, B_57]: (k2_xboole_0(A_56, B_57)=A_56 | ~r1_tarski(k2_xboole_0(A_56, B_57), A_56))), inference(resolution, [status(thm)], [c_14, c_83])).
% 7.05/2.60  tff(c_288, plain, (![B_14, C_15]: (k2_xboole_0(B_14, C_15)=B_14 | ~r1_tarski(C_15, B_14) | ~r1_tarski(B_14, B_14))), inference(resolution, [status(thm)], [c_16, c_284])).
% 7.05/2.60  tff(c_316, plain, (![B_58, C_59]: (k2_xboole_0(B_58, C_59)=B_58 | ~r1_tarski(C_59, B_58))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_288])).
% 7.05/2.60  tff(c_358, plain, (k2_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_26, c_316])).
% 7.05/2.60  tff(c_396, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_2, c_358])).
% 7.05/2.60  tff(c_478, plain, (![A_61, B_62]: (k2_xboole_0(k2_relat_1(A_61), k2_relat_1(B_62))=k2_relat_1(k2_xboole_0(A_61, B_62)) | ~v1_relat_1(B_62) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.05/2.60  tff(c_2239, plain, (![A_98, B_99]: (r1_tarski(k2_relat_1(A_98), k2_relat_1(k2_xboole_0(A_98, B_99))) | ~v1_relat_1(B_99) | ~v1_relat_1(A_98))), inference(superposition, [status(thm), theory('equality')], [c_478, c_14])).
% 7.05/2.60  tff(c_2286, plain, (r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_2')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_396, c_2239])).
% 7.05/2.60  tff(c_2312, plain, (r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_2286])).
% 7.05/2.60  tff(c_171, plain, (![A_44]: (k2_xboole_0(k1_relat_1(A_44), k2_relat_1(A_44))=k3_relat_1(A_44) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.05/2.60  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, k2_xboole_0(C_7, B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.05/2.60  tff(c_180, plain, (![A_5, A_44]: (r1_tarski(A_5, k3_relat_1(A_44)) | ~r1_tarski(A_5, k2_relat_1(A_44)) | ~v1_relat_1(A_44))), inference(superposition, [status(thm), theory('equality')], [c_171, c_10])).
% 7.05/2.60  tff(c_955, plain, (![A_73, B_74]: (k2_xboole_0(k1_relat_1(A_73), k1_relat_1(B_74))=k1_relat_1(k2_xboole_0(A_73, B_74)) | ~v1_relat_1(B_74) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.05/2.60  tff(c_1719, plain, (![A_87, B_88]: (r1_tarski(k1_relat_1(A_87), k1_relat_1(k2_xboole_0(A_87, B_88))) | ~v1_relat_1(B_88) | ~v1_relat_1(A_87))), inference(superposition, [status(thm), theory('equality')], [c_955, c_14])).
% 7.05/2.60  tff(c_1758, plain, (r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_396, c_1719])).
% 7.05/2.60  tff(c_1782, plain, (r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_1758])).
% 7.05/2.60  tff(c_215, plain, (![A_47]: (r1_tarski(k1_relat_1(A_47), k3_relat_1(A_47)) | ~v1_relat_1(A_47))), inference(superposition, [status(thm), theory('equality')], [c_171, c_14])).
% 7.05/2.60  tff(c_12, plain, (![A_8, C_10, B_9]: (r1_tarski(A_8, C_10) | ~r1_tarski(B_9, C_10) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.05/2.60  tff(c_7695, plain, (![A_171, A_172]: (r1_tarski(A_171, k3_relat_1(A_172)) | ~r1_tarski(A_171, k1_relat_1(A_172)) | ~v1_relat_1(A_172))), inference(resolution, [status(thm)], [c_215, c_12])).
% 7.05/2.60  tff(c_18, plain, (![A_16]: (k2_xboole_0(k1_relat_1(A_16), k2_relat_1(A_16))=k3_relat_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.05/2.60  tff(c_255, plain, (![A_53, C_54, B_55]: (r1_tarski(k2_xboole_0(A_53, C_54), B_55) | ~r1_tarski(C_54, B_55) | ~r1_tarski(A_53, B_55))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.05/2.60  tff(c_5130, plain, (![A_132, B_133]: (r1_tarski(k3_relat_1(A_132), B_133) | ~r1_tarski(k2_relat_1(A_132), B_133) | ~r1_tarski(k1_relat_1(A_132), B_133) | ~v1_relat_1(A_132))), inference(superposition, [status(thm), theory('equality')], [c_18, c_255])).
% 7.05/2.60  tff(c_24, plain, (~r1_tarski(k3_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.05/2.60  tff(c_5157, plain, (~r1_tarski(k2_relat_1('#skF_1'), k3_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1('#skF_1'), k3_relat_1('#skF_2')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_5130, c_24])).
% 7.05/2.60  tff(c_5173, plain, (~r1_tarski(k2_relat_1('#skF_1'), k3_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_5157])).
% 7.05/2.60  tff(c_5178, plain, (~r1_tarski(k1_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_5173])).
% 7.05/2.60  tff(c_7720, plain, (~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_7695, c_5178])).
% 7.05/2.60  tff(c_7759, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_1782, c_7720])).
% 7.05/2.60  tff(c_7760, plain, (~r1_tarski(k2_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_5173])).
% 7.05/2.60  tff(c_7764, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_180, c_7760])).
% 7.05/2.60  tff(c_7768, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_2312, c_7764])).
% 7.05/2.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.05/2.60  
% 7.05/2.60  Inference rules
% 7.05/2.60  ----------------------
% 7.05/2.60  #Ref     : 0
% 7.05/2.60  #Sup     : 1948
% 7.05/2.60  #Fact    : 0
% 7.05/2.60  #Define  : 0
% 7.05/2.60  #Split   : 8
% 7.05/2.60  #Chain   : 0
% 7.05/2.60  #Close   : 0
% 7.05/2.60  
% 7.05/2.60  Ordering : KBO
% 7.05/2.60  
% 7.05/2.60  Simplification rules
% 7.05/2.60  ----------------------
% 7.05/2.60  #Subsume      : 463
% 7.05/2.60  #Demod        : 1561
% 7.05/2.60  #Tautology    : 739
% 7.05/2.60  #SimpNegUnit  : 0
% 7.05/2.60  #BackRed      : 0
% 7.05/2.60  
% 7.05/2.60  #Partial instantiations: 0
% 7.05/2.60  #Strategies tried      : 1
% 7.05/2.60  
% 7.05/2.60  Timing (in seconds)
% 7.05/2.60  ----------------------
% 7.05/2.61  Preprocessing        : 0.39
% 7.05/2.61  Parsing              : 0.23
% 7.05/2.61  CNF conversion       : 0.02
% 7.05/2.61  Main loop            : 1.46
% 7.05/2.61  Inferencing          : 0.36
% 7.05/2.61  Reduction            : 0.64
% 7.05/2.61  Demodulation         : 0.52
% 7.05/2.61  BG Simplification    : 0.05
% 7.05/2.61  Subsumption          : 0.33
% 7.05/2.61  Abstraction          : 0.07
% 7.05/2.61  MUC search           : 0.00
% 7.05/2.61  Cooper               : 0.00
% 7.05/2.61  Total                : 1.90
% 7.05/2.61  Index Insertion      : 0.00
% 7.05/2.61  Index Deletion       : 0.00
% 7.05/2.61  Index Matching       : 0.00
% 7.05/2.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
