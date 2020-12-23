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
% DateTime   : Thu Dec  3 10:01:55 EST 2020

% Result     : Theorem 17.85s
% Output     : CNFRefutation 17.92s
% Verified   : 
% Statistics : Number of formulae       :   47 (  58 expanded)
%              Number of leaves         :   21 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   77 ( 119 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k10_relat_1(C,A),k10_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t180_relat_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k10_relat_1(B,A),k10_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t179_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_12,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_39,plain,(
    ! [A_26,B_27] : r1_tarski(k4_xboole_0(A_26,B_27),A_26) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_42,plain,(
    ! [A_12] : r1_tarski(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_39])).

tff(c_26,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_24,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_18,plain,(
    ! [B_19,A_18,C_21] :
      ( r1_tarski(k10_relat_1(B_19,A_18),k10_relat_1(C_21,A_18))
      | ~ r1_tarski(B_19,C_21)
      | ~ v1_relat_1(C_21)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_573,plain,(
    ! [B_59,A_60,C_61] :
      ( r1_tarski(k10_relat_1(B_59,A_60),k10_relat_1(C_61,A_60))
      | ~ r1_tarski(B_59,C_61)
      | ~ v1_relat_1(C_61)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(B_6,C_7)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3110,plain,(
    ! [A_137,C_138,A_139,B_140] :
      ( r1_tarski(A_137,k10_relat_1(C_138,A_139))
      | ~ r1_tarski(A_137,k10_relat_1(B_140,A_139))
      | ~ r1_tarski(B_140,C_138)
      | ~ v1_relat_1(C_138)
      | ~ v1_relat_1(B_140) ) ),
    inference(resolution,[status(thm)],[c_573,c_6])).

tff(c_15867,plain,(
    ! [B_325,A_326,C_327,C_328] :
      ( r1_tarski(k10_relat_1(B_325,A_326),k10_relat_1(C_327,A_326))
      | ~ r1_tarski(C_328,C_327)
      | ~ v1_relat_1(C_327)
      | ~ r1_tarski(B_325,C_328)
      | ~ v1_relat_1(C_328)
      | ~ v1_relat_1(B_325) ) ),
    inference(resolution,[status(thm)],[c_18,c_3110])).

tff(c_15989,plain,(
    ! [B_325,A_326] :
      ( r1_tarski(k10_relat_1(B_325,A_326),k10_relat_1('#skF_4',A_326))
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski(B_325,'#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(B_325) ) ),
    inference(resolution,[status(thm)],[c_24,c_15867])).

tff(c_16074,plain,(
    ! [B_325,A_326] :
      ( r1_tarski(k10_relat_1(B_325,A_326),k10_relat_1('#skF_4',A_326))
      | ~ r1_tarski(B_325,'#skF_3')
      | ~ v1_relat_1(B_325) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_15989])).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_93,plain,(
    ! [A_33,B_34] :
      ( k2_xboole_0(A_33,B_34) = B_34
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_117,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_22,c_93])).

tff(c_443,plain,(
    ! [C_53,A_54,B_55] :
      ( k2_xboole_0(k10_relat_1(C_53,A_54),k10_relat_1(C_53,B_55)) = k10_relat_1(C_53,k2_xboole_0(A_54,B_55))
      | ~ v1_relat_1(C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1066,plain,(
    ! [C_84,A_85,B_86] :
      ( r1_tarski(k10_relat_1(C_84,A_85),k10_relat_1(C_84,k2_xboole_0(A_85,B_86)))
      | ~ v1_relat_1(C_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_443,c_14])).

tff(c_6840,plain,(
    ! [A_211,C_212,A_213,B_214] :
      ( r1_tarski(A_211,k10_relat_1(C_212,k2_xboole_0(A_213,B_214)))
      | ~ r1_tarski(A_211,k10_relat_1(C_212,A_213))
      | ~ v1_relat_1(C_212) ) ),
    inference(resolution,[status(thm)],[c_1066,c_6])).

tff(c_28912,plain,(
    ! [A_462,C_463] :
      ( r1_tarski(A_462,k10_relat_1(C_463,'#skF_2'))
      | ~ r1_tarski(A_462,k10_relat_1(C_463,'#skF_1'))
      | ~ v1_relat_1(C_463) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_6840])).

tff(c_20,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_28962,plain,
    ( ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_4','#skF_1'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28912,c_20])).

tff(c_28982,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28962])).

tff(c_28985,plain,
    ( ~ r1_tarski('#skF_3','#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16074,c_28982])).

tff(c_28992,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_42,c_28985])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 20:04:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.85/8.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.85/8.34  
% 17.85/8.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.92/8.34  %$ r1_tarski > v1_relat_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 17.92/8.34  
% 17.92/8.34  %Foreground sorts:
% 17.92/8.34  
% 17.92/8.34  
% 17.92/8.34  %Background operators:
% 17.92/8.34  
% 17.92/8.34  
% 17.92/8.34  %Foreground operators:
% 17.92/8.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.92/8.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 17.92/8.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.92/8.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.92/8.34  tff('#skF_2', type, '#skF_2': $i).
% 17.92/8.34  tff('#skF_3', type, '#skF_3': $i).
% 17.92/8.34  tff('#skF_1', type, '#skF_1': $i).
% 17.92/8.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.92/8.34  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 17.92/8.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 17.92/8.34  tff('#skF_4', type, '#skF_4': $i).
% 17.92/8.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.92/8.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 17.92/8.34  
% 17.92/8.35  tff(f_70, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k10_relat_1(C, A), k10_relat_1(D, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t180_relat_1)).
% 17.92/8.35  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 17.92/8.35  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 17.92/8.35  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k10_relat_1(B, A), k10_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t179_relat_1)).
% 17.92/8.35  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 17.92/8.35  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 17.92/8.35  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 17.92/8.35  tff(f_45, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 17.92/8.35  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 17.92/8.35  tff(c_12, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_43])).
% 17.92/8.35  tff(c_39, plain, (![A_26, B_27]: (r1_tarski(k4_xboole_0(A_26, B_27), A_26))), inference(cnfTransformation, [status(thm)], [f_39])).
% 17.92/8.35  tff(c_42, plain, (![A_12]: (r1_tarski(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_12, c_39])).
% 17.92/8.35  tff(c_26, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 17.92/8.35  tff(c_24, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 17.92/8.35  tff(c_18, plain, (![B_19, A_18, C_21]: (r1_tarski(k10_relat_1(B_19, A_18), k10_relat_1(C_21, A_18)) | ~r1_tarski(B_19, C_21) | ~v1_relat_1(C_21) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_58])).
% 17.92/8.35  tff(c_573, plain, (![B_59, A_60, C_61]: (r1_tarski(k10_relat_1(B_59, A_60), k10_relat_1(C_61, A_60)) | ~r1_tarski(B_59, C_61) | ~v1_relat_1(C_61) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_58])).
% 17.92/8.35  tff(c_6, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(B_6, C_7) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 17.92/8.35  tff(c_3110, plain, (![A_137, C_138, A_139, B_140]: (r1_tarski(A_137, k10_relat_1(C_138, A_139)) | ~r1_tarski(A_137, k10_relat_1(B_140, A_139)) | ~r1_tarski(B_140, C_138) | ~v1_relat_1(C_138) | ~v1_relat_1(B_140))), inference(resolution, [status(thm)], [c_573, c_6])).
% 17.92/8.35  tff(c_15867, plain, (![B_325, A_326, C_327, C_328]: (r1_tarski(k10_relat_1(B_325, A_326), k10_relat_1(C_327, A_326)) | ~r1_tarski(C_328, C_327) | ~v1_relat_1(C_327) | ~r1_tarski(B_325, C_328) | ~v1_relat_1(C_328) | ~v1_relat_1(B_325))), inference(resolution, [status(thm)], [c_18, c_3110])).
% 17.92/8.35  tff(c_15989, plain, (![B_325, A_326]: (r1_tarski(k10_relat_1(B_325, A_326), k10_relat_1('#skF_4', A_326)) | ~v1_relat_1('#skF_4') | ~r1_tarski(B_325, '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(B_325))), inference(resolution, [status(thm)], [c_24, c_15867])).
% 17.92/8.35  tff(c_16074, plain, (![B_325, A_326]: (r1_tarski(k10_relat_1(B_325, A_326), k10_relat_1('#skF_4', A_326)) | ~r1_tarski(B_325, '#skF_3') | ~v1_relat_1(B_325))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_15989])).
% 17.92/8.35  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 17.92/8.35  tff(c_93, plain, (![A_33, B_34]: (k2_xboole_0(A_33, B_34)=B_34 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_31])).
% 17.92/8.35  tff(c_117, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_22, c_93])).
% 17.92/8.35  tff(c_443, plain, (![C_53, A_54, B_55]: (k2_xboole_0(k10_relat_1(C_53, A_54), k10_relat_1(C_53, B_55))=k10_relat_1(C_53, k2_xboole_0(A_54, B_55)) | ~v1_relat_1(C_53))), inference(cnfTransformation, [status(thm)], [f_49])).
% 17.92/8.35  tff(c_14, plain, (![A_13, B_14]: (r1_tarski(A_13, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 17.92/8.35  tff(c_1066, plain, (![C_84, A_85, B_86]: (r1_tarski(k10_relat_1(C_84, A_85), k10_relat_1(C_84, k2_xboole_0(A_85, B_86))) | ~v1_relat_1(C_84))), inference(superposition, [status(thm), theory('equality')], [c_443, c_14])).
% 17.92/8.35  tff(c_6840, plain, (![A_211, C_212, A_213, B_214]: (r1_tarski(A_211, k10_relat_1(C_212, k2_xboole_0(A_213, B_214))) | ~r1_tarski(A_211, k10_relat_1(C_212, A_213)) | ~v1_relat_1(C_212))), inference(resolution, [status(thm)], [c_1066, c_6])).
% 17.92/8.35  tff(c_28912, plain, (![A_462, C_463]: (r1_tarski(A_462, k10_relat_1(C_463, '#skF_2')) | ~r1_tarski(A_462, k10_relat_1(C_463, '#skF_1')) | ~v1_relat_1(C_463))), inference(superposition, [status(thm), theory('equality')], [c_117, c_6840])).
% 17.92/8.35  tff(c_20, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 17.92/8.35  tff(c_28962, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_4', '#skF_1')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28912, c_20])).
% 17.92/8.35  tff(c_28982, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28962])).
% 17.92/8.35  tff(c_28985, plain, (~r1_tarski('#skF_3', '#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16074, c_28982])).
% 17.92/8.35  tff(c_28992, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_42, c_28985])).
% 17.92/8.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.92/8.35  
% 17.92/8.35  Inference rules
% 17.92/8.35  ----------------------
% 17.92/8.35  #Ref     : 0
% 17.92/8.35  #Sup     : 7563
% 17.92/8.35  #Fact    : 0
% 17.92/8.35  #Define  : 0
% 17.92/8.35  #Split   : 9
% 17.92/8.35  #Chain   : 0
% 17.92/8.35  #Close   : 0
% 17.92/8.35  
% 17.92/8.35  Ordering : KBO
% 17.92/8.36  
% 17.92/8.36  Simplification rules
% 17.92/8.36  ----------------------
% 17.92/8.36  #Subsume      : 1449
% 17.92/8.36  #Demod        : 6486
% 17.92/8.36  #Tautology    : 3573
% 17.92/8.36  #SimpNegUnit  : 0
% 17.92/8.36  #BackRed      : 0
% 17.92/8.36  
% 17.92/8.36  #Partial instantiations: 0
% 17.92/8.36  #Strategies tried      : 1
% 17.92/8.36  
% 17.92/8.36  Timing (in seconds)
% 17.92/8.36  ----------------------
% 17.92/8.36  Preprocessing        : 0.43
% 17.92/8.36  Parsing              : 0.23
% 17.92/8.36  CNF conversion       : 0.03
% 17.92/8.36  Main loop            : 7.02
% 17.92/8.36  Inferencing          : 1.23
% 17.92/8.36  Reduction            : 3.72
% 17.92/8.36  Demodulation         : 3.25
% 17.92/8.36  BG Simplification    : 0.15
% 17.92/8.36  Subsumption          : 1.55
% 17.92/8.36  Abstraction          : 0.21
% 17.92/8.36  MUC search           : 0.00
% 17.92/8.36  Cooper               : 0.00
% 17.92/8.36  Total                : 7.49
% 17.92/8.36  Index Insertion      : 0.00
% 17.92/8.36  Index Deletion       : 0.00
% 17.92/8.36  Index Matching       : 0.00
% 17.92/8.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
