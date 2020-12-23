%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:56 EST 2020

% Result     : Theorem 7.47s
% Output     : CNFRefutation 7.47s
% Verified   : 
% Statistics : Number of formulae       :   52 (  76 expanded)
%              Number of leaves         :   18 (  33 expanded)
%              Depth                    :   13
%              Number of atoms          :  105 ( 178 expanded)
%              Number of equality atoms :    7 (   9 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k7_relat_1(C,A),k7_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k7_relat_1(B,A),k7_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(k7_relat_1(A_4,B_5))
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),k7_relat_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_11,A_10)),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_26,plain,(
    ! [A_23,C_24,B_25] :
      ( r1_tarski(A_23,C_24)
      | ~ r1_tarski(B_25,C_24)
      | ~ r1_tarski(A_23,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    ! [A_23] :
      ( r1_tarski(A_23,'#skF_2')
      | ~ r1_tarski(A_23,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_16,c_26])).

tff(c_98,plain,(
    ! [B_34,A_35] :
      ( k7_relat_1(B_34,A_35) = B_34
      | ~ r1_tarski(k1_relat_1(B_34),A_35)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_113,plain,(
    ! [B_36] :
      ( k7_relat_1(B_36,'#skF_2') = B_36
      | ~ v1_relat_1(B_36)
      | ~ r1_tarski(k1_relat_1(B_36),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_98])).

tff(c_369,plain,(
    ! [B_68] :
      ( k7_relat_1(k7_relat_1(B_68,'#skF_1'),'#skF_2') = k7_relat_1(B_68,'#skF_1')
      | ~ v1_relat_1(k7_relat_1(B_68,'#skF_1'))
      | ~ v1_relat_1(B_68) ) ),
    inference(resolution,[status(thm)],[c_8,c_113])).

tff(c_374,plain,(
    ! [A_4] :
      ( k7_relat_1(k7_relat_1(A_4,'#skF_1'),'#skF_2') = k7_relat_1(A_4,'#skF_1')
      | ~ v1_relat_1(A_4) ) ),
    inference(resolution,[status(thm)],[c_4,c_369])).

tff(c_541,plain,(
    ! [B_79,A_80] :
      ( k7_relat_1(k7_relat_1(B_79,A_80),A_80) = k7_relat_1(B_79,A_80)
      | ~ v1_relat_1(k7_relat_1(B_79,A_80))
      | ~ v1_relat_1(B_79) ) ),
    inference(resolution,[status(thm)],[c_8,c_98])).

tff(c_853,plain,(
    ! [A_92,B_93] :
      ( k7_relat_1(k7_relat_1(A_92,B_93),B_93) = k7_relat_1(A_92,B_93)
      | ~ v1_relat_1(A_92) ) ),
    inference(resolution,[status(thm)],[c_4,c_541])).

tff(c_10,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k7_relat_1(B_13,A_12),B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_958,plain,(
    ! [A_92,B_93] :
      ( r1_tarski(k7_relat_1(A_92,B_93),k7_relat_1(A_92,B_93))
      | ~ v1_relat_1(k7_relat_1(A_92,B_93))
      | ~ v1_relat_1(A_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_853,c_10])).

tff(c_20,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_18,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_39,plain,(
    ! [A_26] :
      ( r1_tarski(A_26,'#skF_4')
      | ~ r1_tarski(A_26,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_18,c_26])).

tff(c_47,plain,(
    ! [A_12] :
      ( r1_tarski(k7_relat_1('#skF_3',A_12),'#skF_4')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_10,c_39])).

tff(c_51,plain,(
    ! [A_12] : r1_tarski(k7_relat_1('#skF_3',A_12),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_47])).

tff(c_6,plain,(
    ! [B_7,A_6,C_9] :
      ( r1_tarski(k7_relat_1(B_7,A_6),k7_relat_1(C_9,A_6))
      | ~ r1_tarski(B_7,C_9)
      | ~ v1_relat_1(C_9)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_170,plain,(
    ! [B_49,A_50,C_51] :
      ( r1_tarski(k7_relat_1(B_49,A_50),k7_relat_1(C_51,A_50))
      | ~ r1_tarski(B_49,C_51)
      | ~ v1_relat_1(C_51)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_786,plain,(
    ! [A_87,C_88,A_89,B_90] :
      ( r1_tarski(A_87,k7_relat_1(C_88,A_89))
      | ~ r1_tarski(A_87,k7_relat_1(B_90,A_89))
      | ~ r1_tarski(B_90,C_88)
      | ~ v1_relat_1(C_88)
      | ~ v1_relat_1(B_90) ) ),
    inference(resolution,[status(thm)],[c_170,c_2])).

tff(c_1758,plain,(
    ! [B_125,A_126,C_127,C_128] :
      ( r1_tarski(k7_relat_1(B_125,A_126),k7_relat_1(C_127,A_126))
      | ~ r1_tarski(C_128,C_127)
      | ~ v1_relat_1(C_127)
      | ~ r1_tarski(B_125,C_128)
      | ~ v1_relat_1(C_128)
      | ~ v1_relat_1(B_125) ) ),
    inference(resolution,[status(thm)],[c_6,c_786])).

tff(c_1820,plain,(
    ! [B_125,A_126,A_12] :
      ( r1_tarski(k7_relat_1(B_125,A_126),k7_relat_1('#skF_4',A_126))
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski(B_125,k7_relat_1('#skF_3',A_12))
      | ~ v1_relat_1(k7_relat_1('#skF_3',A_12))
      | ~ v1_relat_1(B_125) ) ),
    inference(resolution,[status(thm)],[c_51,c_1758])).

tff(c_8184,plain,(
    ! [B_301,A_302,A_303] :
      ( r1_tarski(k7_relat_1(B_301,A_302),k7_relat_1('#skF_4',A_302))
      | ~ r1_tarski(B_301,k7_relat_1('#skF_3',A_303))
      | ~ v1_relat_1(k7_relat_1('#skF_3',A_303))
      | ~ v1_relat_1(B_301) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1820])).

tff(c_8223,plain,(
    ! [B_93,A_302] :
      ( r1_tarski(k7_relat_1(k7_relat_1('#skF_3',B_93),A_302),k7_relat_1('#skF_4',A_302))
      | ~ v1_relat_1(k7_relat_1('#skF_3',B_93))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_958,c_8184])).

tff(c_8551,plain,(
    ! [B_310,A_311] :
      ( r1_tarski(k7_relat_1(k7_relat_1('#skF_3',B_310),A_311),k7_relat_1('#skF_4',A_311))
      | ~ v1_relat_1(k7_relat_1('#skF_3',B_310)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_8223])).

tff(c_8612,plain,
    ( r1_tarski(k7_relat_1('#skF_3','#skF_1'),k7_relat_1('#skF_4','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_374,c_8551])).

tff(c_8657,plain,
    ( r1_tarski(k7_relat_1('#skF_3','#skF_1'),k7_relat_1('#skF_4','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_8612])).

tff(c_8658,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_8657])).

tff(c_8663,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_8658])).

tff(c_8667,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_8663])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:09:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.47/2.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.47/2.75  
% 7.47/2.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.47/2.76  %$ r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.47/2.76  
% 7.47/2.76  %Foreground sorts:
% 7.47/2.76  
% 7.47/2.76  
% 7.47/2.76  %Background operators:
% 7.47/2.76  
% 7.47/2.76  
% 7.47/2.76  %Foreground operators:
% 7.47/2.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.47/2.76  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.47/2.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.47/2.76  tff('#skF_2', type, '#skF_2': $i).
% 7.47/2.76  tff('#skF_3', type, '#skF_3': $i).
% 7.47/2.76  tff('#skF_1', type, '#skF_1': $i).
% 7.47/2.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.47/2.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.47/2.76  tff('#skF_4', type, '#skF_4': $i).
% 7.47/2.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.47/2.76  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.47/2.76  
% 7.47/2.77  tff(f_70, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k7_relat_1(C, A), k7_relat_1(D, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_relat_1)).
% 7.47/2.77  tff(f_35, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 7.47/2.77  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 7.47/2.77  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 7.47/2.77  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 7.47/2.77  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 7.47/2.77  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k7_relat_1(B, A), k7_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_relat_1)).
% 7.47/2.77  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.47/2.77  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k7_relat_1(A_4, B_5)) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.47/2.77  tff(c_14, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), k7_relat_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.47/2.77  tff(c_8, plain, (![B_11, A_10]: (r1_tarski(k1_relat_1(k7_relat_1(B_11, A_10)), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.47/2.77  tff(c_16, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.47/2.77  tff(c_26, plain, (![A_23, C_24, B_25]: (r1_tarski(A_23, C_24) | ~r1_tarski(B_25, C_24) | ~r1_tarski(A_23, B_25))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.47/2.77  tff(c_38, plain, (![A_23]: (r1_tarski(A_23, '#skF_2') | ~r1_tarski(A_23, '#skF_1'))), inference(resolution, [status(thm)], [c_16, c_26])).
% 7.47/2.77  tff(c_98, plain, (![B_34, A_35]: (k7_relat_1(B_34, A_35)=B_34 | ~r1_tarski(k1_relat_1(B_34), A_35) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.47/2.77  tff(c_113, plain, (![B_36]: (k7_relat_1(B_36, '#skF_2')=B_36 | ~v1_relat_1(B_36) | ~r1_tarski(k1_relat_1(B_36), '#skF_1'))), inference(resolution, [status(thm)], [c_38, c_98])).
% 7.47/2.77  tff(c_369, plain, (![B_68]: (k7_relat_1(k7_relat_1(B_68, '#skF_1'), '#skF_2')=k7_relat_1(B_68, '#skF_1') | ~v1_relat_1(k7_relat_1(B_68, '#skF_1')) | ~v1_relat_1(B_68))), inference(resolution, [status(thm)], [c_8, c_113])).
% 7.47/2.77  tff(c_374, plain, (![A_4]: (k7_relat_1(k7_relat_1(A_4, '#skF_1'), '#skF_2')=k7_relat_1(A_4, '#skF_1') | ~v1_relat_1(A_4))), inference(resolution, [status(thm)], [c_4, c_369])).
% 7.47/2.77  tff(c_541, plain, (![B_79, A_80]: (k7_relat_1(k7_relat_1(B_79, A_80), A_80)=k7_relat_1(B_79, A_80) | ~v1_relat_1(k7_relat_1(B_79, A_80)) | ~v1_relat_1(B_79))), inference(resolution, [status(thm)], [c_8, c_98])).
% 7.47/2.77  tff(c_853, plain, (![A_92, B_93]: (k7_relat_1(k7_relat_1(A_92, B_93), B_93)=k7_relat_1(A_92, B_93) | ~v1_relat_1(A_92))), inference(resolution, [status(thm)], [c_4, c_541])).
% 7.47/2.77  tff(c_10, plain, (![B_13, A_12]: (r1_tarski(k7_relat_1(B_13, A_12), B_13) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.47/2.77  tff(c_958, plain, (![A_92, B_93]: (r1_tarski(k7_relat_1(A_92, B_93), k7_relat_1(A_92, B_93)) | ~v1_relat_1(k7_relat_1(A_92, B_93)) | ~v1_relat_1(A_92))), inference(superposition, [status(thm), theory('equality')], [c_853, c_10])).
% 7.47/2.77  tff(c_20, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.47/2.77  tff(c_18, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.47/2.77  tff(c_39, plain, (![A_26]: (r1_tarski(A_26, '#skF_4') | ~r1_tarski(A_26, '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_26])).
% 7.47/2.77  tff(c_47, plain, (![A_12]: (r1_tarski(k7_relat_1('#skF_3', A_12), '#skF_4') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_10, c_39])).
% 7.47/2.77  tff(c_51, plain, (![A_12]: (r1_tarski(k7_relat_1('#skF_3', A_12), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_47])).
% 7.47/2.77  tff(c_6, plain, (![B_7, A_6, C_9]: (r1_tarski(k7_relat_1(B_7, A_6), k7_relat_1(C_9, A_6)) | ~r1_tarski(B_7, C_9) | ~v1_relat_1(C_9) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.47/2.77  tff(c_170, plain, (![B_49, A_50, C_51]: (r1_tarski(k7_relat_1(B_49, A_50), k7_relat_1(C_51, A_50)) | ~r1_tarski(B_49, C_51) | ~v1_relat_1(C_51) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.47/2.77  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.47/2.77  tff(c_786, plain, (![A_87, C_88, A_89, B_90]: (r1_tarski(A_87, k7_relat_1(C_88, A_89)) | ~r1_tarski(A_87, k7_relat_1(B_90, A_89)) | ~r1_tarski(B_90, C_88) | ~v1_relat_1(C_88) | ~v1_relat_1(B_90))), inference(resolution, [status(thm)], [c_170, c_2])).
% 7.47/2.77  tff(c_1758, plain, (![B_125, A_126, C_127, C_128]: (r1_tarski(k7_relat_1(B_125, A_126), k7_relat_1(C_127, A_126)) | ~r1_tarski(C_128, C_127) | ~v1_relat_1(C_127) | ~r1_tarski(B_125, C_128) | ~v1_relat_1(C_128) | ~v1_relat_1(B_125))), inference(resolution, [status(thm)], [c_6, c_786])).
% 7.47/2.77  tff(c_1820, plain, (![B_125, A_126, A_12]: (r1_tarski(k7_relat_1(B_125, A_126), k7_relat_1('#skF_4', A_126)) | ~v1_relat_1('#skF_4') | ~r1_tarski(B_125, k7_relat_1('#skF_3', A_12)) | ~v1_relat_1(k7_relat_1('#skF_3', A_12)) | ~v1_relat_1(B_125))), inference(resolution, [status(thm)], [c_51, c_1758])).
% 7.47/2.77  tff(c_8184, plain, (![B_301, A_302, A_303]: (r1_tarski(k7_relat_1(B_301, A_302), k7_relat_1('#skF_4', A_302)) | ~r1_tarski(B_301, k7_relat_1('#skF_3', A_303)) | ~v1_relat_1(k7_relat_1('#skF_3', A_303)) | ~v1_relat_1(B_301))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1820])).
% 7.47/2.77  tff(c_8223, plain, (![B_93, A_302]: (r1_tarski(k7_relat_1(k7_relat_1('#skF_3', B_93), A_302), k7_relat_1('#skF_4', A_302)) | ~v1_relat_1(k7_relat_1('#skF_3', B_93)) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_958, c_8184])).
% 7.47/2.77  tff(c_8551, plain, (![B_310, A_311]: (r1_tarski(k7_relat_1(k7_relat_1('#skF_3', B_310), A_311), k7_relat_1('#skF_4', A_311)) | ~v1_relat_1(k7_relat_1('#skF_3', B_310)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_8223])).
% 7.47/2.77  tff(c_8612, plain, (r1_tarski(k7_relat_1('#skF_3', '#skF_1'), k7_relat_1('#skF_4', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_374, c_8551])).
% 7.47/2.77  tff(c_8657, plain, (r1_tarski(k7_relat_1('#skF_3', '#skF_1'), k7_relat_1('#skF_4', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_8612])).
% 7.47/2.77  tff(c_8658, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_14, c_8657])).
% 7.47/2.77  tff(c_8663, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4, c_8658])).
% 7.47/2.77  tff(c_8667, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_8663])).
% 7.47/2.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.47/2.77  
% 7.47/2.77  Inference rules
% 7.47/2.77  ----------------------
% 7.47/2.77  #Ref     : 0
% 7.47/2.77  #Sup     : 1938
% 7.47/2.77  #Fact    : 0
% 7.47/2.77  #Define  : 0
% 7.47/2.77  #Split   : 12
% 7.47/2.77  #Chain   : 0
% 7.47/2.77  #Close   : 0
% 7.47/2.77  
% 7.47/2.77  Ordering : KBO
% 7.47/2.77  
% 7.47/2.77  Simplification rules
% 7.47/2.77  ----------------------
% 7.47/2.77  #Subsume      : 692
% 7.47/2.77  #Demod        : 826
% 7.47/2.77  #Tautology    : 240
% 7.47/2.77  #SimpNegUnit  : 1
% 7.47/2.77  #BackRed      : 0
% 7.47/2.77  
% 7.47/2.77  #Partial instantiations: 0
% 7.47/2.77  #Strategies tried      : 1
% 7.47/2.77  
% 7.47/2.77  Timing (in seconds)
% 7.47/2.77  ----------------------
% 7.47/2.77  Preprocessing        : 0.30
% 7.47/2.77  Parsing              : 0.17
% 7.47/2.77  CNF conversion       : 0.02
% 7.47/2.77  Main loop            : 1.65
% 7.47/2.77  Inferencing          : 0.48
% 7.47/2.77  Reduction            : 0.44
% 7.47/2.77  Demodulation         : 0.30
% 7.47/2.77  BG Simplification    : 0.05
% 7.47/2.77  Subsumption          : 0.57
% 7.47/2.77  Abstraction          : 0.08
% 7.47/2.77  MUC search           : 0.00
% 7.47/2.77  Cooper               : 0.00
% 7.47/2.77  Total                : 1.98
% 7.47/2.77  Index Insertion      : 0.00
% 7.47/2.77  Index Deletion       : 0.00
% 7.47/2.77  Index Matching       : 0.00
% 7.47/2.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
