%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:58 EST 2020

% Result     : Theorem 7.75s
% Output     : CNFRefutation 7.75s
% Verified   : 
% Statistics : Number of formulae       :   54 (  76 expanded)
%              Number of leaves         :   26 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   73 ( 115 expanded)
%              Number of equality atoms :    7 (  14 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k7_relat_1(B,A)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_20,plain,(
    ! [A_20,B_21] :
      ( v1_relat_1(k7_relat_1(A_20,B_21))
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_26,plain,(
    ! [B_29,A_28] :
      ( k2_relat_1(k7_relat_1(B_29,A_28)) = k9_relat_1(B_29,A_28)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_202,plain,(
    ! [C_77,A_78,B_79] :
      ( k7_relat_1(k7_relat_1(C_77,A_78),B_79) = k7_relat_1(C_77,k3_xboole_0(A_78,B_79))
      | ~ v1_relat_1(C_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_32,plain,(
    ! [B_34,A_33] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_34,A_33)),k2_relat_1(B_34))
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_3544,plain,(
    ! [C_278,A_279,B_280] :
      ( r1_tarski(k2_relat_1(k7_relat_1(C_278,k3_xboole_0(A_279,B_280))),k2_relat_1(k7_relat_1(C_278,A_279)))
      | ~ v1_relat_1(k7_relat_1(C_278,A_279))
      | ~ v1_relat_1(C_278) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_32])).

tff(c_3684,plain,(
    ! [C_287,B_288,A_289] :
      ( r1_tarski(k2_relat_1(k7_relat_1(C_287,k3_xboole_0(B_288,A_289))),k2_relat_1(k7_relat_1(C_287,A_289)))
      | ~ v1_relat_1(k7_relat_1(C_287,A_289))
      | ~ v1_relat_1(C_287) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3544])).

tff(c_4327,plain,(
    ! [B_341,B_342,A_343] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_341,k3_xboole_0(B_342,A_343))),k9_relat_1(B_341,A_343))
      | ~ v1_relat_1(k7_relat_1(B_341,A_343))
      | ~ v1_relat_1(B_341)
      | ~ v1_relat_1(B_341) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_3684])).

tff(c_6923,plain,(
    ! [B_451,B_452,A_453] :
      ( r1_tarski(k9_relat_1(B_451,k3_xboole_0(B_452,A_453)),k9_relat_1(B_451,A_453))
      | ~ v1_relat_1(k7_relat_1(B_451,A_453))
      | ~ v1_relat_1(B_451)
      | ~ v1_relat_1(B_451)
      | ~ v1_relat_1(B_451) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_4327])).

tff(c_22,plain,(
    ! [C_24,A_22,B_23] :
      ( k7_relat_1(k7_relat_1(C_24,A_22),B_23) = k7_relat_1(C_24,k3_xboole_0(A_22,B_23))
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_149,plain,(
    ! [B_61,A_62] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_61,A_62)),k2_relat_1(B_61))
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_556,plain,(
    ! [B_104,A_105,A_106] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(B_104,A_105),A_106)),k9_relat_1(B_104,A_105))
      | ~ v1_relat_1(k7_relat_1(B_104,A_105))
      | ~ v1_relat_1(B_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_149])).

tff(c_1273,plain,(
    ! [C_163,A_164,B_165] :
      ( r1_tarski(k2_relat_1(k7_relat_1(C_163,k3_xboole_0(A_164,B_165))),k9_relat_1(C_163,A_164))
      | ~ v1_relat_1(k7_relat_1(C_163,A_164))
      | ~ v1_relat_1(C_163)
      | ~ v1_relat_1(C_163) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_556])).

tff(c_3045,plain,(
    ! [B_246,A_247,B_248] :
      ( r1_tarski(k9_relat_1(B_246,k3_xboole_0(A_247,B_248)),k9_relat_1(B_246,A_247))
      | ~ v1_relat_1(k7_relat_1(B_246,A_247))
      | ~ v1_relat_1(B_246)
      | ~ v1_relat_1(B_246)
      | ~ v1_relat_1(B_246) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1273])).

tff(c_182,plain,(
    ! [A_72,B_73,C_74] :
      ( r1_tarski(A_72,k3_xboole_0(B_73,C_74))
      | ~ r1_tarski(A_72,C_74)
      | ~ r1_tarski(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_34,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_196,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_182,c_34])).

tff(c_252,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_3048,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3045,c_252])).

tff(c_3098,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3048])).

tff(c_3102,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_3098])).

tff(c_3106,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3102])).

tff(c_3107,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_6926,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6923,c_3107])).

tff(c_6976,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_6926])).

tff(c_6980,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_6976])).

tff(c_6984,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_6980])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:51:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.75/2.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.75/2.61  
% 7.75/2.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.75/2.61  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 7.75/2.61  
% 7.75/2.61  %Foreground sorts:
% 7.75/2.61  
% 7.75/2.61  
% 7.75/2.61  %Background operators:
% 7.75/2.61  
% 7.75/2.61  
% 7.75/2.61  %Foreground operators:
% 7.75/2.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.75/2.61  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.75/2.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.75/2.61  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.75/2.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.75/2.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.75/2.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.75/2.61  tff('#skF_2', type, '#skF_2': $i).
% 7.75/2.61  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.75/2.61  tff('#skF_3', type, '#skF_3': $i).
% 7.75/2.61  tff('#skF_1', type, '#skF_1': $i).
% 7.75/2.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.75/2.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.75/2.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.75/2.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.75/2.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.75/2.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.75/2.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.75/2.61  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.75/2.61  
% 7.75/2.63  tff(f_88, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_relat_1)).
% 7.75/2.63  tff(f_56, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 7.75/2.63  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 7.75/2.63  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.75/2.63  tff(f_60, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 7.75/2.63  tff(f_83, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k7_relat_1(B, A)), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_relat_1)).
% 7.75/2.63  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 7.75/2.63  tff(c_36, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.75/2.63  tff(c_20, plain, (![A_20, B_21]: (v1_relat_1(k7_relat_1(A_20, B_21)) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.75/2.63  tff(c_26, plain, (![B_29, A_28]: (k2_relat_1(k7_relat_1(B_29, A_28))=k9_relat_1(B_29, A_28) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.75/2.63  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.75/2.63  tff(c_202, plain, (![C_77, A_78, B_79]: (k7_relat_1(k7_relat_1(C_77, A_78), B_79)=k7_relat_1(C_77, k3_xboole_0(A_78, B_79)) | ~v1_relat_1(C_77))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.75/2.63  tff(c_32, plain, (![B_34, A_33]: (r1_tarski(k2_relat_1(k7_relat_1(B_34, A_33)), k2_relat_1(B_34)) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.75/2.63  tff(c_3544, plain, (![C_278, A_279, B_280]: (r1_tarski(k2_relat_1(k7_relat_1(C_278, k3_xboole_0(A_279, B_280))), k2_relat_1(k7_relat_1(C_278, A_279))) | ~v1_relat_1(k7_relat_1(C_278, A_279)) | ~v1_relat_1(C_278))), inference(superposition, [status(thm), theory('equality')], [c_202, c_32])).
% 7.75/2.63  tff(c_3684, plain, (![C_287, B_288, A_289]: (r1_tarski(k2_relat_1(k7_relat_1(C_287, k3_xboole_0(B_288, A_289))), k2_relat_1(k7_relat_1(C_287, A_289))) | ~v1_relat_1(k7_relat_1(C_287, A_289)) | ~v1_relat_1(C_287))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3544])).
% 7.75/2.63  tff(c_4327, plain, (![B_341, B_342, A_343]: (r1_tarski(k2_relat_1(k7_relat_1(B_341, k3_xboole_0(B_342, A_343))), k9_relat_1(B_341, A_343)) | ~v1_relat_1(k7_relat_1(B_341, A_343)) | ~v1_relat_1(B_341) | ~v1_relat_1(B_341))), inference(superposition, [status(thm), theory('equality')], [c_26, c_3684])).
% 7.75/2.63  tff(c_6923, plain, (![B_451, B_452, A_453]: (r1_tarski(k9_relat_1(B_451, k3_xboole_0(B_452, A_453)), k9_relat_1(B_451, A_453)) | ~v1_relat_1(k7_relat_1(B_451, A_453)) | ~v1_relat_1(B_451) | ~v1_relat_1(B_451) | ~v1_relat_1(B_451))), inference(superposition, [status(thm), theory('equality')], [c_26, c_4327])).
% 7.75/2.63  tff(c_22, plain, (![C_24, A_22, B_23]: (k7_relat_1(k7_relat_1(C_24, A_22), B_23)=k7_relat_1(C_24, k3_xboole_0(A_22, B_23)) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.75/2.63  tff(c_149, plain, (![B_61, A_62]: (r1_tarski(k2_relat_1(k7_relat_1(B_61, A_62)), k2_relat_1(B_61)) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.75/2.63  tff(c_556, plain, (![B_104, A_105, A_106]: (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(B_104, A_105), A_106)), k9_relat_1(B_104, A_105)) | ~v1_relat_1(k7_relat_1(B_104, A_105)) | ~v1_relat_1(B_104))), inference(superposition, [status(thm), theory('equality')], [c_26, c_149])).
% 7.75/2.63  tff(c_1273, plain, (![C_163, A_164, B_165]: (r1_tarski(k2_relat_1(k7_relat_1(C_163, k3_xboole_0(A_164, B_165))), k9_relat_1(C_163, A_164)) | ~v1_relat_1(k7_relat_1(C_163, A_164)) | ~v1_relat_1(C_163) | ~v1_relat_1(C_163))), inference(superposition, [status(thm), theory('equality')], [c_22, c_556])).
% 7.75/2.63  tff(c_3045, plain, (![B_246, A_247, B_248]: (r1_tarski(k9_relat_1(B_246, k3_xboole_0(A_247, B_248)), k9_relat_1(B_246, A_247)) | ~v1_relat_1(k7_relat_1(B_246, A_247)) | ~v1_relat_1(B_246) | ~v1_relat_1(B_246) | ~v1_relat_1(B_246))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1273])).
% 7.75/2.63  tff(c_182, plain, (![A_72, B_73, C_74]: (r1_tarski(A_72, k3_xboole_0(B_73, C_74)) | ~r1_tarski(A_72, C_74) | ~r1_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.75/2.63  tff(c_34, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.75/2.63  tff(c_196, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_182, c_34])).
% 7.75/2.63  tff(c_252, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_196])).
% 7.75/2.63  tff(c_3048, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3045, c_252])).
% 7.75/2.63  tff(c_3098, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_3048])).
% 7.75/2.63  tff(c_3102, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_3098])).
% 7.75/2.63  tff(c_3106, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_3102])).
% 7.75/2.63  tff(c_3107, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_196])).
% 7.75/2.63  tff(c_6926, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6923, c_3107])).
% 7.75/2.63  tff(c_6976, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_6926])).
% 7.75/2.63  tff(c_6980, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_6976])).
% 7.75/2.63  tff(c_6984, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_6980])).
% 7.75/2.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.75/2.63  
% 7.75/2.63  Inference rules
% 7.75/2.63  ----------------------
% 7.75/2.63  #Ref     : 0
% 7.75/2.63  #Sup     : 2075
% 7.75/2.63  #Fact    : 0
% 7.75/2.63  #Define  : 0
% 7.75/2.63  #Split   : 2
% 7.75/2.63  #Chain   : 0
% 7.75/2.63  #Close   : 0
% 7.75/2.63  
% 7.75/2.63  Ordering : KBO
% 7.75/2.63  
% 7.75/2.63  Simplification rules
% 7.75/2.63  ----------------------
% 7.75/2.63  #Subsume      : 514
% 7.75/2.63  #Demod        : 8
% 7.75/2.63  #Tautology    : 112
% 7.75/2.63  #SimpNegUnit  : 0
% 7.75/2.63  #BackRed      : 0
% 7.75/2.63  
% 7.75/2.63  #Partial instantiations: 0
% 7.75/2.63  #Strategies tried      : 1
% 7.75/2.63  
% 7.75/2.63  Timing (in seconds)
% 7.75/2.63  ----------------------
% 7.75/2.63  Preprocessing        : 0.30
% 7.75/2.63  Parsing              : 0.17
% 7.75/2.63  CNF conversion       : 0.02
% 7.75/2.63  Main loop            : 1.56
% 7.75/2.63  Inferencing          : 0.56
% 7.75/2.63  Reduction            : 0.47
% 7.75/2.63  Demodulation         : 0.36
% 7.75/2.63  BG Simplification    : 0.08
% 7.75/2.63  Subsumption          : 0.37
% 7.75/2.63  Abstraction          : 0.07
% 7.75/2.63  MUC search           : 0.00
% 7.75/2.63  Cooper               : 0.00
% 7.75/2.63  Total                : 1.89
% 7.75/2.63  Index Insertion      : 0.00
% 7.75/2.63  Index Deletion       : 0.00
% 7.75/2.63  Index Matching       : 0.00
% 7.75/2.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
