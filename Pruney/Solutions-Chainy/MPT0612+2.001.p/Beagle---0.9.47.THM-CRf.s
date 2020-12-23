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
% DateTime   : Thu Dec  3 10:02:41 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   41 (  49 expanded)
%              Number of leaves         :   23 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   50 (  62 expanded)
%              Number of equality atoms :   13 (  21 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k6_subset_1(C,k7_relat_1(C,B)),A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t216_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_31,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [A_6,B_7] : k6_subset_1(A_6,B_7) = k4_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_4,B_5] : m1_subset_1(k6_subset_1(A_4,B_5),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_21,plain,(
    ! [A_4,B_5] : m1_subset_1(k4_xboole_0(A_4,B_5),k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4])).

tff(c_33,plain,(
    ! [B_23,A_24] :
      ( v1_relat_1(B_23)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(A_24))
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_37,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(k4_xboole_0(A_4,B_5))
      | ~ v1_relat_1(A_4) ) ),
    inference(resolution,[status(thm)],[c_21,c_33])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_xboole_0(A_1,k4_xboole_0(C_3,B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [B_15,A_14] :
      ( k1_relat_1(k6_subset_1(B_15,k7_relat_1(B_15,A_14))) = k6_subset_1(k1_relat_1(B_15),A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_40,plain,(
    ! [B_29,A_30] :
      ( k1_relat_1(k4_xboole_0(B_29,k7_relat_1(B_29,A_30))) = k4_xboole_0(k1_relat_1(B_29),A_30)
      | ~ v1_relat_1(B_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_12])).

tff(c_10,plain,(
    ! [A_11,B_13] :
      ( k7_relat_1(A_11,B_13) = k1_xboole_0
      | ~ r1_xboole_0(B_13,k1_relat_1(A_11))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_52,plain,(
    ! [B_31,A_32,B_33] :
      ( k7_relat_1(k4_xboole_0(B_31,k7_relat_1(B_31,A_32)),B_33) = k1_xboole_0
      | ~ r1_xboole_0(B_33,k4_xboole_0(k1_relat_1(B_31),A_32))
      | ~ v1_relat_1(k4_xboole_0(B_31,k7_relat_1(B_31,A_32)))
      | ~ v1_relat_1(B_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_10])).

tff(c_59,plain,(
    ! [B_34,B_35,A_36] :
      ( k7_relat_1(k4_xboole_0(B_34,k7_relat_1(B_34,B_35)),A_36) = k1_xboole_0
      | ~ v1_relat_1(k4_xboole_0(B_34,k7_relat_1(B_34,B_35)))
      | ~ v1_relat_1(B_34)
      | ~ r1_tarski(A_36,B_35) ) ),
    inference(resolution,[status(thm)],[c_2,c_52])).

tff(c_64,plain,(
    ! [A_37,B_38,A_39] :
      ( k7_relat_1(k4_xboole_0(A_37,k7_relat_1(A_37,B_38)),A_39) = k1_xboole_0
      | ~ r1_tarski(A_39,B_38)
      | ~ v1_relat_1(A_37) ) ),
    inference(resolution,[status(thm)],[c_37,c_59])).

tff(c_14,plain,(
    k7_relat_1(k6_subset_1('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_19,plain,(
    k7_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14])).

tff(c_76,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_19])).

tff(c_87,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_76])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n019.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:16:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.13  
% 1.68/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.13  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.68/1.13  
% 1.68/1.13  %Foreground sorts:
% 1.68/1.13  
% 1.68/1.13  
% 1.68/1.13  %Background operators:
% 1.68/1.13  
% 1.68/1.13  
% 1.68/1.13  %Foreground operators:
% 1.68/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.68/1.13  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.68/1.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.68/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.68/1.13  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.68/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.68/1.13  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.68/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.68/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.68/1.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.68/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.68/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.68/1.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.68/1.13  
% 1.84/1.14  tff(f_58, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k6_subset_1(C, k7_relat_1(C, B)), A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t216_relat_1)).
% 1.84/1.14  tff(f_33, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.84/1.14  tff(f_31, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 1.84/1.14  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.84/1.14  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 1.84/1.14  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t212_relat_1)).
% 1.84/1.14  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 1.84/1.14  tff(c_18, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.84/1.14  tff(c_16, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.84/1.14  tff(c_6, plain, (![A_6, B_7]: (k6_subset_1(A_6, B_7)=k4_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.84/1.14  tff(c_4, plain, (![A_4, B_5]: (m1_subset_1(k6_subset_1(A_4, B_5), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.84/1.14  tff(c_21, plain, (![A_4, B_5]: (m1_subset_1(k4_xboole_0(A_4, B_5), k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_4])).
% 1.84/1.14  tff(c_33, plain, (![B_23, A_24]: (v1_relat_1(B_23) | ~m1_subset_1(B_23, k1_zfmisc_1(A_24)) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.84/1.14  tff(c_37, plain, (![A_4, B_5]: (v1_relat_1(k4_xboole_0(A_4, B_5)) | ~v1_relat_1(A_4))), inference(resolution, [status(thm)], [c_21, c_33])).
% 1.84/1.14  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_xboole_0(A_1, k4_xboole_0(C_3, B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.84/1.14  tff(c_12, plain, (![B_15, A_14]: (k1_relat_1(k6_subset_1(B_15, k7_relat_1(B_15, A_14)))=k6_subset_1(k1_relat_1(B_15), A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.84/1.14  tff(c_40, plain, (![B_29, A_30]: (k1_relat_1(k4_xboole_0(B_29, k7_relat_1(B_29, A_30)))=k4_xboole_0(k1_relat_1(B_29), A_30) | ~v1_relat_1(B_29))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_12])).
% 1.84/1.14  tff(c_10, plain, (![A_11, B_13]: (k7_relat_1(A_11, B_13)=k1_xboole_0 | ~r1_xboole_0(B_13, k1_relat_1(A_11)) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.84/1.14  tff(c_52, plain, (![B_31, A_32, B_33]: (k7_relat_1(k4_xboole_0(B_31, k7_relat_1(B_31, A_32)), B_33)=k1_xboole_0 | ~r1_xboole_0(B_33, k4_xboole_0(k1_relat_1(B_31), A_32)) | ~v1_relat_1(k4_xboole_0(B_31, k7_relat_1(B_31, A_32))) | ~v1_relat_1(B_31))), inference(superposition, [status(thm), theory('equality')], [c_40, c_10])).
% 1.84/1.14  tff(c_59, plain, (![B_34, B_35, A_36]: (k7_relat_1(k4_xboole_0(B_34, k7_relat_1(B_34, B_35)), A_36)=k1_xboole_0 | ~v1_relat_1(k4_xboole_0(B_34, k7_relat_1(B_34, B_35))) | ~v1_relat_1(B_34) | ~r1_tarski(A_36, B_35))), inference(resolution, [status(thm)], [c_2, c_52])).
% 1.84/1.14  tff(c_64, plain, (![A_37, B_38, A_39]: (k7_relat_1(k4_xboole_0(A_37, k7_relat_1(A_37, B_38)), A_39)=k1_xboole_0 | ~r1_tarski(A_39, B_38) | ~v1_relat_1(A_37))), inference(resolution, [status(thm)], [c_37, c_59])).
% 1.84/1.14  tff(c_14, plain, (k7_relat_1(k6_subset_1('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.84/1.14  tff(c_19, plain, (k7_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6, c_14])).
% 1.84/1.14  tff(c_76, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_64, c_19])).
% 1.84/1.14  tff(c_87, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_76])).
% 1.84/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.14  
% 1.84/1.14  Inference rules
% 1.84/1.14  ----------------------
% 1.84/1.14  #Ref     : 0
% 1.84/1.14  #Sup     : 15
% 1.84/1.14  #Fact    : 0
% 1.84/1.14  #Define  : 0
% 1.84/1.14  #Split   : 0
% 1.84/1.14  #Chain   : 0
% 1.84/1.14  #Close   : 0
% 1.84/1.14  
% 1.84/1.14  Ordering : KBO
% 1.84/1.14  
% 1.84/1.14  Simplification rules
% 1.84/1.14  ----------------------
% 1.84/1.14  #Subsume      : 1
% 1.84/1.14  #Demod        : 6
% 1.84/1.14  #Tautology    : 5
% 1.84/1.14  #SimpNegUnit  : 0
% 1.84/1.14  #BackRed      : 0
% 1.84/1.14  
% 1.84/1.14  #Partial instantiations: 0
% 1.84/1.14  #Strategies tried      : 1
% 1.84/1.14  
% 1.84/1.14  Timing (in seconds)
% 1.84/1.14  ----------------------
% 1.84/1.15  Preprocessing        : 0.28
% 1.84/1.15  Parsing              : 0.15
% 1.84/1.15  CNF conversion       : 0.02
% 1.84/1.15  Main loop            : 0.11
% 1.84/1.15  Inferencing          : 0.05
% 1.84/1.15  Reduction            : 0.03
% 1.84/1.15  Demodulation         : 0.02
% 1.84/1.15  BG Simplification    : 0.01
% 1.84/1.15  Subsumption          : 0.01
% 1.84/1.15  Abstraction          : 0.01
% 1.84/1.15  MUC search           : 0.00
% 1.84/1.15  Cooper               : 0.00
% 1.84/1.15  Total                : 0.41
% 1.84/1.15  Index Insertion      : 0.00
% 1.84/1.15  Index Deletion       : 0.00
% 1.84/1.15  Index Matching       : 0.00
% 1.84/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
