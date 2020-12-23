%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:37 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   46 (  63 expanded)
%              Number of leaves         :   25 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   60 ( 106 expanded)
%              Number of equality atoms :    9 (  13 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_45,plain,(
    ! [A_29] : k2_tarski(A_29,A_29) = k1_tarski(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_8,plain,(
    ! [D_10,A_5] : r2_hidden(D_10,k2_tarski(A_5,D_10)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_51,plain,(
    ! [A_29] : r2_hidden(A_29,k1_tarski(A_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_8])).

tff(c_62,plain,(
    ! [B_31,A_32] :
      ( ~ r2_hidden(B_31,A_32)
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,(
    ! [A_29] : ~ v1_xboole_0(k1_tarski(A_29)) ),
    inference(resolution,[status(thm)],[c_51,c_62])).

tff(c_36,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_40,plain,(
    m1_subset_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_142,plain,(
    ! [A_47,B_48] :
      ( k6_domain_1(A_47,B_48) = k1_tarski(B_48)
      | ~ m1_subset_1(B_48,A_47)
      | v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_145,plain,
    ( k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_142])).

tff(c_148,plain,(
    k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_145])).

tff(c_38,plain,(
    v1_subset_1(k6_domain_1('#skF_4','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_149,plain,(
    v1_subset_1(k1_tarski('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_38])).

tff(c_215,plain,(
    ! [A_51,B_52] :
      ( m1_subset_1(k6_domain_1(A_51,B_52),k1_zfmisc_1(A_51))
      | ~ m1_subset_1(B_52,A_51)
      | v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_224,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_215])).

tff(c_228,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_224])).

tff(c_229,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_228])).

tff(c_240,plain,(
    ! [B_53,A_54] :
      ( ~ v1_subset_1(B_53,A_54)
      | v1_xboole_0(B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_54))
      | ~ v1_zfmisc_1(A_54)
      | v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_243,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_5'),'#skF_4')
    | v1_xboole_0(k1_tarski('#skF_5'))
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_229,c_240])).

tff(c_249,plain,
    ( v1_xboole_0(k1_tarski('#skF_5'))
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_149,c_243])).

tff(c_251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_72,c_249])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:28:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.28  
% 1.99/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.28  %$ v1_subset_1 > r2_hidden > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 1.99/1.28  
% 1.99/1.28  %Foreground sorts:
% 1.99/1.28  
% 1.99/1.28  
% 1.99/1.28  %Background operators:
% 1.99/1.28  
% 1.99/1.28  
% 1.99/1.28  %Foreground operators:
% 1.99/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.99/1.28  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 1.99/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.99/1.28  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.99/1.28  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 1.99/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.99/1.28  tff('#skF_5', type, '#skF_5': $i).
% 1.99/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.99/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.99/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.99/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.28  tff('#skF_4', type, '#skF_4': $i).
% 1.99/1.28  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.99/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.28  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.99/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.99/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.99/1.28  
% 1.99/1.29  tff(f_92, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 1.99/1.29  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.99/1.29  tff(f_40, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.99/1.29  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.99/1.29  tff(f_66, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 1.99/1.29  tff(f_59, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 1.99/1.29  tff(f_80, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 1.99/1.29  tff(c_42, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 1.99/1.29  tff(c_45, plain, (![A_29]: (k2_tarski(A_29, A_29)=k1_tarski(A_29))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.99/1.29  tff(c_8, plain, (![D_10, A_5]: (r2_hidden(D_10, k2_tarski(A_5, D_10)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.99/1.29  tff(c_51, plain, (![A_29]: (r2_hidden(A_29, k1_tarski(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_45, c_8])).
% 1.99/1.29  tff(c_62, plain, (![B_31, A_32]: (~r2_hidden(B_31, A_32) | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.99/1.29  tff(c_72, plain, (![A_29]: (~v1_xboole_0(k1_tarski(A_29)))), inference(resolution, [status(thm)], [c_51, c_62])).
% 1.99/1.29  tff(c_36, plain, (v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 1.99/1.29  tff(c_40, plain, (m1_subset_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 1.99/1.29  tff(c_142, plain, (![A_47, B_48]: (k6_domain_1(A_47, B_48)=k1_tarski(B_48) | ~m1_subset_1(B_48, A_47) | v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.99/1.29  tff(c_145, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_40, c_142])).
% 1.99/1.29  tff(c_148, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_42, c_145])).
% 1.99/1.29  tff(c_38, plain, (v1_subset_1(k6_domain_1('#skF_4', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 1.99/1.29  tff(c_149, plain, (v1_subset_1(k1_tarski('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_38])).
% 1.99/1.29  tff(c_215, plain, (![A_51, B_52]: (m1_subset_1(k6_domain_1(A_51, B_52), k1_zfmisc_1(A_51)) | ~m1_subset_1(B_52, A_51) | v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.99/1.29  tff(c_224, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', '#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_148, c_215])).
% 1.99/1.29  tff(c_228, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_224])).
% 1.99/1.29  tff(c_229, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_42, c_228])).
% 1.99/1.29  tff(c_240, plain, (![B_53, A_54]: (~v1_subset_1(B_53, A_54) | v1_xboole_0(B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_54)) | ~v1_zfmisc_1(A_54) | v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.99/1.29  tff(c_243, plain, (~v1_subset_1(k1_tarski('#skF_5'), '#skF_4') | v1_xboole_0(k1_tarski('#skF_5')) | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_229, c_240])).
% 1.99/1.29  tff(c_249, plain, (v1_xboole_0(k1_tarski('#skF_5')) | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_149, c_243])).
% 1.99/1.29  tff(c_251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_72, c_249])).
% 1.99/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.29  
% 1.99/1.29  Inference rules
% 1.99/1.29  ----------------------
% 1.99/1.29  #Ref     : 0
% 1.99/1.29  #Sup     : 42
% 1.99/1.29  #Fact    : 2
% 1.99/1.29  #Define  : 0
% 1.99/1.29  #Split   : 0
% 1.99/1.29  #Chain   : 0
% 1.99/1.29  #Close   : 0
% 1.99/1.29  
% 1.99/1.29  Ordering : KBO
% 1.99/1.29  
% 1.99/1.29  Simplification rules
% 1.99/1.29  ----------------------
% 1.99/1.29  #Subsume      : 7
% 1.99/1.29  #Demod        : 19
% 1.99/1.29  #Tautology    : 25
% 1.99/1.29  #SimpNegUnit  : 8
% 1.99/1.29  #BackRed      : 1
% 1.99/1.29  
% 1.99/1.29  #Partial instantiations: 0
% 1.99/1.29  #Strategies tried      : 1
% 1.99/1.29  
% 1.99/1.29  Timing (in seconds)
% 1.99/1.29  ----------------------
% 1.99/1.29  Preprocessing        : 0.33
% 1.99/1.29  Parsing              : 0.17
% 1.99/1.29  CNF conversion       : 0.02
% 1.99/1.29  Main loop            : 0.16
% 1.99/1.29  Inferencing          : 0.06
% 1.99/1.29  Reduction            : 0.05
% 1.99/1.29  Demodulation         : 0.04
% 1.99/1.29  BG Simplification    : 0.02
% 1.99/1.29  Subsumption          : 0.02
% 1.99/1.29  Abstraction          : 0.01
% 1.99/1.29  MUC search           : 0.00
% 1.99/1.29  Cooper               : 0.00
% 1.99/1.29  Total                : 0.51
% 1.99/1.29  Index Insertion      : 0.00
% 1.99/1.29  Index Deletion       : 0.00
% 1.99/1.29  Index Matching       : 0.00
% 1.99/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
