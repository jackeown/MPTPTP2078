%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:25 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   41 (  56 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   53 (  94 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( r2_hidden(B,A)
           => ( r2_hidden(k1_mcart_1(B),k1_relat_1(A))
              & r2_hidden(k2_mcart_1(B),k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_mcart_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_30,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_37,plain,(
    ! [A_25] :
      ( r1_tarski(A_25,k2_zfmisc_1(k1_relat_1(A_25),k2_relat_1(A_25)))
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_89,plain,(
    ! [A_39] :
      ( k3_xboole_0(A_39,k2_zfmisc_1(k1_relat_1(A_39),k2_relat_1(A_39))) = A_39
      | ~ v1_relat_1(A_39) ) ),
    inference(resolution,[status(thm)],[c_37,c_20])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_153,plain,(
    ! [D_46,A_47] :
      ( r2_hidden(D_46,k2_zfmisc_1(k1_relat_1(A_47),k2_relat_1(A_47)))
      | ~ r2_hidden(D_46,A_47)
      | ~ v1_relat_1(A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_4])).

tff(c_24,plain,(
    ! [A_10,C_12,B_11] :
      ( r2_hidden(k2_mcart_1(A_10),C_12)
      | ~ r2_hidden(A_10,k2_zfmisc_1(B_11,C_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_160,plain,(
    ! [D_48,A_49] :
      ( r2_hidden(k2_mcart_1(D_48),k2_relat_1(A_49))
      | ~ r2_hidden(D_48,A_49)
      | ~ v1_relat_1(A_49) ) ),
    inference(resolution,[status(thm)],[c_153,c_24])).

tff(c_44,plain,(
    ! [A_29] :
      ( k3_xboole_0(A_29,k2_zfmisc_1(k1_relat_1(A_29),k2_relat_1(A_29))) = A_29
      | ~ v1_relat_1(A_29) ) ),
    inference(resolution,[status(thm)],[c_37,c_20])).

tff(c_71,plain,(
    ! [D_33,A_34] :
      ( r2_hidden(D_33,k2_zfmisc_1(k1_relat_1(A_34),k2_relat_1(A_34)))
      | ~ r2_hidden(D_33,A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_4])).

tff(c_26,plain,(
    ! [A_10,B_11,C_12] :
      ( r2_hidden(k1_mcart_1(A_10),B_11)
      | ~ r2_hidden(A_10,k2_zfmisc_1(B_11,C_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_79,plain,(
    ! [D_37,A_38] :
      ( r2_hidden(k1_mcart_1(D_37),k1_relat_1(A_38))
      | ~ r2_hidden(D_37,A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(resolution,[status(thm)],[c_71,c_26])).

tff(c_28,plain,
    ( ~ r2_hidden(k2_mcart_1('#skF_4'),k2_relat_1('#skF_3'))
    | ~ r2_hidden(k1_mcart_1('#skF_4'),k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_43,plain,(
    ~ r2_hidden(k1_mcart_1('#skF_4'),k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_82,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_79,c_43])).

tff(c_86,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_82])).

tff(c_87,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_4'),k2_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_163,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_160,c_87])).

tff(c_167,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_163])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:24:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.14  
% 1.70/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.14  %$ r2_hidden > r1_tarski > v1_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 1.70/1.14  
% 1.70/1.14  %Foreground sorts:
% 1.70/1.14  
% 1.70/1.14  
% 1.70/1.14  %Background operators:
% 1.70/1.14  
% 1.70/1.14  
% 1.70/1.14  %Foreground operators:
% 1.70/1.14  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.70/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.70/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.70/1.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.70/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.70/1.14  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.70/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.14  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.70/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.70/1.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.70/1.14  tff('#skF_4', type, '#skF_4': $i).
% 1.70/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.14  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.70/1.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.70/1.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.70/1.14  
% 1.70/1.15  tff(f_58, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (r2_hidden(B, A) => (r2_hidden(k1_mcart_1(B), k1_relat_1(A)) & r2_hidden(k2_mcart_1(B), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_mcart_1)).
% 1.70/1.15  tff(f_42, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 1.70/1.15  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.70/1.15  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.70/1.15  tff(f_48, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.70/1.15  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.70/1.15  tff(c_30, plain, (r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.70/1.15  tff(c_37, plain, (![A_25]: (r1_tarski(A_25, k2_zfmisc_1(k1_relat_1(A_25), k2_relat_1(A_25))) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.70/1.15  tff(c_20, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.70/1.15  tff(c_89, plain, (![A_39]: (k3_xboole_0(A_39, k2_zfmisc_1(k1_relat_1(A_39), k2_relat_1(A_39)))=A_39 | ~v1_relat_1(A_39))), inference(resolution, [status(thm)], [c_37, c_20])).
% 1.70/1.15  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.70/1.15  tff(c_153, plain, (![D_46, A_47]: (r2_hidden(D_46, k2_zfmisc_1(k1_relat_1(A_47), k2_relat_1(A_47))) | ~r2_hidden(D_46, A_47) | ~v1_relat_1(A_47))), inference(superposition, [status(thm), theory('equality')], [c_89, c_4])).
% 1.70/1.15  tff(c_24, plain, (![A_10, C_12, B_11]: (r2_hidden(k2_mcart_1(A_10), C_12) | ~r2_hidden(A_10, k2_zfmisc_1(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.70/1.15  tff(c_160, plain, (![D_48, A_49]: (r2_hidden(k2_mcart_1(D_48), k2_relat_1(A_49)) | ~r2_hidden(D_48, A_49) | ~v1_relat_1(A_49))), inference(resolution, [status(thm)], [c_153, c_24])).
% 1.70/1.15  tff(c_44, plain, (![A_29]: (k3_xboole_0(A_29, k2_zfmisc_1(k1_relat_1(A_29), k2_relat_1(A_29)))=A_29 | ~v1_relat_1(A_29))), inference(resolution, [status(thm)], [c_37, c_20])).
% 1.70/1.15  tff(c_71, plain, (![D_33, A_34]: (r2_hidden(D_33, k2_zfmisc_1(k1_relat_1(A_34), k2_relat_1(A_34))) | ~r2_hidden(D_33, A_34) | ~v1_relat_1(A_34))), inference(superposition, [status(thm), theory('equality')], [c_44, c_4])).
% 1.70/1.15  tff(c_26, plain, (![A_10, B_11, C_12]: (r2_hidden(k1_mcart_1(A_10), B_11) | ~r2_hidden(A_10, k2_zfmisc_1(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.70/1.15  tff(c_79, plain, (![D_37, A_38]: (r2_hidden(k1_mcart_1(D_37), k1_relat_1(A_38)) | ~r2_hidden(D_37, A_38) | ~v1_relat_1(A_38))), inference(resolution, [status(thm)], [c_71, c_26])).
% 1.70/1.15  tff(c_28, plain, (~r2_hidden(k2_mcart_1('#skF_4'), k2_relat_1('#skF_3')) | ~r2_hidden(k1_mcart_1('#skF_4'), k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.70/1.15  tff(c_43, plain, (~r2_hidden(k1_mcart_1('#skF_4'), k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_28])).
% 1.70/1.15  tff(c_82, plain, (~r2_hidden('#skF_4', '#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_79, c_43])).
% 1.70/1.15  tff(c_86, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_82])).
% 1.70/1.15  tff(c_87, plain, (~r2_hidden(k2_mcart_1('#skF_4'), k2_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_28])).
% 1.70/1.15  tff(c_163, plain, (~r2_hidden('#skF_4', '#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_160, c_87])).
% 1.70/1.15  tff(c_167, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_163])).
% 1.70/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.15  
% 1.70/1.15  Inference rules
% 1.70/1.15  ----------------------
% 1.70/1.15  #Ref     : 0
% 1.70/1.15  #Sup     : 29
% 1.70/1.15  #Fact    : 0
% 1.70/1.15  #Define  : 0
% 1.70/1.15  #Split   : 1
% 1.70/1.15  #Chain   : 0
% 1.70/1.15  #Close   : 0
% 1.70/1.15  
% 1.70/1.15  Ordering : KBO
% 1.70/1.15  
% 1.70/1.15  Simplification rules
% 1.70/1.15  ----------------------
% 1.70/1.15  #Subsume      : 0
% 1.70/1.15  #Demod        : 4
% 1.70/1.15  #Tautology    : 12
% 1.70/1.15  #SimpNegUnit  : 0
% 1.70/1.15  #BackRed      : 0
% 1.70/1.15  
% 1.70/1.15  #Partial instantiations: 0
% 1.70/1.15  #Strategies tried      : 1
% 1.70/1.15  
% 1.70/1.15  Timing (in seconds)
% 1.70/1.15  ----------------------
% 1.70/1.15  Preprocessing        : 0.26
% 1.70/1.15  Parsing              : 0.14
% 1.70/1.15  CNF conversion       : 0.02
% 1.70/1.15  Main loop            : 0.17
% 1.70/1.15  Inferencing          : 0.07
% 1.70/1.15  Reduction            : 0.04
% 1.70/1.15  Demodulation         : 0.03
% 1.70/1.15  BG Simplification    : 0.01
% 1.70/1.15  Subsumption          : 0.03
% 1.70/1.15  Abstraction          : 0.01
% 1.70/1.15  MUC search           : 0.00
% 1.70/1.15  Cooper               : 0.00
% 1.70/1.15  Total                : 0.46
% 1.70/1.15  Index Insertion      : 0.00
% 1.70/1.15  Index Deletion       : 0.00
% 1.70/1.15  Index Matching       : 0.00
% 1.70/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
