%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:25 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   37 (  49 expanded)
%              Number of leaves         :   19 (  27 expanded)
%              Depth                    :    5
%              Number of atoms          :   47 (  82 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(f_54,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( r2_hidden(B,A)
           => ( r2_hidden(k1_mcart_1(B),k1_relat_1(A))
              & r2_hidden(k2_mcart_1(B),k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_mcart_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_28,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_81,plain,(
    ! [A_34] :
      ( k3_xboole_0(A_34,k2_zfmisc_1(k1_relat_1(A_34),k2_relat_1(A_34))) = A_34
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_108,plain,(
    ! [D_38,A_39] :
      ( r2_hidden(D_38,k2_zfmisc_1(k1_relat_1(A_39),k2_relat_1(A_39)))
      | ~ r2_hidden(D_38,A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_4])).

tff(c_22,plain,(
    ! [A_8,C_10,B_9] :
      ( r2_hidden(k2_mcart_1(A_8),C_10)
      | ~ r2_hidden(A_8,k2_zfmisc_1(B_9,C_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_115,plain,(
    ! [D_40,A_41] :
      ( r2_hidden(k2_mcart_1(D_40),k2_relat_1(A_41))
      | ~ r2_hidden(D_40,A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(resolution,[status(thm)],[c_108,c_22])).

tff(c_36,plain,(
    ! [A_24] :
      ( k3_xboole_0(A_24,k2_zfmisc_1(k1_relat_1(A_24),k2_relat_1(A_24))) = A_24
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_63,plain,(
    ! [D_28,A_29] :
      ( r2_hidden(D_28,k2_zfmisc_1(k1_relat_1(A_29),k2_relat_1(A_29)))
      | ~ r2_hidden(D_28,A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_4])).

tff(c_24,plain,(
    ! [A_8,B_9,C_10] :
      ( r2_hidden(k1_mcart_1(A_8),B_9)
      | ~ r2_hidden(A_8,k2_zfmisc_1(B_9,C_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_71,plain,(
    ! [D_32,A_33] :
      ( r2_hidden(k1_mcart_1(D_32),k1_relat_1(A_33))
      | ~ r2_hidden(D_32,A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(resolution,[status(thm)],[c_63,c_24])).

tff(c_26,plain,
    ( ~ r2_hidden(k2_mcart_1('#skF_4'),k2_relat_1('#skF_3'))
    | ~ r2_hidden(k1_mcart_1('#skF_4'),k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_35,plain,(
    ~ r2_hidden(k1_mcart_1('#skF_4'),k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_74,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_35])).

tff(c_78,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_74])).

tff(c_79,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_4'),k2_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_118,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_115,c_79])).

tff(c_122,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_118])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:09:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.11  
% 1.67/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.11  %$ r2_hidden > v1_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 1.67/1.11  
% 1.67/1.11  %Foreground sorts:
% 1.67/1.11  
% 1.67/1.11  
% 1.67/1.11  %Background operators:
% 1.67/1.11  
% 1.67/1.11  
% 1.67/1.11  %Foreground operators:
% 1.67/1.11  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.67/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.67/1.11  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.67/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.67/1.11  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.67/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.11  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.67/1.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.67/1.11  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.67/1.11  tff('#skF_4', type, '#skF_4': $i).
% 1.67/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.11  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.67/1.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.67/1.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.67/1.11  
% 1.67/1.12  tff(f_54, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (r2_hidden(B, A) => (r2_hidden(k1_mcart_1(B), k1_relat_1(A)) & r2_hidden(k2_mcart_1(B), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_mcart_1)).
% 1.67/1.12  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 1.67/1.12  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.67/1.12  tff(f_44, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.67/1.12  tff(c_30, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.67/1.12  tff(c_28, plain, (r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.67/1.12  tff(c_81, plain, (![A_34]: (k3_xboole_0(A_34, k2_zfmisc_1(k1_relat_1(A_34), k2_relat_1(A_34)))=A_34 | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.67/1.12  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.67/1.12  tff(c_108, plain, (![D_38, A_39]: (r2_hidden(D_38, k2_zfmisc_1(k1_relat_1(A_39), k2_relat_1(A_39))) | ~r2_hidden(D_38, A_39) | ~v1_relat_1(A_39))), inference(superposition, [status(thm), theory('equality')], [c_81, c_4])).
% 1.67/1.12  tff(c_22, plain, (![A_8, C_10, B_9]: (r2_hidden(k2_mcart_1(A_8), C_10) | ~r2_hidden(A_8, k2_zfmisc_1(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.67/1.12  tff(c_115, plain, (![D_40, A_41]: (r2_hidden(k2_mcart_1(D_40), k2_relat_1(A_41)) | ~r2_hidden(D_40, A_41) | ~v1_relat_1(A_41))), inference(resolution, [status(thm)], [c_108, c_22])).
% 1.67/1.12  tff(c_36, plain, (![A_24]: (k3_xboole_0(A_24, k2_zfmisc_1(k1_relat_1(A_24), k2_relat_1(A_24)))=A_24 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.67/1.12  tff(c_63, plain, (![D_28, A_29]: (r2_hidden(D_28, k2_zfmisc_1(k1_relat_1(A_29), k2_relat_1(A_29))) | ~r2_hidden(D_28, A_29) | ~v1_relat_1(A_29))), inference(superposition, [status(thm), theory('equality')], [c_36, c_4])).
% 1.67/1.12  tff(c_24, plain, (![A_8, B_9, C_10]: (r2_hidden(k1_mcart_1(A_8), B_9) | ~r2_hidden(A_8, k2_zfmisc_1(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.67/1.12  tff(c_71, plain, (![D_32, A_33]: (r2_hidden(k1_mcart_1(D_32), k1_relat_1(A_33)) | ~r2_hidden(D_32, A_33) | ~v1_relat_1(A_33))), inference(resolution, [status(thm)], [c_63, c_24])).
% 1.67/1.12  tff(c_26, plain, (~r2_hidden(k2_mcart_1('#skF_4'), k2_relat_1('#skF_3')) | ~r2_hidden(k1_mcart_1('#skF_4'), k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.67/1.12  tff(c_35, plain, (~r2_hidden(k1_mcart_1('#skF_4'), k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_26])).
% 1.67/1.12  tff(c_74, plain, (~r2_hidden('#skF_4', '#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_71, c_35])).
% 1.67/1.12  tff(c_78, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_74])).
% 1.67/1.12  tff(c_79, plain, (~r2_hidden(k2_mcart_1('#skF_4'), k2_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_26])).
% 1.67/1.12  tff(c_118, plain, (~r2_hidden('#skF_4', '#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_115, c_79])).
% 1.67/1.12  tff(c_122, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_118])).
% 1.67/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.12  
% 1.67/1.12  Inference rules
% 1.67/1.12  ----------------------
% 1.67/1.12  #Ref     : 0
% 1.67/1.12  #Sup     : 20
% 1.67/1.12  #Fact    : 0
% 1.67/1.12  #Define  : 0
% 1.67/1.12  #Split   : 1
% 1.67/1.12  #Chain   : 0
% 1.67/1.12  #Close   : 0
% 1.67/1.12  
% 1.67/1.12  Ordering : KBO
% 1.67/1.12  
% 1.67/1.12  Simplification rules
% 1.67/1.12  ----------------------
% 1.67/1.12  #Subsume      : 0
% 1.67/1.12  #Demod        : 4
% 1.67/1.12  #Tautology    : 12
% 1.67/1.12  #SimpNegUnit  : 0
% 1.67/1.12  #BackRed      : 0
% 1.67/1.12  
% 1.67/1.12  #Partial instantiations: 0
% 1.67/1.12  #Strategies tried      : 1
% 1.67/1.12  
% 1.67/1.12  Timing (in seconds)
% 1.67/1.12  ----------------------
% 1.67/1.13  Preprocessing        : 0.26
% 1.67/1.13  Parsing              : 0.14
% 1.67/1.13  CNF conversion       : 0.02
% 1.67/1.13  Main loop            : 0.12
% 1.67/1.13  Inferencing          : 0.04
% 1.67/1.13  Reduction            : 0.03
% 1.67/1.13  Demodulation         : 0.02
% 1.67/1.13  BG Simplification    : 0.01
% 1.67/1.13  Subsumption          : 0.02
% 1.67/1.13  Abstraction          : 0.01
% 1.67/1.13  MUC search           : 0.00
% 1.67/1.13  Cooper               : 0.00
% 1.67/1.13  Total                : 0.41
% 1.67/1.13  Index Insertion      : 0.00
% 1.67/1.13  Index Deletion       : 0.00
% 1.67/1.13  Index Matching       : 0.00
% 1.67/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
