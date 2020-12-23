%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:19 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   44 (  76 expanded)
%              Number of leaves         :   17 (  35 expanded)
%              Depth                    :    5
%              Number of atoms          :   74 ( 180 expanded)
%              Number of equality atoms :    2 (   6 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k8_relat_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k1_relat_1(k8_relat_1(B,C)))
        <=> ( r2_hidden(A,k1_relat_1(C))
            & r2_hidden(k1_funct_1(C,A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,k6_relat_1(B))))
      <=> ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(k1_funct_1(C,A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_1)).

tff(c_12,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_24,plain,
    ( r2_hidden('#skF_1',k1_relat_1(k8_relat_1('#skF_2','#skF_3')))
    | r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_34,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_20,plain,
    ( r2_hidden('#skF_1',k1_relat_1(k8_relat_1('#skF_2','#skF_3')))
    | r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_35,plain,(
    r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k5_relat_1(B_2,k6_relat_1(A_1)) = k8_relat_1(A_1,B_2)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,(
    ! [A_20,C_21,B_22] :
      ( r2_hidden(A_20,k1_relat_1(k5_relat_1(C_21,k6_relat_1(B_22))))
      | ~ r2_hidden(k1_funct_1(C_21,A_20),B_22)
      | ~ r2_hidden(A_20,k1_relat_1(C_21))
      | ~ v1_funct_1(C_21)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_60,plain,(
    ! [A_23,A_24,B_25] :
      ( r2_hidden(A_23,k1_relat_1(k8_relat_1(A_24,B_25)))
      | ~ r2_hidden(k1_funct_1(B_25,A_23),A_24)
      | ~ r2_hidden(A_23,k1_relat_1(B_25))
      | ~ v1_funct_1(B_25)
      | ~ v1_relat_1(B_25)
      | ~ v1_relat_1(B_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_48])).

tff(c_14,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2')
    | ~ r2_hidden('#skF_1',k1_relat_1('#skF_3'))
    | ~ r2_hidden('#skF_1',k1_relat_1(k8_relat_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_41,plain,(
    ~ r2_hidden('#skF_1',k1_relat_1(k8_relat_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_35,c_14])).

tff(c_69,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2')
    | ~ r2_hidden('#skF_1',k1_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_41])).

tff(c_75,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10,c_34,c_35,c_69])).

tff(c_77,plain,(
    ~ r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_76,plain,(
    r2_hidden('#skF_1',k1_relat_1(k8_relat_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_84,plain,(
    ! [C_29,A_30,B_31] :
      ( r2_hidden(k1_funct_1(C_29,A_30),B_31)
      | ~ r2_hidden(A_30,k1_relat_1(k5_relat_1(C_29,k6_relat_1(B_31))))
      | ~ v1_funct_1(C_29)
      | ~ v1_relat_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_107,plain,(
    ! [B_38,A_39,A_40] :
      ( r2_hidden(k1_funct_1(B_38,A_39),A_40)
      | ~ r2_hidden(A_39,k1_relat_1(k8_relat_1(A_40,B_38)))
      | ~ v1_funct_1(B_38)
      | ~ v1_relat_1(B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_84])).

tff(c_110,plain,
    ( r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_107])).

tff(c_113,plain,(
    r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10,c_110])).

tff(c_115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_113])).

tff(c_117,plain,(
    ~ r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_116,plain,(
    r2_hidden('#skF_1',k1_relat_1(k8_relat_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_119,plain,(
    ! [A_41,C_42,B_43] :
      ( r2_hidden(A_41,k1_relat_1(C_42))
      | ~ r2_hidden(A_41,k1_relat_1(k5_relat_1(C_42,k6_relat_1(B_43))))
      | ~ v1_funct_1(C_42)
      | ~ v1_relat_1(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_129,plain,(
    ! [A_47,B_48,A_49] :
      ( r2_hidden(A_47,k1_relat_1(B_48))
      | ~ r2_hidden(A_47,k1_relat_1(k8_relat_1(A_49,B_48)))
      | ~ v1_funct_1(B_48)
      | ~ v1_relat_1(B_48)
      | ~ v1_relat_1(B_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_119])).

tff(c_132,plain,
    ( r2_hidden('#skF_1',k1_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_116,c_129])).

tff(c_135,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10,c_132])).

tff(c_137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_135])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:26:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.26  
% 1.87/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.26  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k8_relat_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.87/1.26  
% 1.87/1.26  %Foreground sorts:
% 1.87/1.26  
% 1.87/1.26  
% 1.87/1.26  %Background operators:
% 1.87/1.26  
% 1.87/1.26  
% 1.87/1.26  %Foreground operators:
% 1.87/1.26  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.87/1.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.87/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.26  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.87/1.26  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.26  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.26  tff('#skF_1', type, '#skF_1': $i).
% 1.87/1.26  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.87/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.87/1.26  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.87/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.87/1.26  
% 1.87/1.27  tff(f_50, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k8_relat_1(B, C))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_funct_1)).
% 1.87/1.27  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 1.87/1.27  tff(f_39, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, k6_relat_1(B)))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_funct_1)).
% 1.87/1.27  tff(c_12, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.87/1.27  tff(c_10, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.87/1.27  tff(c_24, plain, (r2_hidden('#skF_1', k1_relat_1(k8_relat_1('#skF_2', '#skF_3'))) | r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.87/1.27  tff(c_34, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_24])).
% 1.87/1.27  tff(c_20, plain, (r2_hidden('#skF_1', k1_relat_1(k8_relat_1('#skF_2', '#skF_3'))) | r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.87/1.27  tff(c_35, plain, (r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_20])).
% 1.87/1.27  tff(c_2, plain, (![B_2, A_1]: (k5_relat_1(B_2, k6_relat_1(A_1))=k8_relat_1(A_1, B_2) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.87/1.27  tff(c_48, plain, (![A_20, C_21, B_22]: (r2_hidden(A_20, k1_relat_1(k5_relat_1(C_21, k6_relat_1(B_22)))) | ~r2_hidden(k1_funct_1(C_21, A_20), B_22) | ~r2_hidden(A_20, k1_relat_1(C_21)) | ~v1_funct_1(C_21) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.87/1.27  tff(c_60, plain, (![A_23, A_24, B_25]: (r2_hidden(A_23, k1_relat_1(k8_relat_1(A_24, B_25))) | ~r2_hidden(k1_funct_1(B_25, A_23), A_24) | ~r2_hidden(A_23, k1_relat_1(B_25)) | ~v1_funct_1(B_25) | ~v1_relat_1(B_25) | ~v1_relat_1(B_25))), inference(superposition, [status(thm), theory('equality')], [c_2, c_48])).
% 1.87/1.27  tff(c_14, plain, (~r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2') | ~r2_hidden('#skF_1', k1_relat_1('#skF_3')) | ~r2_hidden('#skF_1', k1_relat_1(k8_relat_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.87/1.27  tff(c_41, plain, (~r2_hidden('#skF_1', k1_relat_1(k8_relat_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_35, c_14])).
% 1.87/1.27  tff(c_69, plain, (~r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2') | ~r2_hidden('#skF_1', k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_41])).
% 1.87/1.27  tff(c_75, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_10, c_34, c_35, c_69])).
% 1.87/1.27  tff(c_77, plain, (~r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_20])).
% 1.87/1.27  tff(c_76, plain, (r2_hidden('#skF_1', k1_relat_1(k8_relat_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_20])).
% 1.87/1.27  tff(c_84, plain, (![C_29, A_30, B_31]: (r2_hidden(k1_funct_1(C_29, A_30), B_31) | ~r2_hidden(A_30, k1_relat_1(k5_relat_1(C_29, k6_relat_1(B_31)))) | ~v1_funct_1(C_29) | ~v1_relat_1(C_29))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.87/1.27  tff(c_107, plain, (![B_38, A_39, A_40]: (r2_hidden(k1_funct_1(B_38, A_39), A_40) | ~r2_hidden(A_39, k1_relat_1(k8_relat_1(A_40, B_38))) | ~v1_funct_1(B_38) | ~v1_relat_1(B_38) | ~v1_relat_1(B_38))), inference(superposition, [status(thm), theory('equality')], [c_2, c_84])).
% 1.87/1.27  tff(c_110, plain, (r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_107])).
% 1.87/1.27  tff(c_113, plain, (r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_10, c_110])).
% 1.87/1.27  tff(c_115, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77, c_113])).
% 1.87/1.27  tff(c_117, plain, (~r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_24])).
% 1.87/1.27  tff(c_116, plain, (r2_hidden('#skF_1', k1_relat_1(k8_relat_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_24])).
% 1.87/1.27  tff(c_119, plain, (![A_41, C_42, B_43]: (r2_hidden(A_41, k1_relat_1(C_42)) | ~r2_hidden(A_41, k1_relat_1(k5_relat_1(C_42, k6_relat_1(B_43)))) | ~v1_funct_1(C_42) | ~v1_relat_1(C_42))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.87/1.27  tff(c_129, plain, (![A_47, B_48, A_49]: (r2_hidden(A_47, k1_relat_1(B_48)) | ~r2_hidden(A_47, k1_relat_1(k8_relat_1(A_49, B_48))) | ~v1_funct_1(B_48) | ~v1_relat_1(B_48) | ~v1_relat_1(B_48))), inference(superposition, [status(thm), theory('equality')], [c_2, c_119])).
% 1.87/1.27  tff(c_132, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_116, c_129])).
% 1.87/1.27  tff(c_135, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_10, c_132])).
% 1.87/1.27  tff(c_137, plain, $false, inference(negUnitSimplification, [status(thm)], [c_117, c_135])).
% 1.87/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.27  
% 1.87/1.27  Inference rules
% 1.87/1.27  ----------------------
% 1.87/1.27  #Ref     : 0
% 1.87/1.27  #Sup     : 20
% 1.87/1.27  #Fact    : 0
% 1.87/1.27  #Define  : 0
% 1.87/1.27  #Split   : 2
% 1.87/1.27  #Chain   : 0
% 1.87/1.27  #Close   : 0
% 1.87/1.27  
% 1.87/1.27  Ordering : KBO
% 1.87/1.27  
% 1.87/1.27  Simplification rules
% 1.87/1.27  ----------------------
% 1.87/1.27  #Subsume      : 2
% 1.87/1.27  #Demod        : 17
% 1.87/1.27  #Tautology    : 13
% 1.87/1.27  #SimpNegUnit  : 2
% 1.87/1.27  #BackRed      : 0
% 1.87/1.27  
% 1.87/1.27  #Partial instantiations: 0
% 1.87/1.28  #Strategies tried      : 1
% 1.87/1.28  
% 1.87/1.28  Timing (in seconds)
% 1.87/1.28  ----------------------
% 1.87/1.28  Preprocessing        : 0.29
% 1.87/1.28  Parsing              : 0.16
% 1.87/1.28  CNF conversion       : 0.02
% 1.87/1.28  Main loop            : 0.16
% 1.87/1.28  Inferencing          : 0.07
% 1.87/1.28  Reduction            : 0.04
% 1.87/1.28  Demodulation         : 0.03
% 1.87/1.28  BG Simplification    : 0.01
% 1.87/1.28  Subsumption          : 0.02
% 1.87/1.28  Abstraction          : 0.01
% 1.87/1.28  MUC search           : 0.00
% 1.87/1.28  Cooper               : 0.00
% 1.87/1.28  Total                : 0.48
% 1.87/1.28  Index Insertion      : 0.00
% 1.87/1.28  Index Deletion       : 0.00
% 1.87/1.28  Index Matching       : 0.00
% 1.87/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
