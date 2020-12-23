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
% DateTime   : Thu Dec  3 10:05:14 EST 2020

% Result     : Theorem 7.57s
% Output     : CNFRefutation 7.57s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 149 expanded)
%              Number of leaves         :   25 (  64 expanded)
%              Depth                    :   12
%              Number of atoms          :  111 ( 379 expanded)
%              Number of equality atoms :   15 (  42 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_39,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k7_relat_1(B,A)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_20,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_26,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_6,plain,(
    ! [A_6] : v1_relat_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_46,plain,(
    ! [A_28,B_29] :
      ( k5_relat_1(k6_relat_1(A_28),B_29) = k7_relat_1(B_29,A_28)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(k5_relat_1(A_4,B_5))
      | ~ v1_relat_1(B_5)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_52,plain,(
    ! [B_29,A_28] :
      ( v1_relat_1(k7_relat_1(B_29,A_28))
      | ~ v1_relat_1(B_29)
      | ~ v1_relat_1(k6_relat_1(A_28))
      | ~ v1_relat_1(B_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_4])).

tff(c_58,plain,(
    ! [B_29,A_28] :
      ( v1_relat_1(k7_relat_1(B_29,A_28))
      | ~ v1_relat_1(B_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_52])).

tff(c_24,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_22,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_201,plain,(
    ! [B_55,A_56] :
      ( k9_relat_1(B_55,k10_relat_1(B_55,A_56)) = A_56
      | ~ r1_tarski(A_56,k2_relat_1(B_55))
      | ~ v1_funct_1(B_55)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_216,plain,
    ( k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_1'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_201])).

tff(c_228,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_216])).

tff(c_10,plain,(
    ! [B_11,A_10] :
      ( k2_relat_1(k7_relat_1(B_11,A_10)) = k9_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_15,A_14)),k2_relat_1(B_15))
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_690,plain,(
    ! [B_83,A_84] :
      ( k9_relat_1(B_83,k10_relat_1(B_83,k2_relat_1(k7_relat_1(B_83,A_84)))) = k2_relat_1(k7_relat_1(B_83,A_84))
      | ~ v1_funct_1(B_83)
      | ~ v1_relat_1(B_83) ) ),
    inference(resolution,[status(thm)],[c_14,c_201])).

tff(c_5250,plain,(
    ! [B_202,A_203] :
      ( k9_relat_1(B_202,k10_relat_1(B_202,k9_relat_1(B_202,A_203))) = k2_relat_1(k7_relat_1(B_202,A_203))
      | ~ v1_funct_1(B_202)
      | ~ v1_relat_1(B_202)
      | ~ v1_relat_1(B_202) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_690])).

tff(c_5566,plain,
    ( k2_relat_1(k7_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1'))) = k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_5250])).

tff(c_5666,plain,(
    k2_relat_1(k7_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_26,c_228,c_5566])).

tff(c_8,plain,(
    ! [C_9,B_8,A_7] :
      ( k7_relat_1(k7_relat_1(C_9,B_8),A_7) = k7_relat_1(C_9,A_7)
      | ~ r1_tarski(A_7,B_8)
      | ~ v1_relat_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_65,plain,(
    ! [B_34,A_35] :
      ( k2_relat_1(k7_relat_1(B_34,A_35)) = k9_relat_1(B_34,A_35)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_408,plain,(
    ! [B_66,A_67,A_68] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(B_66,A_67),A_68)),k9_relat_1(B_66,A_67))
      | ~ v1_relat_1(k7_relat_1(B_66,A_67))
      | ~ v1_relat_1(B_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_14])).

tff(c_7325,plain,(
    ! [C_227,A_228,B_229] :
      ( r1_tarski(k2_relat_1(k7_relat_1(C_227,A_228)),k9_relat_1(C_227,B_229))
      | ~ v1_relat_1(k7_relat_1(C_227,B_229))
      | ~ v1_relat_1(C_227)
      | ~ r1_tarski(A_228,B_229)
      | ~ v1_relat_1(C_227) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_408])).

tff(c_7382,plain,(
    ! [B_229] :
      ( r1_tarski('#skF_1',k9_relat_1('#skF_3',B_229))
      | ~ v1_relat_1(k7_relat_1('#skF_3',B_229))
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),B_229)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5666,c_7325])).

tff(c_7463,plain,(
    ! [B_230] :
      ( r1_tarski('#skF_1',k9_relat_1('#skF_3',B_230))
      | ~ v1_relat_1(k7_relat_1('#skF_3',B_230))
      | ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),B_230) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_7382])).

tff(c_7487,plain,
    ( r1_tarski('#skF_1',k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2')))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_24,c_7463])).

tff(c_7488,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_7487])).

tff(c_7491,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_7488])).

tff(c_7495,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_7491])).

tff(c_7496,plain,(
    r1_tarski('#skF_1',k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_7487])).

tff(c_87,plain,(
    ! [B_38,A_39] :
      ( r1_tarski(k9_relat_1(B_38,k10_relat_1(B_38,A_39)),A_39)
      | ~ v1_funct_1(B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_90,plain,(
    ! [A_1,A_39,B_38] :
      ( r1_tarski(A_1,A_39)
      | ~ r1_tarski(A_1,k9_relat_1(B_38,k10_relat_1(B_38,A_39)))
      | ~ v1_funct_1(B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(resolution,[status(thm)],[c_87,c_2])).

tff(c_7516,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_7496,c_90])).

tff(c_7545,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_7516])).

tff(c_7547,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_7545])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:04:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.57/2.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.57/2.57  
% 7.57/2.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.57/2.57  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 7.57/2.57  
% 7.57/2.57  %Foreground sorts:
% 7.57/2.57  
% 7.57/2.57  
% 7.57/2.57  %Background operators:
% 7.57/2.57  
% 7.57/2.57  
% 7.57/2.57  %Foreground operators:
% 7.57/2.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.57/2.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.57/2.57  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.57/2.57  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.57/2.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.57/2.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.57/2.57  tff('#skF_2', type, '#skF_2': $i).
% 7.57/2.57  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.57/2.57  tff('#skF_3', type, '#skF_3': $i).
% 7.57/2.57  tff('#skF_1', type, '#skF_1': $i).
% 7.57/2.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.57/2.57  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.57/2.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.57/2.57  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.57/2.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.57/2.57  
% 7.57/2.59  tff(f_82, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_funct_1)).
% 7.57/2.59  tff(f_39, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 7.57/2.59  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 7.57/2.59  tff(f_37, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 7.57/2.59  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 7.57/2.59  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 7.57/2.59  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k7_relat_1(B, A)), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_relat_1)).
% 7.57/2.59  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_relat_1)).
% 7.57/2.59  tff(f_63, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 7.57/2.59  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 7.57/2.59  tff(c_20, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.57/2.59  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.57/2.59  tff(c_26, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.57/2.59  tff(c_6, plain, (![A_6]: (v1_relat_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.57/2.59  tff(c_46, plain, (![A_28, B_29]: (k5_relat_1(k6_relat_1(A_28), B_29)=k7_relat_1(B_29, A_28) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.57/2.59  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k5_relat_1(A_4, B_5)) | ~v1_relat_1(B_5) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.57/2.59  tff(c_52, plain, (![B_29, A_28]: (v1_relat_1(k7_relat_1(B_29, A_28)) | ~v1_relat_1(B_29) | ~v1_relat_1(k6_relat_1(A_28)) | ~v1_relat_1(B_29))), inference(superposition, [status(thm), theory('equality')], [c_46, c_4])).
% 7.57/2.59  tff(c_58, plain, (![B_29, A_28]: (v1_relat_1(k7_relat_1(B_29, A_28)) | ~v1_relat_1(B_29))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_52])).
% 7.57/2.59  tff(c_24, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.57/2.59  tff(c_22, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.57/2.59  tff(c_201, plain, (![B_55, A_56]: (k9_relat_1(B_55, k10_relat_1(B_55, A_56))=A_56 | ~r1_tarski(A_56, k2_relat_1(B_55)) | ~v1_funct_1(B_55) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.57/2.59  tff(c_216, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_1' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_201])).
% 7.57/2.59  tff(c_228, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_216])).
% 7.57/2.59  tff(c_10, plain, (![B_11, A_10]: (k2_relat_1(k7_relat_1(B_11, A_10))=k9_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.57/2.59  tff(c_14, plain, (![B_15, A_14]: (r1_tarski(k2_relat_1(k7_relat_1(B_15, A_14)), k2_relat_1(B_15)) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.57/2.59  tff(c_690, plain, (![B_83, A_84]: (k9_relat_1(B_83, k10_relat_1(B_83, k2_relat_1(k7_relat_1(B_83, A_84))))=k2_relat_1(k7_relat_1(B_83, A_84)) | ~v1_funct_1(B_83) | ~v1_relat_1(B_83))), inference(resolution, [status(thm)], [c_14, c_201])).
% 7.57/2.59  tff(c_5250, plain, (![B_202, A_203]: (k9_relat_1(B_202, k10_relat_1(B_202, k9_relat_1(B_202, A_203)))=k2_relat_1(k7_relat_1(B_202, A_203)) | ~v1_funct_1(B_202) | ~v1_relat_1(B_202) | ~v1_relat_1(B_202))), inference(superposition, [status(thm), theory('equality')], [c_10, c_690])).
% 7.57/2.59  tff(c_5566, plain, (k2_relat_1(k7_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1')))=k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_228, c_5250])).
% 7.57/2.59  tff(c_5666, plain, (k2_relat_1(k7_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_26, c_228, c_5566])).
% 7.57/2.59  tff(c_8, plain, (![C_9, B_8, A_7]: (k7_relat_1(k7_relat_1(C_9, B_8), A_7)=k7_relat_1(C_9, A_7) | ~r1_tarski(A_7, B_8) | ~v1_relat_1(C_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.57/2.59  tff(c_65, plain, (![B_34, A_35]: (k2_relat_1(k7_relat_1(B_34, A_35))=k9_relat_1(B_34, A_35) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.57/2.59  tff(c_408, plain, (![B_66, A_67, A_68]: (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(B_66, A_67), A_68)), k9_relat_1(B_66, A_67)) | ~v1_relat_1(k7_relat_1(B_66, A_67)) | ~v1_relat_1(B_66))), inference(superposition, [status(thm), theory('equality')], [c_65, c_14])).
% 7.57/2.59  tff(c_7325, plain, (![C_227, A_228, B_229]: (r1_tarski(k2_relat_1(k7_relat_1(C_227, A_228)), k9_relat_1(C_227, B_229)) | ~v1_relat_1(k7_relat_1(C_227, B_229)) | ~v1_relat_1(C_227) | ~r1_tarski(A_228, B_229) | ~v1_relat_1(C_227))), inference(superposition, [status(thm), theory('equality')], [c_8, c_408])).
% 7.57/2.59  tff(c_7382, plain, (![B_229]: (r1_tarski('#skF_1', k9_relat_1('#skF_3', B_229)) | ~v1_relat_1(k7_relat_1('#skF_3', B_229)) | ~v1_relat_1('#skF_3') | ~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), B_229) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_5666, c_7325])).
% 7.57/2.59  tff(c_7463, plain, (![B_230]: (r1_tarski('#skF_1', k9_relat_1('#skF_3', B_230)) | ~v1_relat_1(k7_relat_1('#skF_3', B_230)) | ~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), B_230))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_7382])).
% 7.57/2.59  tff(c_7487, plain, (r1_tarski('#skF_1', k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2'))) | ~v1_relat_1(k7_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_24, c_7463])).
% 7.57/2.59  tff(c_7488, plain, (~v1_relat_1(k7_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_7487])).
% 7.57/2.59  tff(c_7491, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_7488])).
% 7.57/2.59  tff(c_7495, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_7491])).
% 7.57/2.59  tff(c_7496, plain, (r1_tarski('#skF_1', k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_7487])).
% 7.57/2.59  tff(c_87, plain, (![B_38, A_39]: (r1_tarski(k9_relat_1(B_38, k10_relat_1(B_38, A_39)), A_39) | ~v1_funct_1(B_38) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.57/2.59  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.57/2.59  tff(c_90, plain, (![A_1, A_39, B_38]: (r1_tarski(A_1, A_39) | ~r1_tarski(A_1, k9_relat_1(B_38, k10_relat_1(B_38, A_39))) | ~v1_funct_1(B_38) | ~v1_relat_1(B_38))), inference(resolution, [status(thm)], [c_87, c_2])).
% 7.57/2.59  tff(c_7516, plain, (r1_tarski('#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_7496, c_90])).
% 7.57/2.59  tff(c_7545, plain, (r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_7516])).
% 7.57/2.59  tff(c_7547, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_7545])).
% 7.57/2.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.57/2.59  
% 7.57/2.59  Inference rules
% 7.57/2.59  ----------------------
% 7.57/2.59  #Ref     : 0
% 7.57/2.59  #Sup     : 1734
% 7.57/2.59  #Fact    : 0
% 7.57/2.59  #Define  : 0
% 7.57/2.59  #Split   : 8
% 7.57/2.59  #Chain   : 0
% 7.57/2.59  #Close   : 0
% 7.57/2.59  
% 7.57/2.59  Ordering : KBO
% 7.57/2.59  
% 7.57/2.59  Simplification rules
% 7.57/2.59  ----------------------
% 7.57/2.59  #Subsume      : 586
% 7.57/2.59  #Demod        : 1229
% 7.57/2.59  #Tautology    : 266
% 7.57/2.59  #SimpNegUnit  : 2
% 7.57/2.59  #BackRed      : 3
% 7.57/2.59  
% 7.57/2.59  #Partial instantiations: 0
% 7.57/2.59  #Strategies tried      : 1
% 7.57/2.59  
% 7.57/2.59  Timing (in seconds)
% 7.57/2.59  ----------------------
% 7.57/2.59  Preprocessing        : 0.32
% 7.57/2.59  Parsing              : 0.19
% 7.57/2.59  CNF conversion       : 0.02
% 7.57/2.59  Main loop            : 1.46
% 7.57/2.59  Inferencing          : 0.45
% 7.57/2.59  Reduction            : 0.49
% 7.57/2.59  Demodulation         : 0.35
% 7.57/2.59  BG Simplification    : 0.05
% 7.57/2.59  Subsumption          : 0.39
% 7.57/2.59  Abstraction          : 0.07
% 7.57/2.59  MUC search           : 0.00
% 7.57/2.59  Cooper               : 0.00
% 7.57/2.59  Total                : 1.81
% 7.57/2.59  Index Insertion      : 0.00
% 7.57/2.59  Index Deletion       : 0.00
% 7.57/2.59  Index Matching       : 0.00
% 7.57/2.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
