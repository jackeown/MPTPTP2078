%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:54 EST 2020

% Result     : Theorem 8.43s
% Output     : CNFRefutation 8.77s
% Verified   : 
% Statistics : Number of formulae       :   48 (  60 expanded)
%              Number of leaves         :   22 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :  110 ( 154 expanded)
%              Number of equality atoms :   17 (  25 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v2_funct_1(A)
              & r1_tarski(B,k1_relat_1(A)) )
           => k9_relat_1(k2_funct_1(A),k9_relat_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
          & r1_tarski(A,k1_relat_1(C))
          & v2_funct_1(C) )
       => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_26,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_24,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_68,plain,(
    ! [B_26,A_27] :
      ( k9_relat_1(k2_funct_1(B_26),A_27) = k10_relat_1(B_26,A_27)
      | ~ v2_funct_1(B_26)
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_20,plain,(
    k9_relat_1(k2_funct_1('#skF_1'),k9_relat_1('#skF_1','#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_87,plain,
    ( k10_relat_1('#skF_1',k9_relat_1('#skF_1','#skF_2')) != '#skF_2'
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_20])).

tff(c_97,plain,(
    k10_relat_1('#skF_1',k9_relat_1('#skF_1','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_87])).

tff(c_22,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_3] :
      ( k9_relat_1(A_3,k1_relat_1(A_3)) = k2_relat_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_51,plain,(
    ! [C_21,A_22,B_23] :
      ( r1_tarski(k9_relat_1(C_21,A_22),k9_relat_1(C_21,B_23))
      | ~ r1_tarski(A_22,B_23)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_182,plain,(
    ! [A_36,A_37] :
      ( r1_tarski(k9_relat_1(A_36,A_37),k2_relat_1(A_36))
      | ~ r1_tarski(A_37,k1_relat_1(A_36))
      | ~ v1_relat_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_51])).

tff(c_12,plain,(
    ! [B_8,A_7] :
      ( k9_relat_1(B_8,k10_relat_1(B_8,A_7)) = A_7
      | ~ r1_tarski(A_7,k2_relat_1(B_8))
      | ~ v1_funct_1(B_8)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_426,plain,(
    ! [A_61,A_62] :
      ( k9_relat_1(A_61,k10_relat_1(A_61,k9_relat_1(A_61,A_62))) = k9_relat_1(A_61,A_62)
      | ~ v1_funct_1(A_61)
      | ~ r1_tarski(A_62,k1_relat_1(A_61))
      | ~ v1_relat_1(A_61) ) ),
    inference(resolution,[status(thm)],[c_182,c_12])).

tff(c_10,plain,(
    ! [C_6,A_4,B_5] :
      ( r1_tarski(k9_relat_1(C_6,A_4),k9_relat_1(C_6,B_5))
      | ~ r1_tarski(A_4,B_5)
      | ~ v1_relat_1(C_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6467,plain,(
    ! [A_273,A_274,B_275] :
      ( r1_tarski(k9_relat_1(A_273,A_274),k9_relat_1(A_273,B_275))
      | ~ r1_tarski(k10_relat_1(A_273,k9_relat_1(A_273,A_274)),B_275)
      | ~ v1_relat_1(A_273)
      | ~ v1_funct_1(A_273)
      | ~ r1_tarski(A_274,k1_relat_1(A_273))
      | ~ v1_relat_1(A_273) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_426,c_10])).

tff(c_6667,plain,(
    ! [A_278,A_279] :
      ( r1_tarski(k9_relat_1(A_278,A_279),k9_relat_1(A_278,k10_relat_1(A_278,k9_relat_1(A_278,A_279))))
      | ~ v1_funct_1(A_278)
      | ~ r1_tarski(A_279,k1_relat_1(A_278))
      | ~ v1_relat_1(A_278) ) ),
    inference(resolution,[status(thm)],[c_6,c_6467])).

tff(c_18,plain,(
    ! [A_13,B_14,C_15] :
      ( r1_tarski(A_13,B_14)
      | ~ v2_funct_1(C_15)
      | ~ r1_tarski(A_13,k1_relat_1(C_15))
      | ~ r1_tarski(k9_relat_1(C_15,A_13),k9_relat_1(C_15,B_14))
      | ~ v1_funct_1(C_15)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_7058,plain,(
    ! [A_285,A_286] :
      ( r1_tarski(A_285,k10_relat_1(A_286,k9_relat_1(A_286,A_285)))
      | ~ v2_funct_1(A_286)
      | ~ v1_funct_1(A_286)
      | ~ r1_tarski(A_285,k1_relat_1(A_286))
      | ~ v1_relat_1(A_286) ) ),
    inference(resolution,[status(thm)],[c_6667,c_18])).

tff(c_61,plain,(
    ! [B_24,A_25] :
      ( r1_tarski(k10_relat_1(B_24,k9_relat_1(B_24,A_25)),A_25)
      | ~ v2_funct_1(B_24)
      | ~ v1_funct_1(B_24)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_67,plain,(
    ! [B_24,A_25] :
      ( k10_relat_1(B_24,k9_relat_1(B_24,A_25)) = A_25
      | ~ r1_tarski(A_25,k10_relat_1(B_24,k9_relat_1(B_24,A_25)))
      | ~ v2_funct_1(B_24)
      | ~ v1_funct_1(B_24)
      | ~ v1_relat_1(B_24) ) ),
    inference(resolution,[status(thm)],[c_61,c_2])).

tff(c_7233,plain,(
    ! [A_287,A_288] :
      ( k10_relat_1(A_287,k9_relat_1(A_287,A_288)) = A_288
      | ~ v2_funct_1(A_287)
      | ~ v1_funct_1(A_287)
      | ~ r1_tarski(A_288,k1_relat_1(A_287))
      | ~ v1_relat_1(A_287) ) ),
    inference(resolution,[status(thm)],[c_7058,c_67])).

tff(c_7243,plain,
    ( k10_relat_1('#skF_1',k9_relat_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_7233])).

tff(c_7252,plain,(
    k10_relat_1('#skF_1',k9_relat_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_7243])).

tff(c_7254,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_7252])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:04:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.43/2.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.77/2.84  
% 8.77/2.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.77/2.84  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 8.77/2.84  
% 8.77/2.84  %Foreground sorts:
% 8.77/2.84  
% 8.77/2.84  
% 8.77/2.84  %Background operators:
% 8.77/2.84  
% 8.77/2.84  
% 8.77/2.84  %Foreground operators:
% 8.77/2.84  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.77/2.84  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.77/2.84  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.77/2.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.77/2.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.77/2.84  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.77/2.84  tff('#skF_2', type, '#skF_2': $i).
% 8.77/2.84  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.77/2.84  tff('#skF_1', type, '#skF_1': $i).
% 8.77/2.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.77/2.84  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 8.77/2.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.77/2.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.77/2.84  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.77/2.84  
% 8.77/2.85  tff(f_89, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v2_funct_1(A) & r1_tarski(B, k1_relat_1(A))) => (k9_relat_1(k2_funct_1(A), k9_relat_1(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t177_funct_1)).
% 8.77/2.85  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 8.77/2.85  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.77/2.85  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 8.77/2.85  tff(f_41, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 8.77/2.85  tff(f_49, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 8.77/2.85  tff(f_77, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t157_funct_1)).
% 8.77/2.85  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_funct_1)).
% 8.77/2.85  tff(c_28, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.77/2.85  tff(c_26, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.77/2.85  tff(c_24, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.77/2.85  tff(c_68, plain, (![B_26, A_27]: (k9_relat_1(k2_funct_1(B_26), A_27)=k10_relat_1(B_26, A_27) | ~v2_funct_1(B_26) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.77/2.85  tff(c_20, plain, (k9_relat_1(k2_funct_1('#skF_1'), k9_relat_1('#skF_1', '#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.77/2.85  tff(c_87, plain, (k10_relat_1('#skF_1', k9_relat_1('#skF_1', '#skF_2'))!='#skF_2' | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_68, c_20])).
% 8.77/2.85  tff(c_97, plain, (k10_relat_1('#skF_1', k9_relat_1('#skF_1', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_87])).
% 8.77/2.85  tff(c_22, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.77/2.85  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.77/2.85  tff(c_8, plain, (![A_3]: (k9_relat_1(A_3, k1_relat_1(A_3))=k2_relat_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.77/2.85  tff(c_51, plain, (![C_21, A_22, B_23]: (r1_tarski(k9_relat_1(C_21, A_22), k9_relat_1(C_21, B_23)) | ~r1_tarski(A_22, B_23) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.77/2.85  tff(c_182, plain, (![A_36, A_37]: (r1_tarski(k9_relat_1(A_36, A_37), k2_relat_1(A_36)) | ~r1_tarski(A_37, k1_relat_1(A_36)) | ~v1_relat_1(A_36) | ~v1_relat_1(A_36))), inference(superposition, [status(thm), theory('equality')], [c_8, c_51])).
% 8.77/2.85  tff(c_12, plain, (![B_8, A_7]: (k9_relat_1(B_8, k10_relat_1(B_8, A_7))=A_7 | ~r1_tarski(A_7, k2_relat_1(B_8)) | ~v1_funct_1(B_8) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.77/2.85  tff(c_426, plain, (![A_61, A_62]: (k9_relat_1(A_61, k10_relat_1(A_61, k9_relat_1(A_61, A_62)))=k9_relat_1(A_61, A_62) | ~v1_funct_1(A_61) | ~r1_tarski(A_62, k1_relat_1(A_61)) | ~v1_relat_1(A_61))), inference(resolution, [status(thm)], [c_182, c_12])).
% 8.77/2.85  tff(c_10, plain, (![C_6, A_4, B_5]: (r1_tarski(k9_relat_1(C_6, A_4), k9_relat_1(C_6, B_5)) | ~r1_tarski(A_4, B_5) | ~v1_relat_1(C_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.77/2.85  tff(c_6467, plain, (![A_273, A_274, B_275]: (r1_tarski(k9_relat_1(A_273, A_274), k9_relat_1(A_273, B_275)) | ~r1_tarski(k10_relat_1(A_273, k9_relat_1(A_273, A_274)), B_275) | ~v1_relat_1(A_273) | ~v1_funct_1(A_273) | ~r1_tarski(A_274, k1_relat_1(A_273)) | ~v1_relat_1(A_273))), inference(superposition, [status(thm), theory('equality')], [c_426, c_10])).
% 8.77/2.85  tff(c_6667, plain, (![A_278, A_279]: (r1_tarski(k9_relat_1(A_278, A_279), k9_relat_1(A_278, k10_relat_1(A_278, k9_relat_1(A_278, A_279)))) | ~v1_funct_1(A_278) | ~r1_tarski(A_279, k1_relat_1(A_278)) | ~v1_relat_1(A_278))), inference(resolution, [status(thm)], [c_6, c_6467])).
% 8.77/2.85  tff(c_18, plain, (![A_13, B_14, C_15]: (r1_tarski(A_13, B_14) | ~v2_funct_1(C_15) | ~r1_tarski(A_13, k1_relat_1(C_15)) | ~r1_tarski(k9_relat_1(C_15, A_13), k9_relat_1(C_15, B_14)) | ~v1_funct_1(C_15) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.77/2.85  tff(c_7058, plain, (![A_285, A_286]: (r1_tarski(A_285, k10_relat_1(A_286, k9_relat_1(A_286, A_285))) | ~v2_funct_1(A_286) | ~v1_funct_1(A_286) | ~r1_tarski(A_285, k1_relat_1(A_286)) | ~v1_relat_1(A_286))), inference(resolution, [status(thm)], [c_6667, c_18])).
% 8.77/2.85  tff(c_61, plain, (![B_24, A_25]: (r1_tarski(k10_relat_1(B_24, k9_relat_1(B_24, A_25)), A_25) | ~v2_funct_1(B_24) | ~v1_funct_1(B_24) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.77/2.85  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.77/2.85  tff(c_67, plain, (![B_24, A_25]: (k10_relat_1(B_24, k9_relat_1(B_24, A_25))=A_25 | ~r1_tarski(A_25, k10_relat_1(B_24, k9_relat_1(B_24, A_25))) | ~v2_funct_1(B_24) | ~v1_funct_1(B_24) | ~v1_relat_1(B_24))), inference(resolution, [status(thm)], [c_61, c_2])).
% 8.77/2.85  tff(c_7233, plain, (![A_287, A_288]: (k10_relat_1(A_287, k9_relat_1(A_287, A_288))=A_288 | ~v2_funct_1(A_287) | ~v1_funct_1(A_287) | ~r1_tarski(A_288, k1_relat_1(A_287)) | ~v1_relat_1(A_287))), inference(resolution, [status(thm)], [c_7058, c_67])).
% 8.77/2.85  tff(c_7243, plain, (k10_relat_1('#skF_1', k9_relat_1('#skF_1', '#skF_2'))='#skF_2' | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_22, c_7233])).
% 8.77/2.85  tff(c_7252, plain, (k10_relat_1('#skF_1', k9_relat_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_7243])).
% 8.77/2.85  tff(c_7254, plain, $false, inference(negUnitSimplification, [status(thm)], [c_97, c_7252])).
% 8.77/2.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.77/2.85  
% 8.77/2.85  Inference rules
% 8.77/2.85  ----------------------
% 8.77/2.85  #Ref     : 0
% 8.77/2.85  #Sup     : 1931
% 8.77/2.85  #Fact    : 0
% 8.77/2.85  #Define  : 0
% 8.77/2.85  #Split   : 1
% 8.77/2.85  #Chain   : 0
% 8.77/2.85  #Close   : 0
% 8.77/2.85  
% 8.77/2.85  Ordering : KBO
% 8.77/2.85  
% 8.77/2.85  Simplification rules
% 8.77/2.85  ----------------------
% 8.77/2.85  #Subsume      : 538
% 8.77/2.85  #Demod        : 344
% 8.77/2.85  #Tautology    : 259
% 8.77/2.85  #SimpNegUnit  : 1
% 8.77/2.85  #BackRed      : 0
% 8.77/2.85  
% 8.77/2.85  #Partial instantiations: 0
% 8.77/2.85  #Strategies tried      : 1
% 8.77/2.85  
% 8.77/2.85  Timing (in seconds)
% 8.77/2.85  ----------------------
% 8.77/2.86  Preprocessing        : 0.28
% 8.77/2.86  Parsing              : 0.16
% 8.77/2.86  CNF conversion       : 0.02
% 8.77/2.86  Main loop            : 1.82
% 8.77/2.86  Inferencing          : 0.57
% 8.77/2.86  Reduction            : 0.42
% 8.77/2.86  Demodulation         : 0.28
% 8.77/2.86  BG Simplification    : 0.07
% 8.77/2.86  Subsumption          : 0.66
% 8.77/2.86  Abstraction          : 0.09
% 8.77/2.86  MUC search           : 0.00
% 8.77/2.86  Cooper               : 0.00
% 8.77/2.86  Total                : 2.13
% 8.77/2.86  Index Insertion      : 0.00
% 8.77/2.86  Index Deletion       : 0.00
% 8.77/2.86  Index Matching       : 0.00
% 8.77/2.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
