%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:22 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   45 (  76 expanded)
%              Number of leaves         :   22 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :   53 ( 126 expanded)
%              Number of equality atoms :   19 (  52 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & ~ ! [C] :
                ( m1_subset_1(C,k2_zfmisc_1(A,B))
               => C = k4_tarski(k1_mcart_1(C),k2_mcart_1(C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_mcart_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,k2_zfmisc_1(B,C))
        & ! [D,E] : k4_tarski(D,E) != A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_mcart_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ~ v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_subset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_16,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_14,plain,(
    m1_subset_1('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8,plain,(
    ! [A_9,B_10] :
      ( r2_hidden(A_9,B_10)
      | v1_xboole_0(B_10)
      | ~ m1_subset_1(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [A_2,B_3,C_4] :
      ( k4_tarski('#skF_1'(A_2,B_3,C_4),'#skF_2'(A_2,B_3,C_4)) = A_2
      | ~ r2_hidden(A_2,k2_zfmisc_1(B_3,C_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_47,plain,(
    ! [A_24,B_25,C_26] :
      ( k4_tarski('#skF_1'(A_24,B_25,C_26),'#skF_2'(A_24,B_25,C_26)) = A_24
      | ~ r2_hidden(A_24,k2_zfmisc_1(B_25,C_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_10,plain,(
    ! [B_14,C_15] : k4_tarski(k1_mcart_1(k4_tarski(B_14,C_15)),k2_mcart_1(k4_tarski(B_14,C_15))) = k4_tarski(B_14,C_15) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_62,plain,(
    ! [A_27,B_28,C_29] :
      ( k4_tarski(k1_mcart_1(A_27),k2_mcart_1(k4_tarski('#skF_1'(A_27,B_28,C_29),'#skF_2'(A_27,B_28,C_29)))) = k4_tarski('#skF_1'(A_27,B_28,C_29),'#skF_2'(A_27,B_28,C_29))
      | ~ r2_hidden(A_27,k2_zfmisc_1(B_28,C_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_10])).

tff(c_80,plain,(
    ! [A_30,B_31,C_32] :
      ( k4_tarski(k1_mcart_1(A_30),k2_mcart_1(A_30)) = k4_tarski('#skF_1'(A_30,B_31,C_32),'#skF_2'(A_30,B_31,C_32))
      | ~ r2_hidden(A_30,k2_zfmisc_1(B_31,C_32))
      | ~ r2_hidden(A_30,k2_zfmisc_1(B_31,C_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_62])).

tff(c_12,plain,(
    k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_125,plain,(
    ! [B_33,C_34] :
      ( k4_tarski('#skF_1'('#skF_5',B_33,C_34),'#skF_2'('#skF_5',B_33,C_34)) != '#skF_5'
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_33,C_34))
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(B_33,C_34)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_12])).

tff(c_135,plain,(
    ! [B_35,C_36] : ~ r2_hidden('#skF_5',k2_zfmisc_1(B_35,C_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_125])).

tff(c_140,plain,(
    ! [B_37,C_38] :
      ( v1_xboole_0(k2_zfmisc_1(B_37,C_38))
      | ~ m1_subset_1('#skF_5',k2_zfmisc_1(B_37,C_38)) ) ),
    inference(resolution,[status(thm)],[c_8,c_135])).

tff(c_144,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_14,c_140])).

tff(c_6,plain,(
    ! [A_7,B_8] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_7,B_8))
      | v1_xboole_0(B_8)
      | v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_151,plain,
    ( v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_144,c_6])).

tff(c_174,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_177,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_174,c_2])).

tff(c_181,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_177])).

tff(c_182,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_186,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_182,c_2])).

tff(c_190,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_186])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:22:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.20  
% 1.96/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.20  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 1.96/1.20  
% 1.96/1.20  %Foreground sorts:
% 1.96/1.20  
% 1.96/1.20  
% 1.96/1.20  %Background operators:
% 1.96/1.20  
% 1.96/1.20  
% 1.96/1.20  %Foreground operators:
% 1.96/1.20  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.96/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.96/1.20  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.96/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.96/1.20  tff('#skF_5', type, '#skF_5': $i).
% 1.96/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.96/1.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.96/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.20  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.96/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.96/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.96/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.20  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.96/1.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.96/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.96/1.20  
% 1.96/1.21  tff(f_70, negated_conjecture, ~(![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (C = k4_tarski(k1_mcart_1(C), k2_mcart_1(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_mcart_1)).
% 1.96/1.21  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 1.96/1.21  tff(f_36, axiom, (![A, B, C]: ~(r2_hidden(A, k2_zfmisc_1(B, C)) & (![D, E]: ~(k4_tarski(D, E) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 1.96/1.21  tff(f_56, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (k4_tarski(k1_mcart_1(A), k2_mcart_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_mcart_1)).
% 1.96/1.21  tff(f_45, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => ~v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_subset_1)).
% 1.96/1.21  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.96/1.21  tff(c_16, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.96/1.21  tff(c_18, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.96/1.21  tff(c_14, plain, (m1_subset_1('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.96/1.21  tff(c_8, plain, (![A_9, B_10]: (r2_hidden(A_9, B_10) | v1_xboole_0(B_10) | ~m1_subset_1(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.96/1.21  tff(c_4, plain, (![A_2, B_3, C_4]: (k4_tarski('#skF_1'(A_2, B_3, C_4), '#skF_2'(A_2, B_3, C_4))=A_2 | ~r2_hidden(A_2, k2_zfmisc_1(B_3, C_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.96/1.21  tff(c_47, plain, (![A_24, B_25, C_26]: (k4_tarski('#skF_1'(A_24, B_25, C_26), '#skF_2'(A_24, B_25, C_26))=A_24 | ~r2_hidden(A_24, k2_zfmisc_1(B_25, C_26)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.96/1.21  tff(c_10, plain, (![B_14, C_15]: (k4_tarski(k1_mcart_1(k4_tarski(B_14, C_15)), k2_mcart_1(k4_tarski(B_14, C_15)))=k4_tarski(B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.96/1.21  tff(c_62, plain, (![A_27, B_28, C_29]: (k4_tarski(k1_mcart_1(A_27), k2_mcart_1(k4_tarski('#skF_1'(A_27, B_28, C_29), '#skF_2'(A_27, B_28, C_29))))=k4_tarski('#skF_1'(A_27, B_28, C_29), '#skF_2'(A_27, B_28, C_29)) | ~r2_hidden(A_27, k2_zfmisc_1(B_28, C_29)))), inference(superposition, [status(thm), theory('equality')], [c_47, c_10])).
% 1.96/1.21  tff(c_80, plain, (![A_30, B_31, C_32]: (k4_tarski(k1_mcart_1(A_30), k2_mcart_1(A_30))=k4_tarski('#skF_1'(A_30, B_31, C_32), '#skF_2'(A_30, B_31, C_32)) | ~r2_hidden(A_30, k2_zfmisc_1(B_31, C_32)) | ~r2_hidden(A_30, k2_zfmisc_1(B_31, C_32)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_62])).
% 1.96/1.21  tff(c_12, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.96/1.21  tff(c_125, plain, (![B_33, C_34]: (k4_tarski('#skF_1'('#skF_5', B_33, C_34), '#skF_2'('#skF_5', B_33, C_34))!='#skF_5' | ~r2_hidden('#skF_5', k2_zfmisc_1(B_33, C_34)) | ~r2_hidden('#skF_5', k2_zfmisc_1(B_33, C_34)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_12])).
% 1.96/1.21  tff(c_135, plain, (![B_35, C_36]: (~r2_hidden('#skF_5', k2_zfmisc_1(B_35, C_36)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_125])).
% 1.96/1.21  tff(c_140, plain, (![B_37, C_38]: (v1_xboole_0(k2_zfmisc_1(B_37, C_38)) | ~m1_subset_1('#skF_5', k2_zfmisc_1(B_37, C_38)))), inference(resolution, [status(thm)], [c_8, c_135])).
% 1.96/1.21  tff(c_144, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_14, c_140])).
% 1.96/1.21  tff(c_6, plain, (![A_7, B_8]: (~v1_xboole_0(k2_zfmisc_1(A_7, B_8)) | v1_xboole_0(B_8) | v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.96/1.21  tff(c_151, plain, (v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_144, c_6])).
% 1.96/1.21  tff(c_174, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_151])).
% 1.96/1.21  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.96/1.21  tff(c_177, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_174, c_2])).
% 1.96/1.21  tff(c_181, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_177])).
% 1.96/1.21  tff(c_182, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_151])).
% 1.96/1.21  tff(c_186, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_182, c_2])).
% 1.96/1.21  tff(c_190, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_186])).
% 1.96/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.21  
% 1.96/1.21  Inference rules
% 1.96/1.21  ----------------------
% 1.96/1.21  #Ref     : 0
% 1.96/1.21  #Sup     : 43
% 1.96/1.21  #Fact    : 0
% 1.96/1.21  #Define  : 0
% 1.96/1.21  #Split   : 1
% 1.96/1.21  #Chain   : 0
% 1.96/1.21  #Close   : 0
% 1.96/1.21  
% 1.96/1.21  Ordering : KBO
% 1.96/1.21  
% 1.96/1.21  Simplification rules
% 1.96/1.21  ----------------------
% 1.96/1.21  #Subsume      : 5
% 1.96/1.21  #Demod        : 4
% 1.96/1.21  #Tautology    : 14
% 1.96/1.21  #SimpNegUnit  : 2
% 1.96/1.21  #BackRed      : 0
% 1.96/1.21  
% 1.96/1.21  #Partial instantiations: 0
% 1.96/1.21  #Strategies tried      : 1
% 1.96/1.21  
% 1.96/1.21  Timing (in seconds)
% 1.96/1.21  ----------------------
% 1.96/1.22  Preprocessing        : 0.28
% 1.96/1.22  Parsing              : 0.15
% 1.96/1.22  CNF conversion       : 0.02
% 1.96/1.22  Main loop            : 0.17
% 1.96/1.22  Inferencing          : 0.08
% 1.96/1.22  Reduction            : 0.05
% 1.96/1.22  Demodulation         : 0.04
% 1.96/1.22  BG Simplification    : 0.01
% 1.96/1.22  Subsumption          : 0.02
% 1.96/1.22  Abstraction          : 0.01
% 1.96/1.22  MUC search           : 0.00
% 1.96/1.22  Cooper               : 0.00
% 1.96/1.22  Total                : 0.48
% 1.96/1.22  Index Insertion      : 0.00
% 1.96/1.22  Index Deletion       : 0.00
% 1.96/1.22  Index Matching       : 0.00
% 1.96/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
