%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:21 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 147 expanded)
%              Number of leaves         :   22 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :   80 ( 319 expanded)
%              Number of equality atoms :   41 ( 108 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & ~ ! [C] :
                ( m1_subset_1(C,k2_zfmisc_1(A,B))
               => C = k4_tarski(k1_mcart_1(C),k2_mcart_1(C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_mcart_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,k2_zfmisc_1(B,C))
        & ! [D,E] : k4_tarski(D,E) != A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_75,plain,(
    ! [B_25,A_26] :
      ( v1_xboole_0(B_25)
      | ~ m1_subset_1(B_25,A_26)
      | ~ v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_79,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_28,c_75])).

tff(c_80,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( r2_hidden(B_12,A_11)
      | ~ m1_subset_1(B_12,A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] :
      ( k4_tarski('#skF_1'(A_4,B_5,C_6),'#skF_2'(A_4,B_5,C_6)) = A_4
      | ~ r2_hidden(A_4,k2_zfmisc_1(B_5,C_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_103,plain,(
    ! [A_35,B_36,C_37] :
      ( k4_tarski('#skF_1'(A_35,B_36,C_37),'#skF_2'(A_35,B_36,C_37)) = A_35
      | ~ r2_hidden(A_35,k2_zfmisc_1(B_36,C_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    ! [A_13,B_14] : k2_mcart_1(k4_tarski(A_13,B_14)) = B_14 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_144,plain,(
    ! [A_43,B_44,C_45] :
      ( k2_mcart_1(A_43) = '#skF_2'(A_43,B_44,C_45)
      | ~ r2_hidden(A_43,k2_zfmisc_1(B_44,C_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_24])).

tff(c_265,plain,(
    ! [B_71,B_72,C_73] :
      ( k2_mcart_1(B_71) = '#skF_2'(B_71,B_72,C_73)
      | ~ m1_subset_1(B_71,k2_zfmisc_1(B_72,C_73))
      | v1_xboole_0(k2_zfmisc_1(B_72,C_73)) ) ),
    inference(resolution,[status(thm)],[c_16,c_144])).

tff(c_272,plain,
    ( k2_mcart_1('#skF_5') = '#skF_2'('#skF_5','#skF_3','#skF_4')
    | v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_28,c_265])).

tff(c_282,plain,(
    k2_mcart_1('#skF_5') = '#skF_2'('#skF_5','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_272])).

tff(c_22,plain,(
    ! [A_13,B_14] : k1_mcart_1(k4_tarski(A_13,B_14)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_175,plain,(
    ! [A_52,B_53,C_54] :
      ( k1_mcart_1(A_52) = '#skF_1'(A_52,B_53,C_54)
      | ~ r2_hidden(A_52,k2_zfmisc_1(B_53,C_54)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_22])).

tff(c_238,plain,(
    ! [B_68,B_69,C_70] :
      ( k1_mcart_1(B_68) = '#skF_1'(B_68,B_69,C_70)
      | ~ m1_subset_1(B_68,k2_zfmisc_1(B_69,C_70))
      | v1_xboole_0(k2_zfmisc_1(B_69,C_70)) ) ),
    inference(resolution,[status(thm)],[c_16,c_175])).

tff(c_245,plain,
    ( k1_mcart_1('#skF_5') = '#skF_1'('#skF_5','#skF_3','#skF_4')
    | v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_28,c_238])).

tff(c_255,plain,(
    k1_mcart_1('#skF_5') = '#skF_1'('#skF_5','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_245])).

tff(c_26,plain,(
    k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_260,plain,(
    k4_tarski('#skF_1'('#skF_5','#skF_3','#skF_4'),k2_mcart_1('#skF_5')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_26])).

tff(c_287,plain,(
    k4_tarski('#skF_1'('#skF_5','#skF_3','#skF_4'),'#skF_2'('#skF_5','#skF_3','#skF_4')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_260])).

tff(c_295,plain,(
    ~ r2_hidden('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_287])).

tff(c_298,plain,
    ( ~ m1_subset_1('#skF_5',k2_zfmisc_1('#skF_3','#skF_4'))
    | v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_16,c_295])).

tff(c_301,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_298])).

tff(c_303,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_301])).

tff(c_304,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_309,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_304,c_2])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_319,plain,(
    '#skF_5' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_32])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_318,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_30])).

tff(c_305,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_331,plain,(
    ! [A_77] :
      ( A_77 = '#skF_5'
      | ~ v1_xboole_0(A_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_2])).

tff(c_338,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_305,c_331])).

tff(c_8,plain,(
    ! [B_10,A_9] :
      ( k1_xboole_0 = B_10
      | k1_xboole_0 = A_9
      | k2_zfmisc_1(A_9,B_10) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_376,plain,(
    ! [B_83,A_84] :
      ( B_83 = '#skF_5'
      | A_84 = '#skF_5'
      | k2_zfmisc_1(A_84,B_83) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_309,c_309,c_8])).

tff(c_379,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_376])).

tff(c_389,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_319,c_318,c_379])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:22:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.25  
% 2.09/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.25  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 2.09/1.25  
% 2.09/1.25  %Foreground sorts:
% 2.09/1.25  
% 2.09/1.25  
% 2.09/1.25  %Background operators:
% 2.09/1.25  
% 2.09/1.25  
% 2.09/1.25  %Foreground operators:
% 2.09/1.25  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.09/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.25  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.09/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.09/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.09/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.09/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.25  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.09/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.09/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.09/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.25  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.09/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.09/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.09/1.25  
% 2.09/1.27  tff(f_76, negated_conjecture, ~(![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (C = k4_tarski(k1_mcart_1(C), k2_mcart_1(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_mcart_1)).
% 2.09/1.27  tff(f_58, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.09/1.27  tff(f_39, axiom, (![A, B, C]: ~(r2_hidden(A, k2_zfmisc_1(B, C)) & (![D, E]: ~(k4_tarski(D, E) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 2.09/1.27  tff(f_62, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.09/1.27  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.09/1.27  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.09/1.27  tff(c_28, plain, (m1_subset_1('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.09/1.27  tff(c_75, plain, (![B_25, A_26]: (v1_xboole_0(B_25) | ~m1_subset_1(B_25, A_26) | ~v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.09/1.27  tff(c_79, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_28, c_75])).
% 2.09/1.27  tff(c_80, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_79])).
% 2.09/1.27  tff(c_16, plain, (![B_12, A_11]: (r2_hidden(B_12, A_11) | ~m1_subset_1(B_12, A_11) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.09/1.27  tff(c_6, plain, (![A_4, B_5, C_6]: (k4_tarski('#skF_1'(A_4, B_5, C_6), '#skF_2'(A_4, B_5, C_6))=A_4 | ~r2_hidden(A_4, k2_zfmisc_1(B_5, C_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.09/1.27  tff(c_103, plain, (![A_35, B_36, C_37]: (k4_tarski('#skF_1'(A_35, B_36, C_37), '#skF_2'(A_35, B_36, C_37))=A_35 | ~r2_hidden(A_35, k2_zfmisc_1(B_36, C_37)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.09/1.27  tff(c_24, plain, (![A_13, B_14]: (k2_mcart_1(k4_tarski(A_13, B_14))=B_14)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.09/1.27  tff(c_144, plain, (![A_43, B_44, C_45]: (k2_mcart_1(A_43)='#skF_2'(A_43, B_44, C_45) | ~r2_hidden(A_43, k2_zfmisc_1(B_44, C_45)))), inference(superposition, [status(thm), theory('equality')], [c_103, c_24])).
% 2.09/1.27  tff(c_265, plain, (![B_71, B_72, C_73]: (k2_mcart_1(B_71)='#skF_2'(B_71, B_72, C_73) | ~m1_subset_1(B_71, k2_zfmisc_1(B_72, C_73)) | v1_xboole_0(k2_zfmisc_1(B_72, C_73)))), inference(resolution, [status(thm)], [c_16, c_144])).
% 2.09/1.27  tff(c_272, plain, (k2_mcart_1('#skF_5')='#skF_2'('#skF_5', '#skF_3', '#skF_4') | v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_28, c_265])).
% 2.09/1.27  tff(c_282, plain, (k2_mcart_1('#skF_5')='#skF_2'('#skF_5', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_80, c_272])).
% 2.09/1.27  tff(c_22, plain, (![A_13, B_14]: (k1_mcart_1(k4_tarski(A_13, B_14))=A_13)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.09/1.27  tff(c_175, plain, (![A_52, B_53, C_54]: (k1_mcart_1(A_52)='#skF_1'(A_52, B_53, C_54) | ~r2_hidden(A_52, k2_zfmisc_1(B_53, C_54)))), inference(superposition, [status(thm), theory('equality')], [c_103, c_22])).
% 2.09/1.27  tff(c_238, plain, (![B_68, B_69, C_70]: (k1_mcart_1(B_68)='#skF_1'(B_68, B_69, C_70) | ~m1_subset_1(B_68, k2_zfmisc_1(B_69, C_70)) | v1_xboole_0(k2_zfmisc_1(B_69, C_70)))), inference(resolution, [status(thm)], [c_16, c_175])).
% 2.09/1.27  tff(c_245, plain, (k1_mcart_1('#skF_5')='#skF_1'('#skF_5', '#skF_3', '#skF_4') | v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_28, c_238])).
% 2.09/1.27  tff(c_255, plain, (k1_mcart_1('#skF_5')='#skF_1'('#skF_5', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_80, c_245])).
% 2.09/1.27  tff(c_26, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.09/1.27  tff(c_260, plain, (k4_tarski('#skF_1'('#skF_5', '#skF_3', '#skF_4'), k2_mcart_1('#skF_5'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_255, c_26])).
% 2.09/1.27  tff(c_287, plain, (k4_tarski('#skF_1'('#skF_5', '#skF_3', '#skF_4'), '#skF_2'('#skF_5', '#skF_3', '#skF_4'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_282, c_260])).
% 2.09/1.27  tff(c_295, plain, (~r2_hidden('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6, c_287])).
% 2.09/1.27  tff(c_298, plain, (~m1_subset_1('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4')) | v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_16, c_295])).
% 2.09/1.27  tff(c_301, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_298])).
% 2.09/1.27  tff(c_303, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_301])).
% 2.09/1.27  tff(c_304, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_79])).
% 2.09/1.27  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.09/1.27  tff(c_309, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_304, c_2])).
% 2.09/1.27  tff(c_32, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.09/1.27  tff(c_319, plain, ('#skF_5'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_309, c_32])).
% 2.09/1.27  tff(c_30, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.09/1.27  tff(c_318, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_309, c_30])).
% 2.09/1.27  tff(c_305, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_79])).
% 2.09/1.27  tff(c_331, plain, (![A_77]: (A_77='#skF_5' | ~v1_xboole_0(A_77))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_2])).
% 2.09/1.27  tff(c_338, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_305, c_331])).
% 2.09/1.27  tff(c_8, plain, (![B_10, A_9]: (k1_xboole_0=B_10 | k1_xboole_0=A_9 | k2_zfmisc_1(A_9, B_10)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.09/1.27  tff(c_376, plain, (![B_83, A_84]: (B_83='#skF_5' | A_84='#skF_5' | k2_zfmisc_1(A_84, B_83)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_309, c_309, c_309, c_8])).
% 2.09/1.27  tff(c_379, plain, ('#skF_5'='#skF_4' | '#skF_5'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_338, c_376])).
% 2.09/1.27  tff(c_389, plain, $false, inference(negUnitSimplification, [status(thm)], [c_319, c_318, c_379])).
% 2.09/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.27  
% 2.09/1.27  Inference rules
% 2.09/1.27  ----------------------
% 2.09/1.27  #Ref     : 0
% 2.09/1.27  #Sup     : 76
% 2.09/1.27  #Fact    : 0
% 2.09/1.27  #Define  : 0
% 2.09/1.27  #Split   : 3
% 2.09/1.27  #Chain   : 0
% 2.09/1.27  #Close   : 0
% 2.09/1.27  
% 2.09/1.27  Ordering : KBO
% 2.09/1.27  
% 2.09/1.27  Simplification rules
% 2.09/1.27  ----------------------
% 2.09/1.27  #Subsume      : 11
% 2.09/1.27  #Demod        : 24
% 2.09/1.27  #Tautology    : 38
% 2.09/1.27  #SimpNegUnit  : 15
% 2.09/1.27  #BackRed      : 9
% 2.09/1.27  
% 2.09/1.27  #Partial instantiations: 0
% 2.09/1.27  #Strategies tried      : 1
% 2.09/1.27  
% 2.09/1.27  Timing (in seconds)
% 2.09/1.27  ----------------------
% 2.09/1.27  Preprocessing        : 0.29
% 2.09/1.27  Parsing              : 0.16
% 2.09/1.27  CNF conversion       : 0.02
% 2.09/1.27  Main loop            : 0.22
% 2.09/1.27  Inferencing          : 0.08
% 2.09/1.27  Reduction            : 0.06
% 2.09/1.27  Demodulation         : 0.04
% 2.09/1.27  BG Simplification    : 0.01
% 2.09/1.27  Subsumption          : 0.03
% 2.09/1.27  Abstraction          : 0.01
% 2.09/1.27  MUC search           : 0.00
% 2.09/1.27  Cooper               : 0.00
% 2.09/1.27  Total                : 0.54
% 2.09/1.27  Index Insertion      : 0.00
% 2.09/1.27  Index Deletion       : 0.00
% 2.09/1.27  Index Matching       : 0.00
% 2.09/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
