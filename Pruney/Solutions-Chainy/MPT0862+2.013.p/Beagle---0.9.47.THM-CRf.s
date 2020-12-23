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
% DateTime   : Thu Dec  3 10:09:06 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 148 expanded)
%              Number of leaves         :   24 (  60 expanded)
%              Depth                    :    8
%              Number of atoms          :   73 ( 310 expanded)
%              Number of equality atoms :   22 (  84 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),k2_tarski(C,D)))
       => ( k1_mcart_1(A) = B
          & ( k2_mcart_1(A) = C
            | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_mcart_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
     => ( k1_mcart_1(A) = B
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C)
        & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(c_44,plain,
    ( k2_mcart_1('#skF_3') != '#skF_6'
    | k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_56,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_42,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k1_tarski('#skF_4'),k2_tarski('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_82,plain,(
    ! [A_42,B_43,C_44] :
      ( k1_mcart_1(A_42) = B_43
      | ~ r2_hidden(A_42,k2_zfmisc_1(k1_tarski(B_43),C_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_85,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_42,c_82])).

tff(c_89,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_85])).

tff(c_90,plain,(
    k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_91,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_46,plain,
    ( k2_mcart_1('#skF_3') != '#skF_5'
    | k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_98,plain,(
    k2_mcart_1('#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_46])).

tff(c_125,plain,(
    ! [A_61,C_62,B_63] :
      ( r2_hidden(k2_mcart_1(A_61),C_62)
      | ~ r2_hidden(A_61,k2_zfmisc_1(B_63,C_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_128,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),k2_tarski('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_42,c_125])).

tff(c_154,plain,(
    ! [D_73,A_74,B_75] :
      ( r2_hidden(D_73,k4_xboole_0(A_74,B_75))
      | r2_hidden(D_73,B_75)
      | ~ r2_hidden(D_73,A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,(
    ! [C_18,B_17] : ~ r2_hidden(C_18,k4_xboole_0(B_17,k1_tarski(C_18))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_168,plain,(
    ! [D_76,A_77] :
      ( r2_hidden(D_76,k1_tarski(D_76))
      | ~ r2_hidden(D_76,A_77) ) ),
    inference(resolution,[status(thm)],[c_154,c_30])).

tff(c_183,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),k1_tarski(k2_mcart_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_128,c_168])).

tff(c_201,plain,(
    ! [C_78,A_79,B_80] :
      ( k4_xboole_0(C_78,k2_tarski(A_79,B_80)) = C_78
      | r2_hidden(B_80,C_78)
      | r2_hidden(A_79,C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_325,plain,(
    ! [D_89,A_90,B_91,C_92] :
      ( ~ r2_hidden(D_89,k2_tarski(A_90,B_91))
      | ~ r2_hidden(D_89,C_92)
      | r2_hidden(B_91,C_92)
      | r2_hidden(A_90,C_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_4])).

tff(c_339,plain,(
    ! [C_93] :
      ( ~ r2_hidden(k2_mcart_1('#skF_3'),C_93)
      | r2_hidden('#skF_6',C_93)
      | r2_hidden('#skF_5',C_93) ) ),
    inference(resolution,[status(thm)],[c_128,c_325])).

tff(c_354,plain,
    ( r2_hidden('#skF_6',k1_tarski(k2_mcart_1('#skF_3')))
    | r2_hidden('#skF_5',k1_tarski(k2_mcart_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_183,c_339])).

tff(c_376,plain,(
    r2_hidden('#skF_5',k1_tarski(k2_mcart_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_354])).

tff(c_134,plain,(
    ! [A_67,B_68,C_69] :
      ( r2_hidden(A_67,k4_xboole_0(B_68,k1_tarski(C_69)))
      | C_69 = A_67
      | ~ r2_hidden(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_146,plain,(
    ! [A_67,C_69,B_68] :
      ( ~ r2_hidden(A_67,k1_tarski(C_69))
      | C_69 = A_67
      | ~ r2_hidden(A_67,B_68) ) ),
    inference(resolution,[status(thm)],[c_134,c_4])).

tff(c_382,plain,(
    ! [B_68] :
      ( k2_mcart_1('#skF_3') = '#skF_5'
      | ~ r2_hidden('#skF_5',B_68) ) ),
    inference(resolution,[status(thm)],[c_376,c_146])).

tff(c_388,plain,(
    ! [B_68] : ~ r2_hidden('#skF_5',B_68) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_382])).

tff(c_393,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_388,c_376])).

tff(c_394,plain,(
    r2_hidden('#skF_6',k1_tarski(k2_mcart_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_354])).

tff(c_414,plain,(
    ! [B_68] :
      ( k2_mcart_1('#skF_3') = '#skF_6'
      | ~ r2_hidden('#skF_6',B_68) ) ),
    inference(resolution,[status(thm)],[c_394,c_146])).

tff(c_419,plain,(
    ! [B_68] : ~ r2_hidden('#skF_6',B_68) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_414])).

tff(c_422,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_419,c_394])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:20:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.33  
% 2.05/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.33  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 2.05/1.33  
% 2.05/1.33  %Foreground sorts:
% 2.05/1.33  
% 2.05/1.33  
% 2.05/1.33  %Background operators:
% 2.05/1.33  
% 2.05/1.33  
% 2.05/1.33  %Foreground operators:
% 2.05/1.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.05/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.05/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.05/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.05/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.05/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.05/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.05/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.05/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.05/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.05/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.05/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.33  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.05/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.05/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.05/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.33  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.05/1.33  
% 2.45/1.34  tff(f_79, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), k2_tarski(C, D))) => ((k1_mcart_1(A) = B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_mcart_1)).
% 2.45/1.34  tff(f_70, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_mcart_1)).
% 2.45/1.34  tff(f_64, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.45/1.34  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.45/1.34  tff(f_58, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.45/1.34  tff(f_51, axiom, (![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 2.45/1.34  tff(c_44, plain, (k2_mcart_1('#skF_3')!='#skF_6' | k1_mcart_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.45/1.34  tff(c_56, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_44])).
% 2.45/1.34  tff(c_42, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k1_tarski('#skF_4'), k2_tarski('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.45/1.34  tff(c_82, plain, (![A_42, B_43, C_44]: (k1_mcart_1(A_42)=B_43 | ~r2_hidden(A_42, k2_zfmisc_1(k1_tarski(B_43), C_44)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.45/1.34  tff(c_85, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_42, c_82])).
% 2.45/1.34  tff(c_89, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_85])).
% 2.45/1.34  tff(c_90, plain, (k2_mcart_1('#skF_3')!='#skF_6'), inference(splitRight, [status(thm)], [c_44])).
% 2.45/1.35  tff(c_91, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_44])).
% 2.45/1.35  tff(c_46, plain, (k2_mcart_1('#skF_3')!='#skF_5' | k1_mcart_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.45/1.35  tff(c_98, plain, (k2_mcart_1('#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_91, c_46])).
% 2.45/1.35  tff(c_125, plain, (![A_61, C_62, B_63]: (r2_hidden(k2_mcart_1(A_61), C_62) | ~r2_hidden(A_61, k2_zfmisc_1(B_63, C_62)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.45/1.35  tff(c_128, plain, (r2_hidden(k2_mcart_1('#skF_3'), k2_tarski('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_42, c_125])).
% 2.45/1.35  tff(c_154, plain, (![D_73, A_74, B_75]: (r2_hidden(D_73, k4_xboole_0(A_74, B_75)) | r2_hidden(D_73, B_75) | ~r2_hidden(D_73, A_74))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.45/1.35  tff(c_30, plain, (![C_18, B_17]: (~r2_hidden(C_18, k4_xboole_0(B_17, k1_tarski(C_18))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.45/1.35  tff(c_168, plain, (![D_76, A_77]: (r2_hidden(D_76, k1_tarski(D_76)) | ~r2_hidden(D_76, A_77))), inference(resolution, [status(thm)], [c_154, c_30])).
% 2.45/1.35  tff(c_183, plain, (r2_hidden(k2_mcart_1('#skF_3'), k1_tarski(k2_mcart_1('#skF_3')))), inference(resolution, [status(thm)], [c_128, c_168])).
% 2.45/1.35  tff(c_201, plain, (![C_78, A_79, B_80]: (k4_xboole_0(C_78, k2_tarski(A_79, B_80))=C_78 | r2_hidden(B_80, C_78) | r2_hidden(A_79, C_78))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.45/1.35  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.45/1.35  tff(c_325, plain, (![D_89, A_90, B_91, C_92]: (~r2_hidden(D_89, k2_tarski(A_90, B_91)) | ~r2_hidden(D_89, C_92) | r2_hidden(B_91, C_92) | r2_hidden(A_90, C_92))), inference(superposition, [status(thm), theory('equality')], [c_201, c_4])).
% 2.45/1.35  tff(c_339, plain, (![C_93]: (~r2_hidden(k2_mcart_1('#skF_3'), C_93) | r2_hidden('#skF_6', C_93) | r2_hidden('#skF_5', C_93))), inference(resolution, [status(thm)], [c_128, c_325])).
% 2.45/1.35  tff(c_354, plain, (r2_hidden('#skF_6', k1_tarski(k2_mcart_1('#skF_3'))) | r2_hidden('#skF_5', k1_tarski(k2_mcart_1('#skF_3')))), inference(resolution, [status(thm)], [c_183, c_339])).
% 2.45/1.35  tff(c_376, plain, (r2_hidden('#skF_5', k1_tarski(k2_mcart_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_354])).
% 2.45/1.35  tff(c_134, plain, (![A_67, B_68, C_69]: (r2_hidden(A_67, k4_xboole_0(B_68, k1_tarski(C_69))) | C_69=A_67 | ~r2_hidden(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.45/1.35  tff(c_146, plain, (![A_67, C_69, B_68]: (~r2_hidden(A_67, k1_tarski(C_69)) | C_69=A_67 | ~r2_hidden(A_67, B_68))), inference(resolution, [status(thm)], [c_134, c_4])).
% 2.45/1.35  tff(c_382, plain, (![B_68]: (k2_mcart_1('#skF_3')='#skF_5' | ~r2_hidden('#skF_5', B_68))), inference(resolution, [status(thm)], [c_376, c_146])).
% 2.45/1.35  tff(c_388, plain, (![B_68]: (~r2_hidden('#skF_5', B_68))), inference(negUnitSimplification, [status(thm)], [c_98, c_382])).
% 2.45/1.35  tff(c_393, plain, $false, inference(negUnitSimplification, [status(thm)], [c_388, c_376])).
% 2.45/1.35  tff(c_394, plain, (r2_hidden('#skF_6', k1_tarski(k2_mcart_1('#skF_3')))), inference(splitRight, [status(thm)], [c_354])).
% 2.45/1.35  tff(c_414, plain, (![B_68]: (k2_mcart_1('#skF_3')='#skF_6' | ~r2_hidden('#skF_6', B_68))), inference(resolution, [status(thm)], [c_394, c_146])).
% 2.45/1.35  tff(c_419, plain, (![B_68]: (~r2_hidden('#skF_6', B_68))), inference(negUnitSimplification, [status(thm)], [c_90, c_414])).
% 2.45/1.35  tff(c_422, plain, $false, inference(negUnitSimplification, [status(thm)], [c_419, c_394])).
% 2.45/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.35  
% 2.45/1.35  Inference rules
% 2.45/1.35  ----------------------
% 2.45/1.35  #Ref     : 0
% 2.45/1.35  #Sup     : 87
% 2.45/1.35  #Fact    : 0
% 2.45/1.35  #Define  : 0
% 2.45/1.35  #Split   : 3
% 2.45/1.35  #Chain   : 0
% 2.45/1.35  #Close   : 0
% 2.45/1.35  
% 2.45/1.35  Ordering : KBO
% 2.45/1.35  
% 2.45/1.35  Simplification rules
% 2.45/1.35  ----------------------
% 2.45/1.35  #Subsume      : 6
% 2.45/1.35  #Demod        : 8
% 2.45/1.35  #Tautology    : 41
% 2.45/1.35  #SimpNegUnit  : 9
% 2.45/1.35  #BackRed      : 6
% 2.45/1.35  
% 2.45/1.35  #Partial instantiations: 0
% 2.45/1.35  #Strategies tried      : 1
% 2.45/1.35  
% 2.45/1.35  Timing (in seconds)
% 2.45/1.35  ----------------------
% 2.45/1.35  Preprocessing        : 0.30
% 2.45/1.35  Parsing              : 0.15
% 2.45/1.35  CNF conversion       : 0.02
% 2.45/1.35  Main loop            : 0.24
% 2.45/1.35  Inferencing          : 0.09
% 2.45/1.35  Reduction            : 0.07
% 2.45/1.35  Demodulation         : 0.04
% 2.45/1.35  BG Simplification    : 0.02
% 2.45/1.35  Subsumption          : 0.05
% 2.45/1.35  Abstraction          : 0.02
% 2.45/1.35  MUC search           : 0.00
% 2.45/1.35  Cooper               : 0.00
% 2.45/1.35  Total                : 0.57
% 2.45/1.35  Index Insertion      : 0.00
% 2.45/1.35  Index Deletion       : 0.00
% 2.45/1.35  Index Matching       : 0.00
% 2.45/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
