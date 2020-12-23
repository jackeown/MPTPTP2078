%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:56 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   47 (  71 expanded)
%              Number of leaves         :   21 (  35 expanded)
%              Depth                    :    5
%              Number of atoms          :   59 ( 118 expanded)
%              Number of equality atoms :   14 (  32 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),k1_tarski(C)))
       => ( k1_mcart_1(A) = B
          & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_mcart_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_36,plain,
    ( k2_mcart_1('#skF_3') != '#skF_5'
    | k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_48,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_38,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k1_tarski('#skF_4'),k1_tarski('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_74,plain,(
    ! [A_36,B_37,C_38] :
      ( r2_hidden(k1_mcart_1(A_36),B_37)
      | ~ r2_hidden(A_36,k2_zfmisc_1(B_37,C_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_77,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_38,c_74])).

tff(c_105,plain,(
    ! [A_44,B_45,C_46] :
      ( r2_hidden(A_44,k4_xboole_0(B_45,k1_tarski(C_46)))
      | C_46 = A_44
      | ~ r2_hidden(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_144,plain,(
    ! [A_50,C_51,B_52] :
      ( ~ r2_hidden(A_50,k1_tarski(C_51))
      | C_51 = A_50
      | ~ r2_hidden(A_50,B_52) ) ),
    inference(resolution,[status(thm)],[c_105,c_4])).

tff(c_152,plain,(
    ! [B_52] :
      ( k1_mcart_1('#skF_3') = '#skF_4'
      | ~ r2_hidden(k1_mcart_1('#skF_3'),B_52) ) ),
    inference(resolution,[status(thm)],[c_77,c_144])).

tff(c_163,plain,(
    ! [B_52] : ~ r2_hidden(k1_mcart_1('#skF_3'),B_52) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_152])).

tff(c_78,plain,(
    ! [D_39,A_40,B_41] :
      ( r2_hidden(D_39,k4_xboole_0(A_40,B_41))
      | r2_hidden(D_39,B_41)
      | ~ r2_hidden(D_39,A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_28,plain,(
    ! [C_15,B_14] : ~ r2_hidden(C_15,k4_xboole_0(B_14,k1_tarski(C_15))) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_92,plain,(
    ! [D_42,A_43] :
      ( r2_hidden(D_42,k1_tarski(D_42))
      | ~ r2_hidden(D_42,A_43) ) ),
    inference(resolution,[status(thm)],[c_78,c_28])).

tff(c_102,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k1_tarski(k1_mcart_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_77,c_92])).

tff(c_167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_163,c_102])).

tff(c_168,plain,(
    k2_mcart_1('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_200,plain,(
    ! [A_69,C_70,B_71] :
      ( r2_hidden(k2_mcart_1(A_69),C_70)
      | ~ r2_hidden(A_69,k2_zfmisc_1(B_71,C_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_203,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_38,c_200])).

tff(c_204,plain,(
    ! [A_72,B_73,C_74] :
      ( r2_hidden(A_72,k4_xboole_0(B_73,k1_tarski(C_74)))
      | C_74 = A_72
      | ~ r2_hidden(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_267,plain,(
    ! [A_83,C_84,B_85] :
      ( ~ r2_hidden(A_83,k1_tarski(C_84))
      | C_84 = A_83
      | ~ r2_hidden(A_83,B_85) ) ),
    inference(resolution,[status(thm)],[c_204,c_4])).

tff(c_273,plain,(
    ! [B_85] :
      ( k2_mcart_1('#skF_3') = '#skF_5'
      | ~ r2_hidden(k2_mcart_1('#skF_3'),B_85) ) ),
    inference(resolution,[status(thm)],[c_203,c_267])).

tff(c_282,plain,(
    ! [B_85] : ~ r2_hidden(k2_mcart_1('#skF_3'),B_85) ),
    inference(negUnitSimplification,[status(thm)],[c_168,c_273])).

tff(c_219,plain,(
    ! [D_75,A_76,B_77] :
      ( r2_hidden(D_75,k4_xboole_0(A_76,B_77))
      | r2_hidden(D_75,B_77)
      | ~ r2_hidden(D_75,A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_233,plain,(
    ! [D_78,A_79] :
      ( r2_hidden(D_78,k1_tarski(D_78))
      | ~ r2_hidden(D_78,A_79) ) ),
    inference(resolution,[status(thm)],[c_219,c_28])).

tff(c_246,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),k1_tarski(k2_mcart_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_203,c_233])).

tff(c_287,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_282,c_246])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:55:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.33  
% 2.03/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.33  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 2.03/1.33  
% 2.03/1.33  %Foreground sorts:
% 2.03/1.33  
% 2.03/1.33  
% 2.03/1.33  %Background operators:
% 2.03/1.33  
% 2.03/1.33  
% 2.03/1.33  %Foreground operators:
% 2.03/1.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.03/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.03/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.03/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.03/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.03/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.03/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.03/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.03/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.03/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.33  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.03/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.03/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.03/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.33  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.03/1.33  
% 2.03/1.34  tff(f_61, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), k1_tarski(C))) => ((k1_mcart_1(A) = B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_mcart_1)).
% 2.03/1.34  tff(f_54, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.03/1.34  tff(f_48, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.03/1.34  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.03/1.34  tff(c_36, plain, (k2_mcart_1('#skF_3')!='#skF_5' | k1_mcart_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.03/1.34  tff(c_48, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_36])).
% 2.03/1.34  tff(c_38, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k1_tarski('#skF_4'), k1_tarski('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.03/1.34  tff(c_74, plain, (![A_36, B_37, C_38]: (r2_hidden(k1_mcart_1(A_36), B_37) | ~r2_hidden(A_36, k2_zfmisc_1(B_37, C_38)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.03/1.34  tff(c_77, plain, (r2_hidden(k1_mcart_1('#skF_3'), k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_38, c_74])).
% 2.03/1.34  tff(c_105, plain, (![A_44, B_45, C_46]: (r2_hidden(A_44, k4_xboole_0(B_45, k1_tarski(C_46))) | C_46=A_44 | ~r2_hidden(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.03/1.34  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.03/1.34  tff(c_144, plain, (![A_50, C_51, B_52]: (~r2_hidden(A_50, k1_tarski(C_51)) | C_51=A_50 | ~r2_hidden(A_50, B_52))), inference(resolution, [status(thm)], [c_105, c_4])).
% 2.03/1.34  tff(c_152, plain, (![B_52]: (k1_mcart_1('#skF_3')='#skF_4' | ~r2_hidden(k1_mcart_1('#skF_3'), B_52))), inference(resolution, [status(thm)], [c_77, c_144])).
% 2.03/1.34  tff(c_163, plain, (![B_52]: (~r2_hidden(k1_mcart_1('#skF_3'), B_52))), inference(negUnitSimplification, [status(thm)], [c_48, c_152])).
% 2.03/1.34  tff(c_78, plain, (![D_39, A_40, B_41]: (r2_hidden(D_39, k4_xboole_0(A_40, B_41)) | r2_hidden(D_39, B_41) | ~r2_hidden(D_39, A_40))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.03/1.34  tff(c_28, plain, (![C_15, B_14]: (~r2_hidden(C_15, k4_xboole_0(B_14, k1_tarski(C_15))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.03/1.34  tff(c_92, plain, (![D_42, A_43]: (r2_hidden(D_42, k1_tarski(D_42)) | ~r2_hidden(D_42, A_43))), inference(resolution, [status(thm)], [c_78, c_28])).
% 2.03/1.34  tff(c_102, plain, (r2_hidden(k1_mcart_1('#skF_3'), k1_tarski(k1_mcart_1('#skF_3')))), inference(resolution, [status(thm)], [c_77, c_92])).
% 2.03/1.34  tff(c_167, plain, $false, inference(negUnitSimplification, [status(thm)], [c_163, c_102])).
% 2.03/1.34  tff(c_168, plain, (k2_mcart_1('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_36])).
% 2.03/1.34  tff(c_200, plain, (![A_69, C_70, B_71]: (r2_hidden(k2_mcart_1(A_69), C_70) | ~r2_hidden(A_69, k2_zfmisc_1(B_71, C_70)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.03/1.34  tff(c_203, plain, (r2_hidden(k2_mcart_1('#skF_3'), k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_38, c_200])).
% 2.03/1.34  tff(c_204, plain, (![A_72, B_73, C_74]: (r2_hidden(A_72, k4_xboole_0(B_73, k1_tarski(C_74))) | C_74=A_72 | ~r2_hidden(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.03/1.34  tff(c_267, plain, (![A_83, C_84, B_85]: (~r2_hidden(A_83, k1_tarski(C_84)) | C_84=A_83 | ~r2_hidden(A_83, B_85))), inference(resolution, [status(thm)], [c_204, c_4])).
% 2.03/1.34  tff(c_273, plain, (![B_85]: (k2_mcart_1('#skF_3')='#skF_5' | ~r2_hidden(k2_mcart_1('#skF_3'), B_85))), inference(resolution, [status(thm)], [c_203, c_267])).
% 2.03/1.34  tff(c_282, plain, (![B_85]: (~r2_hidden(k2_mcart_1('#skF_3'), B_85))), inference(negUnitSimplification, [status(thm)], [c_168, c_273])).
% 2.03/1.34  tff(c_219, plain, (![D_75, A_76, B_77]: (r2_hidden(D_75, k4_xboole_0(A_76, B_77)) | r2_hidden(D_75, B_77) | ~r2_hidden(D_75, A_76))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.03/1.34  tff(c_233, plain, (![D_78, A_79]: (r2_hidden(D_78, k1_tarski(D_78)) | ~r2_hidden(D_78, A_79))), inference(resolution, [status(thm)], [c_219, c_28])).
% 2.03/1.34  tff(c_246, plain, (r2_hidden(k2_mcart_1('#skF_3'), k1_tarski(k2_mcart_1('#skF_3')))), inference(resolution, [status(thm)], [c_203, c_233])).
% 2.03/1.34  tff(c_287, plain, $false, inference(negUnitSimplification, [status(thm)], [c_282, c_246])).
% 2.03/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.34  
% 2.03/1.34  Inference rules
% 2.03/1.34  ----------------------
% 2.03/1.34  #Ref     : 0
% 2.03/1.34  #Sup     : 56
% 2.03/1.34  #Fact    : 0
% 2.03/1.34  #Define  : 0
% 2.03/1.34  #Split   : 1
% 2.03/1.34  #Chain   : 0
% 2.03/1.34  #Close   : 0
% 2.03/1.34  
% 2.03/1.34  Ordering : KBO
% 2.03/1.34  
% 2.03/1.34  Simplification rules
% 2.03/1.34  ----------------------
% 2.03/1.34  #Subsume      : 5
% 2.03/1.34  #Demod        : 7
% 2.03/1.34  #Tautology    : 32
% 2.03/1.34  #SimpNegUnit  : 6
% 2.03/1.34  #BackRed      : 4
% 2.03/1.34  
% 2.03/1.34  #Partial instantiations: 0
% 2.03/1.34  #Strategies tried      : 1
% 2.03/1.34  
% 2.03/1.34  Timing (in seconds)
% 2.03/1.34  ----------------------
% 2.03/1.34  Preprocessing        : 0.30
% 2.03/1.34  Parsing              : 0.16
% 2.03/1.34  CNF conversion       : 0.02
% 2.03/1.34  Main loop            : 0.19
% 2.03/1.34  Inferencing          : 0.07
% 2.03/1.34  Reduction            : 0.05
% 2.03/1.34  Demodulation         : 0.04
% 2.03/1.34  BG Simplification    : 0.01
% 2.03/1.34  Subsumption          : 0.03
% 2.03/1.34  Abstraction          : 0.01
% 2.03/1.34  MUC search           : 0.00
% 2.03/1.34  Cooper               : 0.00
% 2.03/1.34  Total                : 0.52
% 2.03/1.34  Index Insertion      : 0.00
% 2.03/1.34  Index Deletion       : 0.00
% 2.03/1.34  Index Matching       : 0.00
% 2.03/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
