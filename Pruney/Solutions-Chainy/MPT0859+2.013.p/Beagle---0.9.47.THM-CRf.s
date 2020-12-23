%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:59 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 148 expanded)
%              Number of leaves         :   23 (  60 expanded)
%              Depth                    :    8
%              Number of atoms          :   70 ( 310 expanded)
%              Number of equality atoms :   14 (  62 expanded)
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

tff(f_73,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),D))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & r2_hidden(k2_mcart_1(A),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_mcart_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C)
        & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(c_40,plain,
    ( k1_mcart_1('#skF_3') != '#skF_5'
    | ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_53,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_38,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_74,plain,(
    ! [A_36,C_37,B_38] :
      ( r2_hidden(k2_mcart_1(A_36),C_37)
      | ~ r2_hidden(A_36,k2_zfmisc_1(B_38,C_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_76,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_74])).

tff(c_80,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_76])).

tff(c_81,plain,(
    k1_mcart_1('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_82,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_42,plain,
    ( k1_mcart_1('#skF_3') != '#skF_4'
    | ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_93,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_42])).

tff(c_105,plain,(
    ! [A_50,B_51,C_52] :
      ( r2_hidden(k1_mcart_1(A_50),B_51)
      | ~ r2_hidden(A_50,k2_zfmisc_1(B_51,C_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_108,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_38,c_105])).

tff(c_114,plain,(
    ! [D_56,A_57,B_58] :
      ( r2_hidden(D_56,k4_xboole_0(A_57,B_58))
      | r2_hidden(D_56,B_58)
      | ~ r2_hidden(D_56,A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,(
    ! [C_18,B_17] : ~ r2_hidden(C_18,k4_xboole_0(B_17,k1_tarski(C_18))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_128,plain,(
    ! [D_59,A_60] :
      ( r2_hidden(D_59,k1_tarski(D_59))
      | ~ r2_hidden(D_59,A_60) ) ),
    inference(resolution,[status(thm)],[c_114,c_30])).

tff(c_138,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k1_tarski(k1_mcart_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_108,c_128])).

tff(c_184,plain,(
    ! [C_67,A_68,B_69] :
      ( k4_xboole_0(C_67,k2_tarski(A_68,B_69)) = C_67
      | r2_hidden(B_69,C_67)
      | r2_hidden(A_68,C_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_239,plain,(
    ! [D_75,A_76,B_77,C_78] :
      ( ~ r2_hidden(D_75,k2_tarski(A_76,B_77))
      | ~ r2_hidden(D_75,C_78)
      | r2_hidden(B_77,C_78)
      | r2_hidden(A_76,C_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_4])).

tff(c_245,plain,(
    ! [C_79] :
      ( ~ r2_hidden(k1_mcart_1('#skF_3'),C_79)
      | r2_hidden('#skF_5',C_79)
      | r2_hidden('#skF_4',C_79) ) ),
    inference(resolution,[status(thm)],[c_108,c_239])).

tff(c_260,plain,
    ( r2_hidden('#skF_5',k1_tarski(k1_mcart_1('#skF_3')))
    | r2_hidden('#skF_4',k1_tarski(k1_mcart_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_138,c_245])).

tff(c_264,plain,(
    r2_hidden('#skF_4',k1_tarski(k1_mcart_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_260])).

tff(c_145,plain,(
    ! [A_61,B_62,C_63] :
      ( r2_hidden(A_61,k4_xboole_0(B_62,k1_tarski(C_63)))
      | C_63 = A_61
      | ~ r2_hidden(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_159,plain,(
    ! [A_61,C_63,B_62] :
      ( ~ r2_hidden(A_61,k1_tarski(C_63))
      | C_63 = A_61
      | ~ r2_hidden(A_61,B_62) ) ),
    inference(resolution,[status(thm)],[c_145,c_4])).

tff(c_279,plain,(
    ! [B_62] :
      ( k1_mcart_1('#skF_3') = '#skF_4'
      | ~ r2_hidden('#skF_4',B_62) ) ),
    inference(resolution,[status(thm)],[c_264,c_159])).

tff(c_285,plain,(
    ! [B_62] : ~ r2_hidden('#skF_4',B_62) ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_279])).

tff(c_289,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_285,c_264])).

tff(c_290,plain,(
    r2_hidden('#skF_5',k1_tarski(k1_mcart_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_260])).

tff(c_295,plain,(
    ! [B_62] :
      ( k1_mcart_1('#skF_3') = '#skF_5'
      | ~ r2_hidden('#skF_5',B_62) ) ),
    inference(resolution,[status(thm)],[c_290,c_159])).

tff(c_301,plain,(
    ! [B_62] : ~ r2_hidden('#skF_5',B_62) ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_295])).

tff(c_305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_301,c_290])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:19:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.23  
% 2.01/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.23  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 2.01/1.23  
% 2.01/1.23  %Foreground sorts:
% 2.01/1.23  
% 2.01/1.23  
% 2.01/1.23  %Background operators:
% 2.01/1.23  
% 2.01/1.23  
% 2.01/1.23  %Foreground operators:
% 2.01/1.23  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.01/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.01/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.01/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.01/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.01/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.01/1.23  tff('#skF_5', type, '#skF_5': $i).
% 2.01/1.23  tff('#skF_6', type, '#skF_6': $i).
% 2.01/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.01/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.01/1.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.01/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.23  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.01/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.01/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.01/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.23  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.01/1.23  
% 2.12/1.25  tff(f_73, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), D)) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & r2_hidden(k2_mcart_1(A), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_mcart_1)).
% 2.12/1.25  tff(f_64, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.12/1.25  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.12/1.25  tff(f_58, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.12/1.25  tff(f_51, axiom, (![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 2.12/1.25  tff(c_40, plain, (k1_mcart_1('#skF_3')!='#skF_5' | ~r2_hidden(k2_mcart_1('#skF_3'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.12/1.25  tff(c_53, plain, (~r2_hidden(k2_mcart_1('#skF_3'), '#skF_6')), inference(splitLeft, [status(thm)], [c_40])).
% 2.12/1.25  tff(c_38, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.12/1.25  tff(c_74, plain, (![A_36, C_37, B_38]: (r2_hidden(k2_mcart_1(A_36), C_37) | ~r2_hidden(A_36, k2_zfmisc_1(B_38, C_37)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.12/1.25  tff(c_76, plain, (r2_hidden(k2_mcart_1('#skF_3'), '#skF_6')), inference(resolution, [status(thm)], [c_38, c_74])).
% 2.12/1.25  tff(c_80, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_76])).
% 2.12/1.25  tff(c_81, plain, (k1_mcart_1('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_40])).
% 2.12/1.25  tff(c_82, plain, (r2_hidden(k2_mcart_1('#skF_3'), '#skF_6')), inference(splitRight, [status(thm)], [c_40])).
% 2.12/1.25  tff(c_42, plain, (k1_mcart_1('#skF_3')!='#skF_4' | ~r2_hidden(k2_mcart_1('#skF_3'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.12/1.25  tff(c_93, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_42])).
% 2.12/1.25  tff(c_105, plain, (![A_50, B_51, C_52]: (r2_hidden(k1_mcart_1(A_50), B_51) | ~r2_hidden(A_50, k2_zfmisc_1(B_51, C_52)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.12/1.25  tff(c_108, plain, (r2_hidden(k1_mcart_1('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_38, c_105])).
% 2.12/1.25  tff(c_114, plain, (![D_56, A_57, B_58]: (r2_hidden(D_56, k4_xboole_0(A_57, B_58)) | r2_hidden(D_56, B_58) | ~r2_hidden(D_56, A_57))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.12/1.25  tff(c_30, plain, (![C_18, B_17]: (~r2_hidden(C_18, k4_xboole_0(B_17, k1_tarski(C_18))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.12/1.25  tff(c_128, plain, (![D_59, A_60]: (r2_hidden(D_59, k1_tarski(D_59)) | ~r2_hidden(D_59, A_60))), inference(resolution, [status(thm)], [c_114, c_30])).
% 2.12/1.25  tff(c_138, plain, (r2_hidden(k1_mcart_1('#skF_3'), k1_tarski(k1_mcart_1('#skF_3')))), inference(resolution, [status(thm)], [c_108, c_128])).
% 2.12/1.25  tff(c_184, plain, (![C_67, A_68, B_69]: (k4_xboole_0(C_67, k2_tarski(A_68, B_69))=C_67 | r2_hidden(B_69, C_67) | r2_hidden(A_68, C_67))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.12/1.25  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.12/1.25  tff(c_239, plain, (![D_75, A_76, B_77, C_78]: (~r2_hidden(D_75, k2_tarski(A_76, B_77)) | ~r2_hidden(D_75, C_78) | r2_hidden(B_77, C_78) | r2_hidden(A_76, C_78))), inference(superposition, [status(thm), theory('equality')], [c_184, c_4])).
% 2.12/1.25  tff(c_245, plain, (![C_79]: (~r2_hidden(k1_mcart_1('#skF_3'), C_79) | r2_hidden('#skF_5', C_79) | r2_hidden('#skF_4', C_79))), inference(resolution, [status(thm)], [c_108, c_239])).
% 2.12/1.25  tff(c_260, plain, (r2_hidden('#skF_5', k1_tarski(k1_mcart_1('#skF_3'))) | r2_hidden('#skF_4', k1_tarski(k1_mcart_1('#skF_3')))), inference(resolution, [status(thm)], [c_138, c_245])).
% 2.12/1.25  tff(c_264, plain, (r2_hidden('#skF_4', k1_tarski(k1_mcart_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_260])).
% 2.12/1.25  tff(c_145, plain, (![A_61, B_62, C_63]: (r2_hidden(A_61, k4_xboole_0(B_62, k1_tarski(C_63))) | C_63=A_61 | ~r2_hidden(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.12/1.25  tff(c_159, plain, (![A_61, C_63, B_62]: (~r2_hidden(A_61, k1_tarski(C_63)) | C_63=A_61 | ~r2_hidden(A_61, B_62))), inference(resolution, [status(thm)], [c_145, c_4])).
% 2.12/1.25  tff(c_279, plain, (![B_62]: (k1_mcart_1('#skF_3')='#skF_4' | ~r2_hidden('#skF_4', B_62))), inference(resolution, [status(thm)], [c_264, c_159])).
% 2.12/1.25  tff(c_285, plain, (![B_62]: (~r2_hidden('#skF_4', B_62))), inference(negUnitSimplification, [status(thm)], [c_93, c_279])).
% 2.12/1.25  tff(c_289, plain, $false, inference(negUnitSimplification, [status(thm)], [c_285, c_264])).
% 2.12/1.25  tff(c_290, plain, (r2_hidden('#skF_5', k1_tarski(k1_mcart_1('#skF_3')))), inference(splitRight, [status(thm)], [c_260])).
% 2.12/1.25  tff(c_295, plain, (![B_62]: (k1_mcart_1('#skF_3')='#skF_5' | ~r2_hidden('#skF_5', B_62))), inference(resolution, [status(thm)], [c_290, c_159])).
% 2.12/1.25  tff(c_301, plain, (![B_62]: (~r2_hidden('#skF_5', B_62))), inference(negUnitSimplification, [status(thm)], [c_81, c_295])).
% 2.12/1.25  tff(c_305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_301, c_290])).
% 2.12/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.25  
% 2.12/1.25  Inference rules
% 2.12/1.25  ----------------------
% 2.12/1.25  #Ref     : 0
% 2.12/1.25  #Sup     : 60
% 2.12/1.25  #Fact    : 0
% 2.12/1.25  #Define  : 0
% 2.12/1.25  #Split   : 2
% 2.12/1.25  #Chain   : 0
% 2.12/1.25  #Close   : 0
% 2.12/1.25  
% 2.12/1.25  Ordering : KBO
% 2.12/1.25  
% 2.12/1.25  Simplification rules
% 2.12/1.25  ----------------------
% 2.12/1.25  #Subsume      : 5
% 2.12/1.25  #Demod        : 5
% 2.12/1.25  #Tautology    : 34
% 2.12/1.25  #SimpNegUnit  : 7
% 2.12/1.25  #BackRed      : 4
% 2.12/1.25  
% 2.12/1.25  #Partial instantiations: 0
% 2.12/1.25  #Strategies tried      : 1
% 2.12/1.25  
% 2.12/1.25  Timing (in seconds)
% 2.12/1.25  ----------------------
% 2.12/1.25  Preprocessing        : 0.29
% 2.12/1.25  Parsing              : 0.15
% 2.12/1.25  CNF conversion       : 0.02
% 2.12/1.25  Main loop            : 0.20
% 2.12/1.25  Inferencing          : 0.07
% 2.12/1.25  Reduction            : 0.06
% 2.12/1.25  Demodulation         : 0.03
% 2.12/1.25  BG Simplification    : 0.01
% 2.12/1.25  Subsumption          : 0.04
% 2.12/1.25  Abstraction          : 0.01
% 2.12/1.25  MUC search           : 0.00
% 2.12/1.25  Cooper               : 0.00
% 2.12/1.25  Total                : 0.52
% 2.12/1.25  Index Insertion      : 0.00
% 2.12/1.25  Index Deletion       : 0.00
% 2.12/1.25  Index Matching       : 0.00
% 2.12/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
