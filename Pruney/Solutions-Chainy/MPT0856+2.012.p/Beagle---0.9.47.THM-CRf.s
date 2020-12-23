%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:53 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   55 (  62 expanded)
%              Number of leaves         :   31 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   68 (  86 expanded)
%              Number of equality atoms :   12 (  17 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_tarski > r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(r2_tarski,type,(
    r2_tarski: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_71,axiom,(
    ! [A] :
    ? [B] :
      ( r2_hidden(A,B)
      & ! [C,D] :
          ( ( r2_hidden(C,B)
            & r1_tarski(D,C) )
         => r2_hidden(D,B) )
      & ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(k1_zfmisc_1(C),B) )
      & ! [C] :
          ~ ( r1_tarski(C,B)
            & ~ r2_tarski(C,B)
            & ~ r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t136_zfmisc_1)).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
       => ( k1_mcart_1(A) = B
          & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_40,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_36,plain,(
    ! [A_19] : r2_hidden(A_19,'#skF_3'(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_54,plain,
    ( ~ r2_hidden(k2_mcart_1('#skF_4'),'#skF_6')
    | k1_mcart_1('#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_78,plain,(
    k1_mcart_1('#skF_4') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_44,plain,(
    ! [A_40,B_41,C_42] :
      ( r2_hidden(A_40,k4_xboole_0(B_41,k1_tarski(C_42)))
      | C_42 = A_40
      | ~ r2_hidden(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_56,plain,(
    r2_hidden('#skF_4',k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_99,plain,(
    ! [A_71,B_72,C_73] :
      ( r2_hidden(k1_mcart_1(A_71),B_72)
      | ~ r2_hidden(A_71,k2_zfmisc_1(B_72,C_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_102,plain,(
    r2_hidden(k1_mcart_1('#skF_4'),k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_56,c_99])).

tff(c_22,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_138,plain,(
    ! [A_92,B_93,C_94] :
      ( r1_tarski(k2_tarski(A_92,B_93),C_94)
      | ~ r2_hidden(B_93,C_94)
      | ~ r2_hidden(A_92,C_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_154,plain,(
    ! [A_95,C_96] :
      ( r1_tarski(k1_tarski(A_95),C_96)
      | ~ r2_hidden(A_95,C_96)
      | ~ r2_hidden(A_95,C_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_138])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_170,plain,(
    ! [A_100,C_101] :
      ( k2_xboole_0(k1_tarski(A_100),C_101) = C_101
      | ~ r2_hidden(A_100,C_101) ) ),
    inference(resolution,[status(thm)],[c_154,c_20])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( ~ r2_hidden(D_6,A_1)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_188,plain,(
    ! [D_102,A_103,C_104] :
      ( ~ r2_hidden(D_102,k1_tarski(A_103))
      | r2_hidden(D_102,C_104)
      | ~ r2_hidden(A_103,C_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_6])).

tff(c_192,plain,(
    ! [C_105] :
      ( r2_hidden(k1_mcart_1('#skF_4'),C_105)
      | ~ r2_hidden('#skF_5',C_105) ) ),
    inference(resolution,[status(thm)],[c_102,c_188])).

tff(c_46,plain,(
    ! [C_42,B_41] : ~ r2_hidden(C_42,k4_xboole_0(B_41,k1_tarski(C_42))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_220,plain,(
    ! [B_106] : ~ r2_hidden('#skF_5',k4_xboole_0(B_106,k1_tarski(k1_mcart_1('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_192,c_46])).

tff(c_224,plain,(
    ! [B_41] :
      ( k1_mcart_1('#skF_4') = '#skF_5'
      | ~ r2_hidden('#skF_5',B_41) ) ),
    inference(resolution,[status(thm)],[c_44,c_220])).

tff(c_228,plain,(
    ! [B_107] : ~ r2_hidden('#skF_5',B_107) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_224])).

tff(c_248,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_36,c_228])).

tff(c_249,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_4'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_280,plain,(
    ! [A_128,C_129,B_130] :
      ( r2_hidden(k2_mcart_1(A_128),C_129)
      | ~ r2_hidden(A_128,k2_zfmisc_1(B_130,C_129)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_282,plain,(
    r2_hidden(k2_mcart_1('#skF_4'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_280])).

tff(c_286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_249,c_282])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:17:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.27  
% 2.18/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.28  %$ r2_tarski > r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.18/1.28  
% 2.18/1.28  %Foreground sorts:
% 2.18/1.28  
% 2.18/1.28  
% 2.18/1.28  %Background operators:
% 2.18/1.28  
% 2.18/1.28  
% 2.18/1.28  %Foreground operators:
% 2.18/1.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.18/1.28  tff(r2_tarski, type, r2_tarski: ($i * $i) > $o).
% 2.18/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.18/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.18/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.18/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.18/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.18/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.18/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.18/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.18/1.28  tff('#skF_6', type, '#skF_6': $i).
% 2.18/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.18/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.18/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.28  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.18/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.18/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.18/1.28  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.18/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.28  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.18/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.18/1.28  
% 2.18/1.29  tff(f_71, axiom, (![A]: (?[B]: (((r2_hidden(A, B) & (![C, D]: ((r2_hidden(C, B) & r1_tarski(D, C)) => r2_hidden(D, B)))) & (![C]: (r2_hidden(C, B) => r2_hidden(k1_zfmisc_1(C), B)))) & (![C]: ~((r1_tarski(C, B) & ~r2_tarski(C, B)) & ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t136_zfmisc_1)).
% 2.18/1.29  tff(f_97, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_mcart_1)).
% 2.18/1.29  tff(f_84, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.18/1.29  tff(f_90, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.18/1.29  tff(f_40, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.18/1.29  tff(f_77, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.18/1.29  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.18/1.29  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.18/1.29  tff(c_36, plain, (![A_19]: (r2_hidden(A_19, '#skF_3'(A_19)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.18/1.29  tff(c_54, plain, (~r2_hidden(k2_mcart_1('#skF_4'), '#skF_6') | k1_mcart_1('#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.18/1.29  tff(c_78, plain, (k1_mcart_1('#skF_4')!='#skF_5'), inference(splitLeft, [status(thm)], [c_54])).
% 2.18/1.29  tff(c_44, plain, (![A_40, B_41, C_42]: (r2_hidden(A_40, k4_xboole_0(B_41, k1_tarski(C_42))) | C_42=A_40 | ~r2_hidden(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.18/1.29  tff(c_56, plain, (r2_hidden('#skF_4', k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.18/1.29  tff(c_99, plain, (![A_71, B_72, C_73]: (r2_hidden(k1_mcart_1(A_71), B_72) | ~r2_hidden(A_71, k2_zfmisc_1(B_72, C_73)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.18/1.29  tff(c_102, plain, (r2_hidden(k1_mcart_1('#skF_4'), k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_99])).
% 2.18/1.29  tff(c_22, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.18/1.29  tff(c_138, plain, (![A_92, B_93, C_94]: (r1_tarski(k2_tarski(A_92, B_93), C_94) | ~r2_hidden(B_93, C_94) | ~r2_hidden(A_92, C_94))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.18/1.29  tff(c_154, plain, (![A_95, C_96]: (r1_tarski(k1_tarski(A_95), C_96) | ~r2_hidden(A_95, C_96) | ~r2_hidden(A_95, C_96))), inference(superposition, [status(thm), theory('equality')], [c_22, c_138])).
% 2.18/1.29  tff(c_20, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.18/1.29  tff(c_170, plain, (![A_100, C_101]: (k2_xboole_0(k1_tarski(A_100), C_101)=C_101 | ~r2_hidden(A_100, C_101))), inference(resolution, [status(thm)], [c_154, c_20])).
% 2.18/1.29  tff(c_6, plain, (![D_6, A_1, B_2]: (~r2_hidden(D_6, A_1) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.18/1.29  tff(c_188, plain, (![D_102, A_103, C_104]: (~r2_hidden(D_102, k1_tarski(A_103)) | r2_hidden(D_102, C_104) | ~r2_hidden(A_103, C_104))), inference(superposition, [status(thm), theory('equality')], [c_170, c_6])).
% 2.18/1.29  tff(c_192, plain, (![C_105]: (r2_hidden(k1_mcart_1('#skF_4'), C_105) | ~r2_hidden('#skF_5', C_105))), inference(resolution, [status(thm)], [c_102, c_188])).
% 2.18/1.29  tff(c_46, plain, (![C_42, B_41]: (~r2_hidden(C_42, k4_xboole_0(B_41, k1_tarski(C_42))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.18/1.29  tff(c_220, plain, (![B_106]: (~r2_hidden('#skF_5', k4_xboole_0(B_106, k1_tarski(k1_mcart_1('#skF_4')))))), inference(resolution, [status(thm)], [c_192, c_46])).
% 2.18/1.29  tff(c_224, plain, (![B_41]: (k1_mcart_1('#skF_4')='#skF_5' | ~r2_hidden('#skF_5', B_41))), inference(resolution, [status(thm)], [c_44, c_220])).
% 2.18/1.29  tff(c_228, plain, (![B_107]: (~r2_hidden('#skF_5', B_107))), inference(negUnitSimplification, [status(thm)], [c_78, c_224])).
% 2.18/1.29  tff(c_248, plain, $false, inference(resolution, [status(thm)], [c_36, c_228])).
% 2.18/1.29  tff(c_249, plain, (~r2_hidden(k2_mcart_1('#skF_4'), '#skF_6')), inference(splitRight, [status(thm)], [c_54])).
% 2.18/1.29  tff(c_280, plain, (![A_128, C_129, B_130]: (r2_hidden(k2_mcart_1(A_128), C_129) | ~r2_hidden(A_128, k2_zfmisc_1(B_130, C_129)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.18/1.29  tff(c_282, plain, (r2_hidden(k2_mcart_1('#skF_4'), '#skF_6')), inference(resolution, [status(thm)], [c_56, c_280])).
% 2.18/1.29  tff(c_286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_249, c_282])).
% 2.18/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.29  
% 2.18/1.29  Inference rules
% 2.18/1.29  ----------------------
% 2.18/1.29  #Ref     : 0
% 2.18/1.29  #Sup     : 49
% 2.18/1.29  #Fact    : 0
% 2.18/1.29  #Define  : 0
% 2.18/1.29  #Split   : 1
% 2.18/1.29  #Chain   : 0
% 2.18/1.29  #Close   : 0
% 2.18/1.29  
% 2.18/1.29  Ordering : KBO
% 2.18/1.29  
% 2.18/1.29  Simplification rules
% 2.18/1.29  ----------------------
% 2.18/1.29  #Subsume      : 7
% 2.18/1.29  #Demod        : 1
% 2.18/1.29  #Tautology    : 23
% 2.18/1.29  #SimpNegUnit  : 2
% 2.18/1.29  #BackRed      : 0
% 2.18/1.29  
% 2.18/1.29  #Partial instantiations: 0
% 2.18/1.29  #Strategies tried      : 1
% 2.18/1.29  
% 2.18/1.29  Timing (in seconds)
% 2.18/1.29  ----------------------
% 2.18/1.29  Preprocessing        : 0.32
% 2.18/1.29  Parsing              : 0.16
% 2.18/1.29  CNF conversion       : 0.02
% 2.18/1.29  Main loop            : 0.21
% 2.18/1.29  Inferencing          : 0.08
% 2.18/1.29  Reduction            : 0.06
% 2.18/1.29  Demodulation         : 0.04
% 2.18/1.29  BG Simplification    : 0.02
% 2.18/1.29  Subsumption          : 0.03
% 2.18/1.29  Abstraction          : 0.01
% 2.18/1.29  MUC search           : 0.00
% 2.18/1.29  Cooper               : 0.00
% 2.18/1.29  Total                : 0.56
% 2.18/1.29  Index Insertion      : 0.00
% 2.18/1.29  Index Deletion       : 0.00
% 2.18/1.29  Index Matching       : 0.00
% 2.18/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
