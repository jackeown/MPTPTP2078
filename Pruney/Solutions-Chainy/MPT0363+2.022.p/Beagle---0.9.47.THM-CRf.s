%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:38 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   53 (  67 expanded)
%              Number of leaves         :   22 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   70 ( 111 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,C)
            <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_44,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_32,plain,
    ( r1_xboole_0('#skF_3','#skF_4')
    | r1_tarski('#skF_3',k3_subset_1('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_45,plain,(
    r1_tarski('#skF_3',k3_subset_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_26,plain,
    ( ~ r1_tarski('#skF_3',k3_subset_1('#skF_2','#skF_4'))
    | ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_53,plain,(
    ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_26])).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_101,plain,(
    ! [A_45,B_46] :
      ( k4_xboole_0(A_45,B_46) = k3_subset_1(A_45,B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_108,plain,(
    k4_xboole_0('#skF_2','#skF_4') = k3_subset_1('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_101])).

tff(c_12,plain,(
    ! [A_12,B_13] : r1_xboole_0(k4_xboole_0(A_12,B_13),B_13) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_80,plain,(
    ! [A_36,C_37,B_38] :
      ( r1_xboole_0(A_36,C_37)
      | ~ r1_xboole_0(B_38,C_37)
      | ~ r1_tarski(A_36,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_86,plain,(
    ! [A_36,B_13,A_12] :
      ( r1_xboole_0(A_36,B_13)
      | ~ r1_tarski(A_36,k4_xboole_0(A_12,B_13)) ) ),
    inference(resolution,[status(thm)],[c_12,c_80])).

tff(c_189,plain,(
    ! [A_48] :
      ( r1_xboole_0(A_48,'#skF_4')
      | ~ r1_tarski(A_48,k3_subset_1('#skF_2','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_86])).

tff(c_196,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_45,c_189])).

tff(c_202,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_196])).

tff(c_204,plain,(
    ~ r1_tarski('#skF_3',k3_subset_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_361,plain,(
    ! [A_75,B_76] :
      ( k4_xboole_0(A_75,B_76) = k3_subset_1(A_75,B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_368,plain,(
    k4_xboole_0('#skF_2','#skF_4') = k3_subset_1('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_361])).

tff(c_203,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = A_14
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_208,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_203,c_14])).

tff(c_301,plain,(
    ! [A_70,C_71,B_72] :
      ( r1_tarski(k4_xboole_0(A_70,C_71),k4_xboole_0(B_72,C_71))
      | ~ r1_tarski(A_70,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_315,plain,(
    ! [B_72] :
      ( r1_tarski('#skF_3',k4_xboole_0(B_72,'#skF_4'))
      | ~ r1_tarski('#skF_3',B_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_301])).

tff(c_376,plain,
    ( r1_tarski('#skF_3',k3_subset_1('#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_368,c_315])).

tff(c_394,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_204,c_376])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_297,plain,(
    ! [C_67,A_68,B_69] :
      ( r2_hidden(C_67,A_68)
      | ~ r2_hidden(C_67,B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_631,plain,(
    ! [A_89,B_90,A_91] :
      ( r2_hidden('#skF_1'(A_89,B_90),A_91)
      | ~ m1_subset_1(A_89,k1_zfmisc_1(A_91))
      | r1_tarski(A_89,B_90) ) ),
    inference(resolution,[status(thm)],[c_6,c_297])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_643,plain,(
    ! [A_92,A_93] :
      ( ~ m1_subset_1(A_92,k1_zfmisc_1(A_93))
      | r1_tarski(A_92,A_93) ) ),
    inference(resolution,[status(thm)],[c_631,c_4])).

tff(c_649,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_643])).

tff(c_654,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_394,c_649])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:35:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.32  
% 2.45/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.32  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.45/1.32  
% 2.45/1.32  %Foreground sorts:
% 2.45/1.32  
% 2.45/1.32  
% 2.45/1.32  %Background operators:
% 2.45/1.32  
% 2.45/1.32  
% 2.45/1.32  %Foreground operators:
% 2.45/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.45/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.45/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.45/1.32  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.45/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.45/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.45/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.45/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.45/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.45/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.45/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.45/1.32  
% 2.45/1.33  tff(f_69, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_subset_1)).
% 2.45/1.33  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.45/1.33  tff(f_44, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.45/1.33  tff(f_42, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.45/1.33  tff(f_48, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.45/1.33  tff(f_36, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_xboole_1)).
% 2.45/1.33  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.45/1.33  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.45/1.33  tff(c_32, plain, (r1_xboole_0('#skF_3', '#skF_4') | r1_tarski('#skF_3', k3_subset_1('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.45/1.33  tff(c_45, plain, (r1_tarski('#skF_3', k3_subset_1('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_32])).
% 2.45/1.33  tff(c_26, plain, (~r1_tarski('#skF_3', k3_subset_1('#skF_2', '#skF_4')) | ~r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.45/1.33  tff(c_53, plain, (~r1_xboole_0('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_45, c_26])).
% 2.45/1.33  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.45/1.33  tff(c_101, plain, (![A_45, B_46]: (k4_xboole_0(A_45, B_46)=k3_subset_1(A_45, B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.45/1.33  tff(c_108, plain, (k4_xboole_0('#skF_2', '#skF_4')=k3_subset_1('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_22, c_101])).
% 2.45/1.33  tff(c_12, plain, (![A_12, B_13]: (r1_xboole_0(k4_xboole_0(A_12, B_13), B_13))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.45/1.33  tff(c_80, plain, (![A_36, C_37, B_38]: (r1_xboole_0(A_36, C_37) | ~r1_xboole_0(B_38, C_37) | ~r1_tarski(A_36, B_38))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.45/1.33  tff(c_86, plain, (![A_36, B_13, A_12]: (r1_xboole_0(A_36, B_13) | ~r1_tarski(A_36, k4_xboole_0(A_12, B_13)))), inference(resolution, [status(thm)], [c_12, c_80])).
% 2.45/1.33  tff(c_189, plain, (![A_48]: (r1_xboole_0(A_48, '#skF_4') | ~r1_tarski(A_48, k3_subset_1('#skF_2', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_108, c_86])).
% 2.45/1.33  tff(c_196, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_45, c_189])).
% 2.45/1.33  tff(c_202, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_196])).
% 2.45/1.33  tff(c_204, plain, (~r1_tarski('#skF_3', k3_subset_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_32])).
% 2.45/1.33  tff(c_361, plain, (![A_75, B_76]: (k4_xboole_0(A_75, B_76)=k3_subset_1(A_75, B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.45/1.33  tff(c_368, plain, (k4_xboole_0('#skF_2', '#skF_4')=k3_subset_1('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_22, c_361])).
% 2.45/1.33  tff(c_203, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_32])).
% 2.45/1.33  tff(c_14, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=A_14 | ~r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.45/1.33  tff(c_208, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_203, c_14])).
% 2.45/1.33  tff(c_301, plain, (![A_70, C_71, B_72]: (r1_tarski(k4_xboole_0(A_70, C_71), k4_xboole_0(B_72, C_71)) | ~r1_tarski(A_70, B_72))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.45/1.33  tff(c_315, plain, (![B_72]: (r1_tarski('#skF_3', k4_xboole_0(B_72, '#skF_4')) | ~r1_tarski('#skF_3', B_72))), inference(superposition, [status(thm), theory('equality')], [c_208, c_301])).
% 2.45/1.33  tff(c_376, plain, (r1_tarski('#skF_3', k3_subset_1('#skF_2', '#skF_4')) | ~r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_368, c_315])).
% 2.45/1.33  tff(c_394, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_204, c_376])).
% 2.45/1.33  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.45/1.33  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.45/1.33  tff(c_297, plain, (![C_67, A_68, B_69]: (r2_hidden(C_67, A_68) | ~r2_hidden(C_67, B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.45/1.33  tff(c_631, plain, (![A_89, B_90, A_91]: (r2_hidden('#skF_1'(A_89, B_90), A_91) | ~m1_subset_1(A_89, k1_zfmisc_1(A_91)) | r1_tarski(A_89, B_90))), inference(resolution, [status(thm)], [c_6, c_297])).
% 2.45/1.33  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.45/1.33  tff(c_643, plain, (![A_92, A_93]: (~m1_subset_1(A_92, k1_zfmisc_1(A_93)) | r1_tarski(A_92, A_93))), inference(resolution, [status(thm)], [c_631, c_4])).
% 2.45/1.33  tff(c_649, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_643])).
% 2.45/1.33  tff(c_654, plain, $false, inference(negUnitSimplification, [status(thm)], [c_394, c_649])).
% 2.45/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.33  
% 2.45/1.33  Inference rules
% 2.45/1.33  ----------------------
% 2.45/1.33  #Ref     : 0
% 2.45/1.33  #Sup     : 158
% 2.45/1.33  #Fact    : 0
% 2.45/1.33  #Define  : 0
% 2.45/1.33  #Split   : 2
% 2.45/1.33  #Chain   : 0
% 2.45/1.33  #Close   : 0
% 2.45/1.33  
% 2.45/1.33  Ordering : KBO
% 2.45/1.33  
% 2.45/1.33  Simplification rules
% 2.45/1.33  ----------------------
% 2.45/1.33  #Subsume      : 13
% 2.45/1.33  #Demod        : 68
% 2.45/1.33  #Tautology    : 75
% 2.45/1.33  #SimpNegUnit  : 5
% 2.45/1.33  #BackRed      : 0
% 2.45/1.33  
% 2.45/1.33  #Partial instantiations: 0
% 2.45/1.33  #Strategies tried      : 1
% 2.45/1.33  
% 2.45/1.33  Timing (in seconds)
% 2.45/1.33  ----------------------
% 2.45/1.33  Preprocessing        : 0.29
% 2.45/1.33  Parsing              : 0.16
% 2.45/1.33  CNF conversion       : 0.02
% 2.45/1.33  Main loop            : 0.29
% 2.45/1.33  Inferencing          : 0.11
% 2.45/1.33  Reduction            : 0.09
% 2.45/1.33  Demodulation         : 0.06
% 2.45/1.34  BG Simplification    : 0.02
% 2.45/1.34  Subsumption          : 0.05
% 2.45/1.34  Abstraction          : 0.02
% 2.45/1.34  MUC search           : 0.00
% 2.45/1.34  Cooper               : 0.00
% 2.45/1.34  Total                : 0.61
% 2.45/1.34  Index Insertion      : 0.00
% 2.45/1.34  Index Deletion       : 0.00
% 2.45/1.34  Index Matching       : 0.00
% 2.45/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
