%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:07 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   55 (  80 expanded)
%              Number of leaves         :   26 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   63 ( 105 expanded)
%              Number of equality atoms :   22 (  46 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_38,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_62,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [A_8] : k3_xboole_0(A_8,A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_24,plain,(
    ! [A_20] : k1_subset_1(A_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_30,plain,
    ( k1_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_37,plain,
    ( k1_xboole_0 != '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_30])).

tff(c_55,plain,(
    ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_37])).

tff(c_36,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
    | k1_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_38,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_36])).

tff(c_62,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_38])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r1_xboole_0(A_6,B_7)
      | k3_xboole_0(A_6,B_7) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_63,plain,(
    ! [A_6,B_7] :
      ( r1_xboole_0(A_6,B_7)
      | k3_xboole_0(A_6,B_7) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_10])).

tff(c_92,plain,(
    ! [A_44,B_45,C_46] :
      ( ~ r1_xboole_0(A_44,B_45)
      | ~ r2_hidden(C_46,k3_xboole_0(A_44,B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_140,plain,(
    ! [A_54,C_55] :
      ( ~ r1_xboole_0(A_54,A_54)
      | ~ r2_hidden(C_55,A_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_92])).

tff(c_143,plain,(
    ! [C_55,B_7] :
      ( ~ r2_hidden(C_55,B_7)
      | k3_xboole_0(B_7,B_7) != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_63,c_140])).

tff(c_147,plain,(
    ! [C_56,B_57] :
      ( ~ r2_hidden(C_56,B_57)
      | B_57 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_143])).

tff(c_152,plain,(
    ! [B_2] : r1_tarski('#skF_4',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_147])).

tff(c_155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_55])).

tff(c_156,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_37])).

tff(c_157,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_37])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_502,plain,(
    ! [A_121,B_122] :
      ( k4_xboole_0(A_121,B_122) = k3_subset_1(A_121,B_122)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(A_121)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_506,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_502])).

tff(c_20,plain,(
    ! [A_17,C_19,B_18] :
      ( r1_xboole_0(A_17,C_19)
      | ~ r1_tarski(A_17,k4_xboole_0(B_18,C_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_700,plain,(
    ! [A_135] :
      ( r1_xboole_0(A_135,'#skF_4')
      | ~ r1_tarski(A_135,k3_subset_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_506,c_20])).

tff(c_737,plain,(
    r1_xboole_0('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_157,c_700])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = k1_xboole_0
      | ~ r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_746,plain,(
    k3_xboole_0('#skF_4','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_737,c_8])).

tff(c_751,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_746])).

tff(c_753,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_751])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:39:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.44/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.33  
% 2.44/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.33  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.44/1.33  
% 2.44/1.33  %Foreground sorts:
% 2.44/1.33  
% 2.44/1.33  
% 2.44/1.33  %Background operators:
% 2.44/1.33  
% 2.44/1.33  
% 2.44/1.33  %Foreground operators:
% 2.44/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.44/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.44/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.44/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.44/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.44/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.44/1.33  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.44/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.44/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.44/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.44/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.44/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.44/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.44/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.44/1.33  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.44/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.44/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.44/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.44/1.33  
% 2.44/1.34  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.44/1.34  tff(f_38, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.44/1.34  tff(f_62, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 2.44/1.34  tff(f_73, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 2.44/1.34  tff(f_36, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.44/1.34  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.44/1.34  tff(f_66, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.44/1.34  tff(f_60, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.44/1.34  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.44/1.34  tff(c_12, plain, (![A_8]: (k3_xboole_0(A_8, A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.44/1.34  tff(c_24, plain, (![A_20]: (k1_subset_1(A_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.44/1.34  tff(c_30, plain, (k1_subset_1('#skF_3')!='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.44/1.34  tff(c_37, plain, (k1_xboole_0!='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_30])).
% 2.44/1.34  tff(c_55, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_37])).
% 2.44/1.34  tff(c_36, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | k1_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.44/1.34  tff(c_38, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_36])).
% 2.44/1.34  tff(c_62, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_55, c_38])).
% 2.44/1.34  tff(c_10, plain, (![A_6, B_7]: (r1_xboole_0(A_6, B_7) | k3_xboole_0(A_6, B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.44/1.34  tff(c_63, plain, (![A_6, B_7]: (r1_xboole_0(A_6, B_7) | k3_xboole_0(A_6, B_7)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_10])).
% 2.44/1.34  tff(c_92, plain, (![A_44, B_45, C_46]: (~r1_xboole_0(A_44, B_45) | ~r2_hidden(C_46, k3_xboole_0(A_44, B_45)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.44/1.34  tff(c_140, plain, (![A_54, C_55]: (~r1_xboole_0(A_54, A_54) | ~r2_hidden(C_55, A_54))), inference(superposition, [status(thm), theory('equality')], [c_12, c_92])).
% 2.44/1.34  tff(c_143, plain, (![C_55, B_7]: (~r2_hidden(C_55, B_7) | k3_xboole_0(B_7, B_7)!='#skF_4')), inference(resolution, [status(thm)], [c_63, c_140])).
% 2.44/1.34  tff(c_147, plain, (![C_56, B_57]: (~r2_hidden(C_56, B_57) | B_57!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_143])).
% 2.44/1.34  tff(c_152, plain, (![B_2]: (r1_tarski('#skF_4', B_2))), inference(resolution, [status(thm)], [c_6, c_147])).
% 2.44/1.34  tff(c_155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_152, c_55])).
% 2.44/1.34  tff(c_156, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_37])).
% 2.44/1.34  tff(c_157, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_37])).
% 2.44/1.34  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.44/1.34  tff(c_502, plain, (![A_121, B_122]: (k4_xboole_0(A_121, B_122)=k3_subset_1(A_121, B_122) | ~m1_subset_1(B_122, k1_zfmisc_1(A_121)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.44/1.34  tff(c_506, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_502])).
% 2.44/1.34  tff(c_20, plain, (![A_17, C_19, B_18]: (r1_xboole_0(A_17, C_19) | ~r1_tarski(A_17, k4_xboole_0(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.44/1.34  tff(c_700, plain, (![A_135]: (r1_xboole_0(A_135, '#skF_4') | ~r1_tarski(A_135, k3_subset_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_506, c_20])).
% 2.44/1.34  tff(c_737, plain, (r1_xboole_0('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_157, c_700])).
% 2.44/1.34  tff(c_8, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=k1_xboole_0 | ~r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.44/1.34  tff(c_746, plain, (k3_xboole_0('#skF_4', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_737, c_8])).
% 2.44/1.34  tff(c_751, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_746])).
% 2.44/1.34  tff(c_753, plain, $false, inference(negUnitSimplification, [status(thm)], [c_156, c_751])).
% 2.44/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.34  
% 2.44/1.34  Inference rules
% 2.44/1.34  ----------------------
% 2.44/1.34  #Ref     : 0
% 2.44/1.34  #Sup     : 154
% 2.44/1.34  #Fact    : 0
% 2.44/1.34  #Define  : 0
% 2.44/1.34  #Split   : 1
% 2.44/1.34  #Chain   : 0
% 2.44/1.34  #Close   : 0
% 2.44/1.34  
% 2.44/1.34  Ordering : KBO
% 2.44/1.34  
% 2.44/1.34  Simplification rules
% 2.44/1.34  ----------------------
% 2.44/1.34  #Subsume      : 22
% 2.44/1.34  #Demod        : 46
% 2.44/1.34  #Tautology    : 67
% 2.44/1.34  #SimpNegUnit  : 7
% 2.44/1.34  #BackRed      : 4
% 2.44/1.34  
% 2.44/1.34  #Partial instantiations: 0
% 2.44/1.34  #Strategies tried      : 1
% 2.44/1.34  
% 2.44/1.34  Timing (in seconds)
% 2.44/1.34  ----------------------
% 2.44/1.35  Preprocessing        : 0.29
% 2.44/1.35  Parsing              : 0.15
% 2.44/1.35  CNF conversion       : 0.02
% 2.44/1.35  Main loop            : 0.29
% 2.44/1.35  Inferencing          : 0.12
% 2.44/1.35  Reduction            : 0.09
% 2.44/1.35  Demodulation         : 0.06
% 2.44/1.35  BG Simplification    : 0.01
% 2.44/1.35  Subsumption          : 0.05
% 2.44/1.35  Abstraction          : 0.02
% 2.44/1.35  MUC search           : 0.00
% 2.44/1.35  Cooper               : 0.00
% 2.44/1.35  Total                : 0.61
% 2.44/1.35  Index Insertion      : 0.00
% 2.44/1.35  Index Deletion       : 0.00
% 2.44/1.35  Index Matching       : 0.00
% 2.44/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
