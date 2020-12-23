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
% DateTime   : Thu Dec  3 09:56:14 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 106 expanded)
%              Number of leaves         :   26 (  45 expanded)
%              Depth                    :    7
%              Number of atoms          :   87 ( 167 expanded)
%              Number of equality atoms :   19 (  53 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_61,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_72,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(c_32,plain,(
    ! [A_15] : k2_subset_1(A_15) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_42,plain,
    ( k2_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_50,plain,
    ( '#skF_3' != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_42])).

tff(c_82,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_48,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | k2_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_49,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_48])).

tff(c_83,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_49])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_85,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_40])).

tff(c_36,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(k3_subset_1(A_18,B_19),k1_zfmisc_1(A_18))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_38,plain,(
    ! [A_20] : ~ v1_xboole_0(k1_zfmisc_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_124,plain,(
    ! [B_41,A_42] :
      ( r2_hidden(B_41,A_42)
      | ~ m1_subset_1(B_41,A_42)
      | v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12,plain,(
    ! [C_12,A_8] :
      ( r1_tarski(C_12,A_8)
      | ~ r2_hidden(C_12,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_131,plain,(
    ! [B_41,A_8] :
      ( r1_tarski(B_41,A_8)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_8))
      | v1_xboole_0(k1_zfmisc_1(A_8)) ) ),
    inference(resolution,[status(thm)],[c_124,c_12])).

tff(c_141,plain,(
    ! [B_45,A_46] :
      ( r1_tarski(B_45,A_46)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_46)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_131])).

tff(c_160,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(k3_subset_1(A_47,B_48),A_47)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_47)) ) ),
    inference(resolution,[status(thm)],[c_36,c_141])).

tff(c_84,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_82])).

tff(c_165,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_160,c_84])).

tff(c_173,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_165])).

tff(c_174,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_219,plain,(
    ! [B_61,A_62] :
      ( r2_hidden(B_61,A_62)
      | ~ m1_subset_1(B_61,A_62)
      | v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_226,plain,(
    ! [B_61,A_8] :
      ( r1_tarski(B_61,A_8)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_8))
      | v1_xboole_0(k1_zfmisc_1(A_8)) ) ),
    inference(resolution,[status(thm)],[c_219,c_12])).

tff(c_231,plain,(
    ! [B_63,A_64] :
      ( r1_tarski(B_63,A_64)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_64)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_226])).

tff(c_244,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_231])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_246,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_244,c_2])).

tff(c_252,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_246])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_63,plain,(
    ! [A_24,B_25] :
      ( k2_xboole_0(A_24,B_25) = B_25
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_67,plain,(
    ! [B_2] : k2_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_63])).

tff(c_175,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_278,plain,(
    ! [A_70,B_71] :
      ( k4_xboole_0(A_70,B_71) = k3_subset_1(A_70,B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_291,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_278])).

tff(c_10,plain,(
    ! [A_5,B_6,C_7] :
      ( r1_tarski(A_5,k2_xboole_0(B_6,C_7))
      | ~ r1_tarski(k4_xboole_0(A_5,B_6),C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_388,plain,(
    ! [C_80] :
      ( r1_tarski('#skF_3',k2_xboole_0('#skF_4',C_80))
      | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),C_80) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_10])).

tff(c_403,plain,(
    r1_tarski('#skF_3',k2_xboole_0('#skF_4','#skF_4')) ),
    inference(resolution,[status(thm)],[c_175,c_388])).

tff(c_414,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_403])).

tff(c_416,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_252,c_414])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:09:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.28  
% 2.12/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.28  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.12/1.28  
% 2.12/1.28  %Foreground sorts:
% 2.12/1.28  
% 2.12/1.28  
% 2.12/1.28  %Background operators:
% 2.12/1.28  
% 2.12/1.28  
% 2.12/1.28  %Foreground operators:
% 2.12/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.12/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.12/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.12/1.28  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.12/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.12/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.12/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.12/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.12/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.12/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.12/1.28  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.12/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.12/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.12/1.28  
% 2.12/1.30  tff(f_61, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.12/1.30  tff(f_79, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 2.12/1.30  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.12/1.30  tff(f_72, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.12/1.30  tff(f_59, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.12/1.30  tff(f_46, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.12/1.30  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.12/1.30  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.12/1.30  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.12/1.30  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 2.12/1.30  tff(c_32, plain, (![A_15]: (k2_subset_1(A_15)=A_15)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.12/1.30  tff(c_42, plain, (k2_subset_1('#skF_3')!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.12/1.30  tff(c_50, plain, ('#skF_3'!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_42])).
% 2.12/1.30  tff(c_82, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_50])).
% 2.12/1.30  tff(c_48, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | k2_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.12/1.30  tff(c_49, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_48])).
% 2.12/1.30  tff(c_83, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_82, c_49])).
% 2.12/1.30  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.12/1.30  tff(c_85, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_40])).
% 2.12/1.30  tff(c_36, plain, (![A_18, B_19]: (m1_subset_1(k3_subset_1(A_18, B_19), k1_zfmisc_1(A_18)) | ~m1_subset_1(B_19, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.12/1.30  tff(c_38, plain, (![A_20]: (~v1_xboole_0(k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.12/1.30  tff(c_124, plain, (![B_41, A_42]: (r2_hidden(B_41, A_42) | ~m1_subset_1(B_41, A_42) | v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.12/1.30  tff(c_12, plain, (![C_12, A_8]: (r1_tarski(C_12, A_8) | ~r2_hidden(C_12, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.12/1.30  tff(c_131, plain, (![B_41, A_8]: (r1_tarski(B_41, A_8) | ~m1_subset_1(B_41, k1_zfmisc_1(A_8)) | v1_xboole_0(k1_zfmisc_1(A_8)))), inference(resolution, [status(thm)], [c_124, c_12])).
% 2.12/1.30  tff(c_141, plain, (![B_45, A_46]: (r1_tarski(B_45, A_46) | ~m1_subset_1(B_45, k1_zfmisc_1(A_46)))), inference(negUnitSimplification, [status(thm)], [c_38, c_131])).
% 2.12/1.30  tff(c_160, plain, (![A_47, B_48]: (r1_tarski(k3_subset_1(A_47, B_48), A_47) | ~m1_subset_1(B_48, k1_zfmisc_1(A_47)))), inference(resolution, [status(thm)], [c_36, c_141])).
% 2.12/1.30  tff(c_84, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_82])).
% 2.12/1.30  tff(c_165, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_160, c_84])).
% 2.12/1.30  tff(c_173, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_165])).
% 2.12/1.30  tff(c_174, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_50])).
% 2.12/1.30  tff(c_219, plain, (![B_61, A_62]: (r2_hidden(B_61, A_62) | ~m1_subset_1(B_61, A_62) | v1_xboole_0(A_62))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.12/1.30  tff(c_226, plain, (![B_61, A_8]: (r1_tarski(B_61, A_8) | ~m1_subset_1(B_61, k1_zfmisc_1(A_8)) | v1_xboole_0(k1_zfmisc_1(A_8)))), inference(resolution, [status(thm)], [c_219, c_12])).
% 2.12/1.30  tff(c_231, plain, (![B_63, A_64]: (r1_tarski(B_63, A_64) | ~m1_subset_1(B_63, k1_zfmisc_1(A_64)))), inference(negUnitSimplification, [status(thm)], [c_38, c_226])).
% 2.12/1.30  tff(c_244, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_231])).
% 2.12/1.30  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.12/1.30  tff(c_246, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_244, c_2])).
% 2.12/1.30  tff(c_252, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_174, c_246])).
% 2.12/1.30  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.12/1.30  tff(c_63, plain, (![A_24, B_25]: (k2_xboole_0(A_24, B_25)=B_25 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.12/1.30  tff(c_67, plain, (![B_2]: (k2_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_63])).
% 2.12/1.30  tff(c_175, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_50])).
% 2.12/1.30  tff(c_278, plain, (![A_70, B_71]: (k4_xboole_0(A_70, B_71)=k3_subset_1(A_70, B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(A_70)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.12/1.30  tff(c_291, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_278])).
% 2.12/1.30  tff(c_10, plain, (![A_5, B_6, C_7]: (r1_tarski(A_5, k2_xboole_0(B_6, C_7)) | ~r1_tarski(k4_xboole_0(A_5, B_6), C_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.12/1.30  tff(c_388, plain, (![C_80]: (r1_tarski('#skF_3', k2_xboole_0('#skF_4', C_80)) | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), C_80))), inference(superposition, [status(thm), theory('equality')], [c_291, c_10])).
% 2.12/1.30  tff(c_403, plain, (r1_tarski('#skF_3', k2_xboole_0('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_175, c_388])).
% 2.12/1.30  tff(c_414, plain, (r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_403])).
% 2.12/1.30  tff(c_416, plain, $false, inference(negUnitSimplification, [status(thm)], [c_252, c_414])).
% 2.12/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.30  
% 2.12/1.30  Inference rules
% 2.12/1.30  ----------------------
% 2.12/1.30  #Ref     : 0
% 2.12/1.30  #Sup     : 79
% 2.12/1.30  #Fact    : 0
% 2.12/1.30  #Define  : 0
% 2.12/1.30  #Split   : 2
% 2.12/1.30  #Chain   : 0
% 2.12/1.30  #Close   : 0
% 2.12/1.30  
% 2.12/1.30  Ordering : KBO
% 2.12/1.30  
% 2.12/1.30  Simplification rules
% 2.12/1.30  ----------------------
% 2.12/1.30  #Subsume      : 9
% 2.12/1.30  #Demod        : 15
% 2.12/1.30  #Tautology    : 31
% 2.12/1.30  #SimpNegUnit  : 8
% 2.12/1.30  #BackRed      : 2
% 2.12/1.30  
% 2.12/1.30  #Partial instantiations: 0
% 2.12/1.30  #Strategies tried      : 1
% 2.12/1.30  
% 2.12/1.30  Timing (in seconds)
% 2.12/1.30  ----------------------
% 2.12/1.30  Preprocessing        : 0.31
% 2.12/1.30  Parsing              : 0.17
% 2.12/1.30  CNF conversion       : 0.02
% 2.12/1.30  Main loop            : 0.22
% 2.12/1.30  Inferencing          : 0.08
% 2.12/1.30  Reduction            : 0.06
% 2.12/1.30  Demodulation         : 0.04
% 2.12/1.30  BG Simplification    : 0.02
% 2.12/1.30  Subsumption          : 0.04
% 2.12/1.30  Abstraction          : 0.01
% 2.12/1.30  MUC search           : 0.00
% 2.12/1.30  Cooper               : 0.00
% 2.12/1.30  Total                : 0.56
% 2.12/1.30  Index Insertion      : 0.00
% 2.12/1.30  Index Deletion       : 0.00
% 2.12/1.30  Index Matching       : 0.00
% 2.12/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
