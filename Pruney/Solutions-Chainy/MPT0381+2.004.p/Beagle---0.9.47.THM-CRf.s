%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:01 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   54 (  59 expanded)
%              Number of leaves         :   31 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   64 (  72 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_58,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_54,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_56,plain,(
    ! [B_36,A_37] :
      ( ~ r2_hidden(B_36,A_37)
      | ~ v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_56])).

tff(c_185,plain,(
    ! [B_61,A_62] :
      ( m1_subset_1(B_61,A_62)
      | ~ r2_hidden(B_61,A_62)
      | v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_194,plain,
    ( m1_subset_1('#skF_3','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_185])).

tff(c_199,plain,(
    m1_subset_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_194])).

tff(c_274,plain,(
    ! [B_75,A_76] :
      ( m1_subset_1(k1_tarski(B_75),k1_zfmisc_1(A_76))
      | k1_xboole_0 = A_76
      | ~ m1_subset_1(B_75,A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_52,plain,(
    ~ m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_280,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_274,c_52])).

tff(c_284,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_280])).

tff(c_26,plain,(
    ! [A_17] : r1_xboole_0(A_17,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_286,plain,(
    ! [A_17] : r1_xboole_0(A_17,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_26])).

tff(c_24,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_435,plain,(
    ! [A_104,C_105,B_106] :
      ( r2_hidden(A_104,C_105)
      | ~ r2_hidden(A_104,B_106)
      | r2_hidden(A_104,k5_xboole_0(B_106,C_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_685,plain,(
    ! [A_148,A_149,B_150] :
      ( r2_hidden(A_148,k3_xboole_0(A_149,B_150))
      | ~ r2_hidden(A_148,A_149)
      | r2_hidden(A_148,k4_xboole_0(A_149,B_150)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_435])).

tff(c_38,plain,(
    ! [C_30,B_29] : ~ r2_hidden(C_30,k4_xboole_0(B_29,k1_tarski(C_30))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_704,plain,(
    ! [A_151,A_152] :
      ( r2_hidden(A_151,k3_xboole_0(A_152,k1_tarski(A_151)))
      | ~ r2_hidden(A_151,A_152) ) ),
    inference(resolution,[status(thm)],[c_685,c_38])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_154,plain,(
    ! [A_54,B_55,C_56] :
      ( ~ r1_xboole_0(A_54,B_55)
      | ~ r2_hidden(C_56,k3_xboole_0(A_54,B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_168,plain,(
    ! [B_2,A_1,C_56] :
      ( ~ r1_xboole_0(B_2,A_1)
      | ~ r2_hidden(C_56,k3_xboole_0(A_1,B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_154])).

tff(c_737,plain,(
    ! [A_153,A_154] :
      ( ~ r1_xboole_0(k1_tarski(A_153),A_154)
      | ~ r2_hidden(A_153,A_154) ) ),
    inference(resolution,[status(thm)],[c_704,c_168])).

tff(c_742,plain,(
    ! [A_153] : ~ r2_hidden(A_153,'#skF_4') ),
    inference(resolution,[status(thm)],[c_286,c_737])).

tff(c_744,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_742,c_54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:06:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.38  
% 2.77/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.38  %$ r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.77/1.38  
% 2.77/1.38  %Foreground sorts:
% 2.77/1.38  
% 2.77/1.38  
% 2.77/1.38  %Background operators:
% 2.77/1.38  
% 2.77/1.38  
% 2.77/1.38  %Foreground operators:
% 2.77/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.77/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.77/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.77/1.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.77/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.77/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.77/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.77/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.77/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.77/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.77/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.77/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.77/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.77/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.77/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.77/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.77/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.77/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.77/1.38  
% 2.77/1.39  tff(f_98, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 2.77/1.39  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.77/1.39  tff(f_86, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.77/1.39  tff(f_93, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_subset_1)).
% 2.77/1.39  tff(f_58, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.77/1.39  tff(f_56, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.77/1.39  tff(f_40, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 2.77/1.39  tff(f_73, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.77/1.39  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.77/1.39  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.77/1.39  tff(c_54, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.77/1.39  tff(c_56, plain, (![B_36, A_37]: (~r2_hidden(B_36, A_37) | ~v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.77/1.39  tff(c_60, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_54, c_56])).
% 2.77/1.39  tff(c_185, plain, (![B_61, A_62]: (m1_subset_1(B_61, A_62) | ~r2_hidden(B_61, A_62) | v1_xboole_0(A_62))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.77/1.39  tff(c_194, plain, (m1_subset_1('#skF_3', '#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_54, c_185])).
% 2.77/1.39  tff(c_199, plain, (m1_subset_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_60, c_194])).
% 2.77/1.39  tff(c_274, plain, (![B_75, A_76]: (m1_subset_1(k1_tarski(B_75), k1_zfmisc_1(A_76)) | k1_xboole_0=A_76 | ~m1_subset_1(B_75, A_76))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.77/1.39  tff(c_52, plain, (~m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.77/1.39  tff(c_280, plain, (k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_274, c_52])).
% 2.77/1.39  tff(c_284, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_199, c_280])).
% 2.77/1.39  tff(c_26, plain, (![A_17]: (r1_xboole_0(A_17, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.77/1.39  tff(c_286, plain, (![A_17]: (r1_xboole_0(A_17, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_284, c_26])).
% 2.77/1.39  tff(c_24, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.77/1.39  tff(c_435, plain, (![A_104, C_105, B_106]: (r2_hidden(A_104, C_105) | ~r2_hidden(A_104, B_106) | r2_hidden(A_104, k5_xboole_0(B_106, C_105)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.77/1.39  tff(c_685, plain, (![A_148, A_149, B_150]: (r2_hidden(A_148, k3_xboole_0(A_149, B_150)) | ~r2_hidden(A_148, A_149) | r2_hidden(A_148, k4_xboole_0(A_149, B_150)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_435])).
% 2.77/1.39  tff(c_38, plain, (![C_30, B_29]: (~r2_hidden(C_30, k4_xboole_0(B_29, k1_tarski(C_30))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.77/1.39  tff(c_704, plain, (![A_151, A_152]: (r2_hidden(A_151, k3_xboole_0(A_152, k1_tarski(A_151))) | ~r2_hidden(A_151, A_152))), inference(resolution, [status(thm)], [c_685, c_38])).
% 2.77/1.39  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.77/1.39  tff(c_154, plain, (![A_54, B_55, C_56]: (~r1_xboole_0(A_54, B_55) | ~r2_hidden(C_56, k3_xboole_0(A_54, B_55)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.77/1.39  tff(c_168, plain, (![B_2, A_1, C_56]: (~r1_xboole_0(B_2, A_1) | ~r2_hidden(C_56, k3_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_154])).
% 2.77/1.39  tff(c_737, plain, (![A_153, A_154]: (~r1_xboole_0(k1_tarski(A_153), A_154) | ~r2_hidden(A_153, A_154))), inference(resolution, [status(thm)], [c_704, c_168])).
% 2.77/1.39  tff(c_742, plain, (![A_153]: (~r2_hidden(A_153, '#skF_4'))), inference(resolution, [status(thm)], [c_286, c_737])).
% 2.77/1.39  tff(c_744, plain, $false, inference(negUnitSimplification, [status(thm)], [c_742, c_54])).
% 2.77/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.39  
% 2.77/1.39  Inference rules
% 2.77/1.39  ----------------------
% 2.77/1.39  #Ref     : 0
% 2.77/1.39  #Sup     : 163
% 2.77/1.39  #Fact    : 0
% 2.77/1.39  #Define  : 0
% 2.77/1.39  #Split   : 1
% 2.77/1.39  #Chain   : 0
% 2.77/1.39  #Close   : 0
% 2.77/1.39  
% 2.77/1.39  Ordering : KBO
% 2.77/1.39  
% 2.77/1.39  Simplification rules
% 2.77/1.39  ----------------------
% 2.77/1.39  #Subsume      : 37
% 2.77/1.39  #Demod        : 9
% 2.77/1.39  #Tautology    : 50
% 2.77/1.39  #SimpNegUnit  : 2
% 2.77/1.39  #BackRed      : 3
% 2.77/1.39  
% 2.77/1.39  #Partial instantiations: 0
% 2.77/1.39  #Strategies tried      : 1
% 2.77/1.39  
% 2.77/1.39  Timing (in seconds)
% 2.77/1.39  ----------------------
% 2.77/1.39  Preprocessing        : 0.32
% 2.77/1.40  Parsing              : 0.17
% 2.77/1.40  CNF conversion       : 0.02
% 2.77/1.40  Main loop            : 0.33
% 2.77/1.40  Inferencing          : 0.13
% 2.77/1.40  Reduction            : 0.09
% 2.77/1.40  Demodulation         : 0.06
% 2.77/1.40  BG Simplification    : 0.02
% 2.77/1.40  Subsumption          : 0.07
% 2.77/1.40  Abstraction          : 0.02
% 2.77/1.40  MUC search           : 0.00
% 2.77/1.40  Cooper               : 0.00
% 2.77/1.40  Total                : 0.67
% 2.77/1.40  Index Insertion      : 0.00
% 2.77/1.40  Index Deletion       : 0.00
% 2.77/1.40  Index Matching       : 0.00
% 2.77/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
