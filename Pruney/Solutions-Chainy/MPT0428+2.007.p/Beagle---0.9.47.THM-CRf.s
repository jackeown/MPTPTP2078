%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:05 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   57 (  78 expanded)
%              Number of leaves         :   22 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   74 ( 120 expanded)
%              Number of equality atoms :   19 (  35 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v1_xboole_0 > k5_setfam_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(m1_setfam_1,type,(
    m1_setfam_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( m1_setfam_1(B,A)
        <=> k5_setfam_1(A,B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_setfam_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_40,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_37,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_277,plain,(
    ! [A_68,B_69] :
      ( k5_setfam_1(A_68,B_69) = k3_tarski(B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(k1_zfmisc_1(A_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_281,plain,(
    k5_setfam_1('#skF_1','#skF_2') = k3_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_277])).

tff(c_26,plain,
    ( k5_setfam_1('#skF_1','#skF_2') != '#skF_1'
    | ~ m1_setfam_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_45,plain,(
    ~ m1_setfam_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_32,plain,
    ( m1_setfam_1('#skF_2','#skF_1')
    | k5_setfam_1('#skF_1','#skF_2') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_46,plain,(
    k5_setfam_1('#skF_1','#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_32])).

tff(c_146,plain,(
    ! [A_42,B_43] :
      ( k5_setfam_1(A_42,B_43) = k3_tarski(B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k1_zfmisc_1(A_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_149,plain,(
    k5_setfam_1('#skF_1','#skF_2') = k3_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_146])).

tff(c_151,plain,(
    k3_tarski('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_149])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    ! [B_22,A_23] :
      ( m1_setfam_1(B_22,A_23)
      | ~ r1_tarski(A_23,k3_tarski(B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_75,plain,(
    ! [B_22] : m1_setfam_1(B_22,k3_tarski(B_22)) ),
    inference(resolution,[status(thm)],[c_6,c_59])).

tff(c_176,plain,(
    m1_setfam_1('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_75])).

tff(c_189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_176])).

tff(c_190,plain,(
    k5_setfam_1('#skF_1','#skF_2') != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_282,plain,(
    k3_tarski('#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_190])).

tff(c_191,plain,(
    m1_setfam_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_379,plain,(
    ! [A_82,B_83] :
      ( m1_subset_1(k5_setfam_1(A_82,B_83),k1_zfmisc_1(A_82))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(k1_zfmisc_1(A_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_395,plain,
    ( m1_subset_1(k3_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_379])).

tff(c_403,plain,(
    m1_subset_1(k3_tarski('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_395])).

tff(c_12,plain,(
    ! [A_6] : ~ v1_xboole_0(k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_22,plain,(
    ! [A_13,B_14] :
      ( r2_hidden(A_13,B_14)
      | v1_xboole_0(B_14)
      | ~ m1_subset_1(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10,plain,(
    ! [A_5] : k3_tarski(k1_zfmisc_1(A_5)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_194,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,k3_tarski(B_47))
      | ~ r2_hidden(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_260,plain,(
    ! [A_64,A_65] :
      ( r1_tarski(A_64,A_65)
      | ~ r2_hidden(A_64,k1_zfmisc_1(A_65)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_194])).

tff(c_264,plain,(
    ! [A_13,A_65] :
      ( r1_tarski(A_13,A_65)
      | v1_xboole_0(k1_zfmisc_1(A_65))
      | ~ m1_subset_1(A_13,k1_zfmisc_1(A_65)) ) ),
    inference(resolution,[status(thm)],[c_22,c_260])).

tff(c_267,plain,(
    ! [A_13,A_65] :
      ( r1_tarski(A_13,A_65)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(A_65)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_264])).

tff(c_419,plain,(
    r1_tarski(k3_tarski('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_403,c_267])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,k3_tarski(B_8))
      | ~ m1_setfam_1(B_8,A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_247,plain,(
    ! [B_62,A_63] :
      ( B_62 = A_63
      | ~ r1_tarski(B_62,A_63)
      | ~ r1_tarski(A_63,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_254,plain,(
    ! [B_8,A_7] :
      ( k3_tarski(B_8) = A_7
      | ~ r1_tarski(k3_tarski(B_8),A_7)
      | ~ m1_setfam_1(B_8,A_7) ) ),
    inference(resolution,[status(thm)],[c_14,c_247])).

tff(c_422,plain,
    ( k3_tarski('#skF_2') = '#skF_1'
    | ~ m1_setfam_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_419,c_254])).

tff(c_430,plain,(
    k3_tarski('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_422])).

tff(c_432,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_282,c_430])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.33  % CPULimit   : 60
% 0.19/0.33  % DateTime   : Tue Dec  1 12:44:52 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.33  
% 2.29/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.33  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v1_xboole_0 > k5_setfam_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.29/1.33  
% 2.29/1.33  %Foreground sorts:
% 2.29/1.33  
% 2.29/1.33  
% 2.29/1.33  %Background operators:
% 2.29/1.33  
% 2.29/1.33  
% 2.29/1.33  %Foreground operators:
% 2.29/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.29/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.29/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.29/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.29/1.33  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 2.29/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.29/1.33  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.29/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.33  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.29/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.29/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.29/1.33  
% 2.29/1.35  tff(f_65, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (m1_setfam_1(B, A) <=> (k5_setfam_1(A, B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_setfam_1)).
% 2.29/1.35  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 2.29/1.35  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.29/1.35  tff(f_44, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_setfam_1)).
% 2.29/1.35  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 2.29/1.35  tff(f_40, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.29/1.35  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.29/1.35  tff(f_37, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.29/1.35  tff(f_35, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.29/1.35  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.29/1.35  tff(c_277, plain, (![A_68, B_69]: (k5_setfam_1(A_68, B_69)=k3_tarski(B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(k1_zfmisc_1(A_68))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.29/1.35  tff(c_281, plain, (k5_setfam_1('#skF_1', '#skF_2')=k3_tarski('#skF_2')), inference(resolution, [status(thm)], [c_24, c_277])).
% 2.29/1.35  tff(c_26, plain, (k5_setfam_1('#skF_1', '#skF_2')!='#skF_1' | ~m1_setfam_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.29/1.35  tff(c_45, plain, (~m1_setfam_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_26])).
% 2.29/1.35  tff(c_32, plain, (m1_setfam_1('#skF_2', '#skF_1') | k5_setfam_1('#skF_1', '#skF_2')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.29/1.35  tff(c_46, plain, (k5_setfam_1('#skF_1', '#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_45, c_32])).
% 2.29/1.35  tff(c_146, plain, (![A_42, B_43]: (k5_setfam_1(A_42, B_43)=k3_tarski(B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(k1_zfmisc_1(A_42))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.29/1.35  tff(c_149, plain, (k5_setfam_1('#skF_1', '#skF_2')=k3_tarski('#skF_2')), inference(resolution, [status(thm)], [c_24, c_146])).
% 2.29/1.35  tff(c_151, plain, (k3_tarski('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_149])).
% 2.29/1.35  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.29/1.35  tff(c_59, plain, (![B_22, A_23]: (m1_setfam_1(B_22, A_23) | ~r1_tarski(A_23, k3_tarski(B_22)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.29/1.35  tff(c_75, plain, (![B_22]: (m1_setfam_1(B_22, k3_tarski(B_22)))), inference(resolution, [status(thm)], [c_6, c_59])).
% 2.29/1.35  tff(c_176, plain, (m1_setfam_1('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_151, c_75])).
% 2.29/1.35  tff(c_189, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45, c_176])).
% 2.29/1.35  tff(c_190, plain, (k5_setfam_1('#skF_1', '#skF_2')!='#skF_1'), inference(splitRight, [status(thm)], [c_26])).
% 2.29/1.35  tff(c_282, plain, (k3_tarski('#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_281, c_190])).
% 2.29/1.35  tff(c_191, plain, (m1_setfam_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_26])).
% 2.29/1.35  tff(c_379, plain, (![A_82, B_83]: (m1_subset_1(k5_setfam_1(A_82, B_83), k1_zfmisc_1(A_82)) | ~m1_subset_1(B_83, k1_zfmisc_1(k1_zfmisc_1(A_82))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.29/1.35  tff(c_395, plain, (m1_subset_1(k3_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_281, c_379])).
% 2.29/1.35  tff(c_403, plain, (m1_subset_1(k3_tarski('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_395])).
% 2.29/1.35  tff(c_12, plain, (![A_6]: (~v1_xboole_0(k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.29/1.35  tff(c_22, plain, (![A_13, B_14]: (r2_hidden(A_13, B_14) | v1_xboole_0(B_14) | ~m1_subset_1(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.29/1.35  tff(c_10, plain, (![A_5]: (k3_tarski(k1_zfmisc_1(A_5))=A_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.29/1.35  tff(c_194, plain, (![A_46, B_47]: (r1_tarski(A_46, k3_tarski(B_47)) | ~r2_hidden(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.29/1.35  tff(c_260, plain, (![A_64, A_65]: (r1_tarski(A_64, A_65) | ~r2_hidden(A_64, k1_zfmisc_1(A_65)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_194])).
% 2.29/1.35  tff(c_264, plain, (![A_13, A_65]: (r1_tarski(A_13, A_65) | v1_xboole_0(k1_zfmisc_1(A_65)) | ~m1_subset_1(A_13, k1_zfmisc_1(A_65)))), inference(resolution, [status(thm)], [c_22, c_260])).
% 2.29/1.35  tff(c_267, plain, (![A_13, A_65]: (r1_tarski(A_13, A_65) | ~m1_subset_1(A_13, k1_zfmisc_1(A_65)))), inference(negUnitSimplification, [status(thm)], [c_12, c_264])).
% 2.29/1.35  tff(c_419, plain, (r1_tarski(k3_tarski('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_403, c_267])).
% 2.29/1.35  tff(c_14, plain, (![A_7, B_8]: (r1_tarski(A_7, k3_tarski(B_8)) | ~m1_setfam_1(B_8, A_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.29/1.35  tff(c_247, plain, (![B_62, A_63]: (B_62=A_63 | ~r1_tarski(B_62, A_63) | ~r1_tarski(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.29/1.35  tff(c_254, plain, (![B_8, A_7]: (k3_tarski(B_8)=A_7 | ~r1_tarski(k3_tarski(B_8), A_7) | ~m1_setfam_1(B_8, A_7))), inference(resolution, [status(thm)], [c_14, c_247])).
% 2.29/1.35  tff(c_422, plain, (k3_tarski('#skF_2')='#skF_1' | ~m1_setfam_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_419, c_254])).
% 2.29/1.35  tff(c_430, plain, (k3_tarski('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_191, c_422])).
% 2.29/1.35  tff(c_432, plain, $false, inference(negUnitSimplification, [status(thm)], [c_282, c_430])).
% 2.29/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.35  
% 2.29/1.35  Inference rules
% 2.29/1.35  ----------------------
% 2.29/1.35  #Ref     : 0
% 2.29/1.35  #Sup     : 81
% 2.29/1.35  #Fact    : 0
% 2.29/1.35  #Define  : 0
% 2.29/1.35  #Split   : 3
% 2.29/1.35  #Chain   : 0
% 2.29/1.35  #Close   : 0
% 2.29/1.35  
% 2.29/1.35  Ordering : KBO
% 2.29/1.35  
% 2.29/1.35  Simplification rules
% 2.29/1.35  ----------------------
% 2.29/1.35  #Subsume      : 3
% 2.29/1.35  #Demod        : 24
% 2.29/1.35  #Tautology    : 27
% 2.29/1.35  #SimpNegUnit  : 13
% 2.29/1.35  #BackRed      : 1
% 2.29/1.35  
% 2.29/1.35  #Partial instantiations: 0
% 2.29/1.35  #Strategies tried      : 1
% 2.29/1.35  
% 2.29/1.35  Timing (in seconds)
% 2.29/1.35  ----------------------
% 2.29/1.35  Preprocessing        : 0.31
% 2.29/1.35  Parsing              : 0.17
% 2.29/1.35  CNF conversion       : 0.02
% 2.29/1.35  Main loop            : 0.23
% 2.29/1.35  Inferencing          : 0.09
% 2.29/1.35  Reduction            : 0.06
% 2.29/1.35  Demodulation         : 0.04
% 2.29/1.35  BG Simplification    : 0.01
% 2.29/1.35  Subsumption          : 0.04
% 2.29/1.35  Abstraction          : 0.01
% 2.29/1.35  MUC search           : 0.00
% 2.29/1.35  Cooper               : 0.00
% 2.29/1.35  Total                : 0.57
% 2.29/1.35  Index Insertion      : 0.00
% 2.29/1.35  Index Deletion       : 0.00
% 2.29/1.35  Index Matching       : 0.00
% 2.29/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
