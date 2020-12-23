%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:04 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 104 expanded)
%              Number of leaves         :   25 (  45 expanded)
%              Depth                    :    9
%              Number of atoms          :   80 ( 169 expanded)
%              Number of equality atoms :   18 (  42 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v1_xboole_0 > k5_setfam_1 > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( m1_setfam_1(B,A)
        <=> k5_setfam_1(A,B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_setfam_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_199,plain,(
    ! [A_56,B_57] :
      ( k5_setfam_1(A_56,B_57) = k3_tarski(B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(k1_zfmisc_1(A_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_207,plain,(
    k5_setfam_1('#skF_4','#skF_5') = k3_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_199])).

tff(c_40,plain,
    ( k5_setfam_1('#skF_4','#skF_5') != '#skF_4'
    | ~ m1_setfam_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_82,plain,(
    ~ m1_setfam_1('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_46,plain,
    ( m1_setfam_1('#skF_5','#skF_4')
    | k5_setfam_1('#skF_4','#skF_5') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_83,plain,(
    k5_setfam_1('#skF_4','#skF_5') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_46])).

tff(c_129,plain,(
    ! [A_44,B_45] :
      ( k5_setfam_1(A_44,B_45) = k3_tarski(B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(k1_zfmisc_1(A_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_132,plain,(
    k5_setfam_1('#skF_4','#skF_5') = k3_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_129])).

tff(c_138,plain,(
    k3_tarski('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_132])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_89,plain,(
    ! [B_36,A_37] :
      ( m1_setfam_1(B_36,A_37)
      | ~ r1_tarski(A_37,k3_tarski(B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_98,plain,(
    ! [B_36] : m1_setfam_1(B_36,k3_tarski(B_36)) ),
    inference(resolution,[status(thm)],[c_10,c_89])).

tff(c_143,plain,(
    m1_setfam_1('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_98])).

tff(c_153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_143])).

tff(c_154,plain,(
    k5_setfam_1('#skF_4','#skF_5') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_209,plain,(
    k3_tarski('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_154])).

tff(c_155,plain,(
    m1_setfam_1('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_290,plain,(
    ! [A_67,B_68] :
      ( m1_subset_1(k5_setfam_1(A_67,B_68),k1_zfmisc_1(A_67))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(k1_zfmisc_1(A_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_303,plain,
    ( m1_subset_1(k3_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_290])).

tff(c_309,plain,(
    m1_subset_1(k3_tarski('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_303])).

tff(c_180,plain,(
    ! [A_53,B_54] :
      ( r2_hidden(A_53,B_54)
      | v1_xboole_0(B_54)
      | ~ m1_subset_1(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_12,plain,(
    ! [C_11,A_7] :
      ( r1_tarski(C_11,A_7)
      | ~ r2_hidden(C_11,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_188,plain,(
    ! [A_53,A_7] :
      ( r1_tarski(A_53,A_7)
      | v1_xboole_0(k1_zfmisc_1(A_7))
      | ~ m1_subset_1(A_53,k1_zfmisc_1(A_7)) ) ),
    inference(resolution,[status(thm)],[c_180,c_12])).

tff(c_323,plain,
    ( r1_tarski(k3_tarski('#skF_5'),'#skF_4')
    | v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_309,c_188])).

tff(c_334,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_323])).

tff(c_66,plain,(
    ! [C_28,A_29] :
      ( r2_hidden(C_28,k1_zfmisc_1(A_29))
      | ~ r1_tarski(C_28,A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    ! [A_29,C_28] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_29))
      | ~ r1_tarski(C_28,A_29) ) ),
    inference(resolution,[status(thm)],[c_66,c_2])).

tff(c_338,plain,(
    ! [C_72] : ~ r1_tarski(C_72,'#skF_4') ),
    inference(resolution,[status(thm)],[c_334,c_70])).

tff(c_349,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_10,c_338])).

tff(c_350,plain,(
    r1_tarski(k3_tarski('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_323])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,k3_tarski(B_15))
      | ~ m1_setfam_1(B_15,A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_170,plain,(
    ! [B_51,A_52] :
      ( B_51 = A_52
      | ~ r1_tarski(B_51,A_52)
      | ~ r1_tarski(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_175,plain,(
    ! [B_15,A_14] :
      ( k3_tarski(B_15) = A_14
      | ~ r1_tarski(k3_tarski(B_15),A_14)
      | ~ m1_setfam_1(B_15,A_14) ) ),
    inference(resolution,[status(thm)],[c_28,c_170])).

tff(c_354,plain,
    ( k3_tarski('#skF_5') = '#skF_4'
    | ~ m1_setfam_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_350,c_175])).

tff(c_359,plain,(
    k3_tarski('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_354])).

tff(c_361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_209,c_359])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:05:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.30  
% 2.08/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.31  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v1_xboole_0 > k5_setfam_1 > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 2.08/1.31  
% 2.08/1.31  %Foreground sorts:
% 2.08/1.31  
% 2.08/1.31  
% 2.08/1.31  %Background operators:
% 2.08/1.31  
% 2.08/1.31  
% 2.08/1.31  %Foreground operators:
% 2.08/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.08/1.31  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.08/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.08/1.31  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 2.08/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.08/1.31  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.08/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.08/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.08/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.08/1.31  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.08/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.08/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.08/1.31  
% 2.32/1.32  tff(f_73, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (m1_setfam_1(B, A) <=> (k5_setfam_1(A, B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_setfam_1)).
% 2.32/1.32  tff(f_60, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 2.32/1.32  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.32/1.32  tff(f_52, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_setfam_1)).
% 2.32/1.32  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 2.32/1.32  tff(f_66, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.32/1.32  tff(f_44, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.32/1.32  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.32/1.32  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.32/1.32  tff(c_199, plain, (![A_56, B_57]: (k5_setfam_1(A_56, B_57)=k3_tarski(B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(k1_zfmisc_1(A_56))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.32/1.32  tff(c_207, plain, (k5_setfam_1('#skF_4', '#skF_5')=k3_tarski('#skF_5')), inference(resolution, [status(thm)], [c_38, c_199])).
% 2.32/1.32  tff(c_40, plain, (k5_setfam_1('#skF_4', '#skF_5')!='#skF_4' | ~m1_setfam_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.32/1.32  tff(c_82, plain, (~m1_setfam_1('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_40])).
% 2.32/1.32  tff(c_46, plain, (m1_setfam_1('#skF_5', '#skF_4') | k5_setfam_1('#skF_4', '#skF_5')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.32/1.32  tff(c_83, plain, (k5_setfam_1('#skF_4', '#skF_5')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_82, c_46])).
% 2.32/1.32  tff(c_129, plain, (![A_44, B_45]: (k5_setfam_1(A_44, B_45)=k3_tarski(B_45) | ~m1_subset_1(B_45, k1_zfmisc_1(k1_zfmisc_1(A_44))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.32/1.32  tff(c_132, plain, (k5_setfam_1('#skF_4', '#skF_5')=k3_tarski('#skF_5')), inference(resolution, [status(thm)], [c_38, c_129])).
% 2.32/1.32  tff(c_138, plain, (k3_tarski('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_83, c_132])).
% 2.32/1.32  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.32/1.32  tff(c_89, plain, (![B_36, A_37]: (m1_setfam_1(B_36, A_37) | ~r1_tarski(A_37, k3_tarski(B_36)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.32/1.32  tff(c_98, plain, (![B_36]: (m1_setfam_1(B_36, k3_tarski(B_36)))), inference(resolution, [status(thm)], [c_10, c_89])).
% 2.32/1.32  tff(c_143, plain, (m1_setfam_1('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_138, c_98])).
% 2.32/1.32  tff(c_153, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_143])).
% 2.32/1.32  tff(c_154, plain, (k5_setfam_1('#skF_4', '#skF_5')!='#skF_4'), inference(splitRight, [status(thm)], [c_40])).
% 2.32/1.32  tff(c_209, plain, (k3_tarski('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_207, c_154])).
% 2.32/1.32  tff(c_155, plain, (m1_setfam_1('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_40])).
% 2.32/1.32  tff(c_290, plain, (![A_67, B_68]: (m1_subset_1(k5_setfam_1(A_67, B_68), k1_zfmisc_1(A_67)) | ~m1_subset_1(B_68, k1_zfmisc_1(k1_zfmisc_1(A_67))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.32/1.32  tff(c_303, plain, (m1_subset_1(k3_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_207, c_290])).
% 2.32/1.32  tff(c_309, plain, (m1_subset_1(k3_tarski('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_303])).
% 2.32/1.32  tff(c_180, plain, (![A_53, B_54]: (r2_hidden(A_53, B_54) | v1_xboole_0(B_54) | ~m1_subset_1(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.32/1.32  tff(c_12, plain, (![C_11, A_7]: (r1_tarski(C_11, A_7) | ~r2_hidden(C_11, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.32/1.32  tff(c_188, plain, (![A_53, A_7]: (r1_tarski(A_53, A_7) | v1_xboole_0(k1_zfmisc_1(A_7)) | ~m1_subset_1(A_53, k1_zfmisc_1(A_7)))), inference(resolution, [status(thm)], [c_180, c_12])).
% 2.32/1.32  tff(c_323, plain, (r1_tarski(k3_tarski('#skF_5'), '#skF_4') | v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_309, c_188])).
% 2.32/1.32  tff(c_334, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_323])).
% 2.32/1.32  tff(c_66, plain, (![C_28, A_29]: (r2_hidden(C_28, k1_zfmisc_1(A_29)) | ~r1_tarski(C_28, A_29))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.32/1.32  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.32/1.32  tff(c_70, plain, (![A_29, C_28]: (~v1_xboole_0(k1_zfmisc_1(A_29)) | ~r1_tarski(C_28, A_29))), inference(resolution, [status(thm)], [c_66, c_2])).
% 2.32/1.32  tff(c_338, plain, (![C_72]: (~r1_tarski(C_72, '#skF_4'))), inference(resolution, [status(thm)], [c_334, c_70])).
% 2.32/1.32  tff(c_349, plain, $false, inference(resolution, [status(thm)], [c_10, c_338])).
% 2.32/1.32  tff(c_350, plain, (r1_tarski(k3_tarski('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_323])).
% 2.32/1.32  tff(c_28, plain, (![A_14, B_15]: (r1_tarski(A_14, k3_tarski(B_15)) | ~m1_setfam_1(B_15, A_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.32/1.32  tff(c_170, plain, (![B_51, A_52]: (B_51=A_52 | ~r1_tarski(B_51, A_52) | ~r1_tarski(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.32/1.32  tff(c_175, plain, (![B_15, A_14]: (k3_tarski(B_15)=A_14 | ~r1_tarski(k3_tarski(B_15), A_14) | ~m1_setfam_1(B_15, A_14))), inference(resolution, [status(thm)], [c_28, c_170])).
% 2.32/1.32  tff(c_354, plain, (k3_tarski('#skF_5')='#skF_4' | ~m1_setfam_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_350, c_175])).
% 2.32/1.32  tff(c_359, plain, (k3_tarski('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_155, c_354])).
% 2.32/1.32  tff(c_361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_209, c_359])).
% 2.32/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.32  
% 2.32/1.32  Inference rules
% 2.32/1.32  ----------------------
% 2.32/1.32  #Ref     : 0
% 2.32/1.32  #Sup     : 63
% 2.32/1.32  #Fact    : 0
% 2.32/1.32  #Define  : 0
% 2.32/1.32  #Split   : 4
% 2.32/1.32  #Chain   : 0
% 2.32/1.32  #Close   : 0
% 2.32/1.32  
% 2.32/1.32  Ordering : KBO
% 2.32/1.32  
% 2.32/1.32  Simplification rules
% 2.32/1.32  ----------------------
% 2.32/1.32  #Subsume      : 1
% 2.32/1.32  #Demod        : 16
% 2.32/1.32  #Tautology    : 25
% 2.32/1.32  #SimpNegUnit  : 4
% 2.32/1.32  #BackRed      : 1
% 2.32/1.32  
% 2.32/1.32  #Partial instantiations: 0
% 2.32/1.32  #Strategies tried      : 1
% 2.32/1.32  
% 2.32/1.32  Timing (in seconds)
% 2.32/1.32  ----------------------
% 2.32/1.32  Preprocessing        : 0.29
% 2.32/1.32  Parsing              : 0.15
% 2.32/1.32  CNF conversion       : 0.02
% 2.32/1.32  Main loop            : 0.22
% 2.32/1.32  Inferencing          : 0.08
% 2.32/1.32  Reduction            : 0.06
% 2.32/1.32  Demodulation         : 0.04
% 2.32/1.32  BG Simplification    : 0.01
% 2.32/1.32  Subsumption          : 0.04
% 2.32/1.32  Abstraction          : 0.01
% 2.32/1.32  MUC search           : 0.00
% 2.32/1.32  Cooper               : 0.00
% 2.32/1.32  Total                : 0.54
% 2.32/1.32  Index Insertion      : 0.00
% 2.32/1.32  Index Deletion       : 0.00
% 2.32/1.32  Index Matching       : 0.00
% 2.32/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
