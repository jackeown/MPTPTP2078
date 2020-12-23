%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:05 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 103 expanded)
%              Number of leaves         :   26 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :   90 ( 165 expanded)
%              Number of equality atoms :   18 (  39 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v1_xboole_0 > k5_setfam_1 > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( m1_setfam_1(B,A)
        <=> k5_setfam_1(A,B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_setfam_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_40,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,
    ( m1_setfam_1('#skF_4','#skF_3')
    | k5_setfam_1('#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_76,plain,(
    k5_setfam_1('#skF_3','#skF_4') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_38,plain,
    ( k5_setfam_1('#skF_3','#skF_4') != '#skF_3'
    | ~ m1_setfam_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_82,plain,(
    ~ m1_setfam_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_38])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_106,plain,(
    ! [A_40,B_41] :
      ( k5_setfam_1(A_40,B_41) = k3_tarski(B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(k1_zfmisc_1(A_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_109,plain,(
    k5_setfam_1('#skF_3','#skF_4') = k3_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_106])).

tff(c_115,plain,(
    k3_tarski('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_109])).

tff(c_60,plain,(
    ! [B_28,A_29] :
      ( m1_setfam_1(B_28,A_29)
      | ~ r1_tarski(A_29,k3_tarski(B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_69,plain,(
    ! [B_28] : m1_setfam_1(B_28,k3_tarski(B_28)) ),
    inference(resolution,[status(thm)],[c_6,c_60])).

tff(c_120,plain,(
    m1_setfam_1('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_69])).

tff(c_130,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_120])).

tff(c_131,plain,(
    m1_setfam_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_24,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,k3_tarski(B_11))
      | ~ m1_setfam_1(B_11,A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_168,plain,(
    ! [A_51,B_52] :
      ( k5_setfam_1(A_51,B_52) = k3_tarski(B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(k1_zfmisc_1(A_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_176,plain,(
    k5_setfam_1('#skF_3','#skF_4') = k3_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_168])).

tff(c_132,plain,(
    k5_setfam_1('#skF_3','#skF_4') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_178,plain,(
    k3_tarski('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_132])).

tff(c_151,plain,(
    ! [C_46,B_47,A_48] :
      ( ~ v1_xboole_0(C_46)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(C_46))
      | ~ r2_hidden(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_156,plain,(
    ! [A_48] :
      ( ~ v1_xboole_0(k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(A_48,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_151])).

tff(c_167,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_183,plain,(
    ! [A_53,B_54] :
      ( m1_subset_1(k5_setfam_1(A_53,B_54),k1_zfmisc_1(A_53))
      | ~ m1_subset_1(B_54,k1_zfmisc_1(k1_zfmisc_1(A_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_192,plain,
    ( m1_subset_1(k3_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_183])).

tff(c_196,plain,(
    m1_subset_1(k3_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_192])).

tff(c_145,plain,(
    ! [A_44,B_45] :
      ( r2_hidden(A_44,B_45)
      | v1_xboole_0(B_45)
      | ~ m1_subset_1(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8,plain,(
    ! [C_7,A_3] :
      ( r1_tarski(C_7,A_3)
      | ~ r2_hidden(C_7,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_237,plain,(
    ! [A_63,A_64] :
      ( r1_tarski(A_63,A_64)
      | v1_xboole_0(k1_zfmisc_1(A_64))
      | ~ m1_subset_1(A_63,k1_zfmisc_1(A_64)) ) ),
    inference(resolution,[status(thm)],[c_145,c_8])).

tff(c_243,plain,
    ( r1_tarski(k3_tarski('#skF_4'),'#skF_3')
    | v1_xboole_0(k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_196,c_237])).

tff(c_256,plain,(
    r1_tarski(k3_tarski('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_243])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_305,plain,
    ( k3_tarski('#skF_4') = '#skF_3'
    | ~ r1_tarski('#skF_3',k3_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_256,c_2])).

tff(c_308,plain,(
    ~ r1_tarski('#skF_3',k3_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_305])).

tff(c_311,plain,(
    ~ m1_setfam_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_308])).

tff(c_315,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_311])).

tff(c_317,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_10,plain,(
    ! [C_7,A_3] :
      ( r2_hidden(C_7,k1_zfmisc_1(A_3))
      | ~ r1_tarski(C_7,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_20,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_22,plain,(
    ! [A_9] : m1_subset_1(k2_subset_1(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_45,plain,(
    ! [A_9] : m1_subset_1(A_9,k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_158,plain,(
    ! [A_49,A_50] :
      ( ~ v1_xboole_0(A_49)
      | ~ r2_hidden(A_50,A_49) ) ),
    inference(resolution,[status(thm)],[c_45,c_151])).

tff(c_326,plain,(
    ! [A_70,C_71] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_70))
      | ~ r1_tarski(C_71,A_70) ) ),
    inference(resolution,[status(thm)],[c_10,c_158])).

tff(c_330,plain,(
    ! [C_72] : ~ r1_tarski(C_72,'#skF_3') ),
    inference(resolution,[status(thm)],[c_317,c_326])).

tff(c_335,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_330])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:02:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.25  
% 2.13/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.25  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v1_xboole_0 > k5_setfam_1 > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.13/1.25  
% 2.13/1.25  %Foreground sorts:
% 2.13/1.25  
% 2.13/1.25  
% 2.13/1.25  %Background operators:
% 2.13/1.25  
% 2.13/1.25  
% 2.13/1.25  %Foreground operators:
% 2.13/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.13/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.13/1.25  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 2.13/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.13/1.25  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.13/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.25  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.13/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.13/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.25  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.13/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.13/1.25  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.13/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.13/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.13/1.25  
% 2.13/1.26  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.13/1.26  tff(f_74, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (m1_setfam_1(B, A) <=> (k5_setfam_1(A, B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_setfam_1)).
% 2.13/1.26  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 2.13/1.26  tff(f_46, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_setfam_1)).
% 2.13/1.26  tff(f_67, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.13/1.26  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 2.13/1.26  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.13/1.26  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.13/1.26  tff(f_40, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.13/1.26  tff(f_42, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.13/1.26  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.13/1.26  tff(c_44, plain, (m1_setfam_1('#skF_4', '#skF_3') | k5_setfam_1('#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.13/1.26  tff(c_76, plain, (k5_setfam_1('#skF_3', '#skF_4')='#skF_3'), inference(splitLeft, [status(thm)], [c_44])).
% 2.13/1.26  tff(c_38, plain, (k5_setfam_1('#skF_3', '#skF_4')!='#skF_3' | ~m1_setfam_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.13/1.26  tff(c_82, plain, (~m1_setfam_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_38])).
% 2.13/1.26  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.13/1.26  tff(c_106, plain, (![A_40, B_41]: (k5_setfam_1(A_40, B_41)=k3_tarski(B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(k1_zfmisc_1(A_40))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.13/1.26  tff(c_109, plain, (k5_setfam_1('#skF_3', '#skF_4')=k3_tarski('#skF_4')), inference(resolution, [status(thm)], [c_36, c_106])).
% 2.13/1.26  tff(c_115, plain, (k3_tarski('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_109])).
% 2.13/1.26  tff(c_60, plain, (![B_28, A_29]: (m1_setfam_1(B_28, A_29) | ~r1_tarski(A_29, k3_tarski(B_28)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.13/1.26  tff(c_69, plain, (![B_28]: (m1_setfam_1(B_28, k3_tarski(B_28)))), inference(resolution, [status(thm)], [c_6, c_60])).
% 2.13/1.26  tff(c_120, plain, (m1_setfam_1('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_115, c_69])).
% 2.13/1.26  tff(c_130, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_120])).
% 2.13/1.26  tff(c_131, plain, (m1_setfam_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 2.13/1.26  tff(c_24, plain, (![A_10, B_11]: (r1_tarski(A_10, k3_tarski(B_11)) | ~m1_setfam_1(B_11, A_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.13/1.26  tff(c_168, plain, (![A_51, B_52]: (k5_setfam_1(A_51, B_52)=k3_tarski(B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(k1_zfmisc_1(A_51))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.13/1.26  tff(c_176, plain, (k5_setfam_1('#skF_3', '#skF_4')=k3_tarski('#skF_4')), inference(resolution, [status(thm)], [c_36, c_168])).
% 2.13/1.26  tff(c_132, plain, (k5_setfam_1('#skF_3', '#skF_4')!='#skF_3'), inference(splitRight, [status(thm)], [c_44])).
% 2.13/1.26  tff(c_178, plain, (k3_tarski('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_176, c_132])).
% 2.13/1.26  tff(c_151, plain, (![C_46, B_47, A_48]: (~v1_xboole_0(C_46) | ~m1_subset_1(B_47, k1_zfmisc_1(C_46)) | ~r2_hidden(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.13/1.26  tff(c_156, plain, (![A_48]: (~v1_xboole_0(k1_zfmisc_1('#skF_3')) | ~r2_hidden(A_48, '#skF_4'))), inference(resolution, [status(thm)], [c_36, c_151])).
% 2.13/1.26  tff(c_167, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_156])).
% 2.13/1.26  tff(c_183, plain, (![A_53, B_54]: (m1_subset_1(k5_setfam_1(A_53, B_54), k1_zfmisc_1(A_53)) | ~m1_subset_1(B_54, k1_zfmisc_1(k1_zfmisc_1(A_53))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.13/1.26  tff(c_192, plain, (m1_subset_1(k3_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_176, c_183])).
% 2.13/1.26  tff(c_196, plain, (m1_subset_1(k3_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_192])).
% 2.13/1.26  tff(c_145, plain, (![A_44, B_45]: (r2_hidden(A_44, B_45) | v1_xboole_0(B_45) | ~m1_subset_1(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.13/1.26  tff(c_8, plain, (![C_7, A_3]: (r1_tarski(C_7, A_3) | ~r2_hidden(C_7, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.13/1.26  tff(c_237, plain, (![A_63, A_64]: (r1_tarski(A_63, A_64) | v1_xboole_0(k1_zfmisc_1(A_64)) | ~m1_subset_1(A_63, k1_zfmisc_1(A_64)))), inference(resolution, [status(thm)], [c_145, c_8])).
% 2.13/1.26  tff(c_243, plain, (r1_tarski(k3_tarski('#skF_4'), '#skF_3') | v1_xboole_0(k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_196, c_237])).
% 2.13/1.26  tff(c_256, plain, (r1_tarski(k3_tarski('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_167, c_243])).
% 2.13/1.26  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.13/1.26  tff(c_305, plain, (k3_tarski('#skF_4')='#skF_3' | ~r1_tarski('#skF_3', k3_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_256, c_2])).
% 2.13/1.26  tff(c_308, plain, (~r1_tarski('#skF_3', k3_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_178, c_305])).
% 2.13/1.26  tff(c_311, plain, (~m1_setfam_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_308])).
% 2.13/1.26  tff(c_315, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131, c_311])).
% 2.13/1.26  tff(c_317, plain, (v1_xboole_0(k1_zfmisc_1('#skF_3'))), inference(splitRight, [status(thm)], [c_156])).
% 2.13/1.26  tff(c_10, plain, (![C_7, A_3]: (r2_hidden(C_7, k1_zfmisc_1(A_3)) | ~r1_tarski(C_7, A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.13/1.26  tff(c_20, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.13/1.26  tff(c_22, plain, (![A_9]: (m1_subset_1(k2_subset_1(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.13/1.26  tff(c_45, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22])).
% 2.13/1.26  tff(c_158, plain, (![A_49, A_50]: (~v1_xboole_0(A_49) | ~r2_hidden(A_50, A_49))), inference(resolution, [status(thm)], [c_45, c_151])).
% 2.13/1.26  tff(c_326, plain, (![A_70, C_71]: (~v1_xboole_0(k1_zfmisc_1(A_70)) | ~r1_tarski(C_71, A_70))), inference(resolution, [status(thm)], [c_10, c_158])).
% 2.13/1.26  tff(c_330, plain, (![C_72]: (~r1_tarski(C_72, '#skF_3'))), inference(resolution, [status(thm)], [c_317, c_326])).
% 2.13/1.26  tff(c_335, plain, $false, inference(resolution, [status(thm)], [c_6, c_330])).
% 2.13/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.26  
% 2.13/1.26  Inference rules
% 2.13/1.26  ----------------------
% 2.13/1.26  #Ref     : 0
% 2.13/1.26  #Sup     : 60
% 2.13/1.26  #Fact    : 0
% 2.13/1.26  #Define  : 0
% 2.13/1.26  #Split   : 5
% 2.13/1.26  #Chain   : 0
% 2.13/1.26  #Close   : 0
% 2.13/1.26  
% 2.13/1.26  Ordering : KBO
% 2.13/1.26  
% 2.13/1.26  Simplification rules
% 2.13/1.26  ----------------------
% 2.13/1.26  #Subsume      : 1
% 2.13/1.26  #Demod        : 12
% 2.13/1.26  #Tautology    : 18
% 2.13/1.26  #SimpNegUnit  : 4
% 2.13/1.26  #BackRed      : 1
% 2.13/1.26  
% 2.13/1.26  #Partial instantiations: 0
% 2.13/1.26  #Strategies tried      : 1
% 2.13/1.26  
% 2.13/1.26  Timing (in seconds)
% 2.13/1.26  ----------------------
% 2.13/1.27  Preprocessing        : 0.30
% 2.13/1.27  Parsing              : 0.16
% 2.13/1.27  CNF conversion       : 0.02
% 2.13/1.27  Main loop            : 0.21
% 2.13/1.27  Inferencing          : 0.08
% 2.13/1.27  Reduction            : 0.06
% 2.13/1.27  Demodulation         : 0.04
% 2.13/1.27  BG Simplification    : 0.01
% 2.13/1.27  Subsumption          : 0.04
% 2.13/1.27  Abstraction          : 0.01
% 2.13/1.27  MUC search           : 0.00
% 2.13/1.27  Cooper               : 0.00
% 2.13/1.27  Total                : 0.54
% 2.13/1.27  Index Insertion      : 0.00
% 2.13/1.27  Index Deletion       : 0.00
% 2.13/1.27  Index Matching       : 0.00
% 2.13/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
