%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:34 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 100 expanded)
%              Number of leaves         :   25 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :   55 ( 160 expanded)
%              Number of equality atoms :   19 (  54 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k5_setfam_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(m1_setfam_1,type,(
    m1_setfam_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ~ ( m1_setfam_1(B,u1_struct_0(A))
                & B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tops_2)).

tff(f_31,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_32,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_34,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( m1_setfam_1(B,A)
      <=> k5_setfam_1(A,B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_setfam_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_28,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_41,plain,(
    ! [A_12] :
      ( A_12 = '#skF_3'
      | ~ v1_xboole_0(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2])).

tff(c_45,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_41])).

tff(c_22,plain,(
    m1_setfam_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_61,plain,(
    m1_setfam_1('#skF_1',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_22])).

tff(c_6,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_31,plain,(
    k3_tarski('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_6])).

tff(c_47,plain,(
    k3_tarski('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_45,c_31])).

tff(c_8,plain,(
    ! [A_2] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_29,plain,(
    ! [A_2] : m1_subset_1('#skF_3',k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_8])).

tff(c_62,plain,(
    ! [A_2] : m1_subset_1('#skF_1',k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_29])).

tff(c_71,plain,(
    ! [A_16,B_17] :
      ( k5_setfam_1(A_16,B_17) = k3_tarski(B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k1_zfmisc_1(A_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_75,plain,(
    ! [A_16] : k5_setfam_1(A_16,'#skF_1') = k3_tarski('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_71])).

tff(c_77,plain,(
    ! [A_16] : k5_setfam_1(A_16,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_75])).

tff(c_90,plain,(
    ! [A_24,B_25] :
      ( k5_setfam_1(A_24,B_25) = A_24
      | ~ m1_setfam_1(B_25,A_24)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(k1_zfmisc_1(A_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_94,plain,(
    ! [A_24] :
      ( k5_setfam_1(A_24,'#skF_1') = A_24
      | ~ m1_setfam_1('#skF_1',A_24) ) ),
    inference(resolution,[status(thm)],[c_62,c_90])).

tff(c_97,plain,(
    ! [A_26] :
      ( A_26 = '#skF_1'
      | ~ m1_setfam_1('#skF_1',A_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_94])).

tff(c_101,plain,(
    u1_struct_0('#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_61,c_97])).

tff(c_18,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(u1_struct_0(A_10))
      | ~ l1_struct_0(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_106,plain,
    ( ~ v1_xboole_0('#skF_1')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_18])).

tff(c_110,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_4,c_106])).

tff(c_112,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_110])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:54:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.12  
% 1.67/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.13  %$ r2_hidden > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k5_setfam_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.67/1.13  
% 1.67/1.13  %Foreground sorts:
% 1.67/1.13  
% 1.67/1.13  
% 1.67/1.13  %Background operators:
% 1.67/1.13  
% 1.67/1.13  
% 1.67/1.13  %Foreground operators:
% 1.67/1.13  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.67/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.67/1.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.67/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.67/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.13  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 1.67/1.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.67/1.13  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.67/1.13  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 1.67/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.13  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.67/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.13  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.67/1.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.67/1.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.67/1.13  
% 1.67/1.14  tff(f_72, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~(m1_setfam_1(B, u1_struct_0(A)) & (B = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_tops_2)).
% 1.67/1.14  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 1.67/1.14  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.67/1.14  tff(f_32, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 1.67/1.14  tff(f_34, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 1.67/1.14  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 1.67/1.14  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (m1_setfam_1(B, A) <=> (k5_setfam_1(A, B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_setfam_1)).
% 1.67/1.14  tff(f_58, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 1.67/1.14  tff(c_28, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.67/1.14  tff(c_26, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.67/1.14  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.67/1.14  tff(c_20, plain, (k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.67/1.14  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.67/1.14  tff(c_41, plain, (![A_12]: (A_12='#skF_3' | ~v1_xboole_0(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2])).
% 1.67/1.14  tff(c_45, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_4, c_41])).
% 1.67/1.14  tff(c_22, plain, (m1_setfam_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.67/1.14  tff(c_61, plain, (m1_setfam_1('#skF_1', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_22])).
% 1.67/1.14  tff(c_6, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.67/1.14  tff(c_31, plain, (k3_tarski('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_6])).
% 1.67/1.14  tff(c_47, plain, (k3_tarski('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_45, c_45, c_31])).
% 1.67/1.14  tff(c_8, plain, (![A_2]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.67/1.14  tff(c_29, plain, (![A_2]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_8])).
% 1.67/1.14  tff(c_62, plain, (![A_2]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_29])).
% 1.67/1.14  tff(c_71, plain, (![A_16, B_17]: (k5_setfam_1(A_16, B_17)=k3_tarski(B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(k1_zfmisc_1(A_16))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.67/1.14  tff(c_75, plain, (![A_16]: (k5_setfam_1(A_16, '#skF_1')=k3_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_62, c_71])).
% 1.67/1.14  tff(c_77, plain, (![A_16]: (k5_setfam_1(A_16, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_75])).
% 1.67/1.14  tff(c_90, plain, (![A_24, B_25]: (k5_setfam_1(A_24, B_25)=A_24 | ~m1_setfam_1(B_25, A_24) | ~m1_subset_1(B_25, k1_zfmisc_1(k1_zfmisc_1(A_24))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.67/1.14  tff(c_94, plain, (![A_24]: (k5_setfam_1(A_24, '#skF_1')=A_24 | ~m1_setfam_1('#skF_1', A_24))), inference(resolution, [status(thm)], [c_62, c_90])).
% 1.67/1.14  tff(c_97, plain, (![A_26]: (A_26='#skF_1' | ~m1_setfam_1('#skF_1', A_26))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_94])).
% 1.67/1.14  tff(c_101, plain, (u1_struct_0('#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_61, c_97])).
% 1.67/1.14  tff(c_18, plain, (![A_10]: (~v1_xboole_0(u1_struct_0(A_10)) | ~l1_struct_0(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.67/1.14  tff(c_106, plain, (~v1_xboole_0('#skF_1') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_101, c_18])).
% 1.67/1.14  tff(c_110, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_4, c_106])).
% 1.67/1.14  tff(c_112, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_110])).
% 1.67/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.14  
% 1.67/1.14  Inference rules
% 1.67/1.14  ----------------------
% 1.67/1.14  #Ref     : 0
% 1.67/1.14  #Sup     : 21
% 1.67/1.14  #Fact    : 0
% 1.67/1.14  #Define  : 0
% 1.67/1.14  #Split   : 0
% 1.67/1.14  #Chain   : 0
% 1.67/1.14  #Close   : 0
% 1.67/1.14  
% 1.67/1.14  Ordering : KBO
% 1.67/1.14  
% 1.67/1.14  Simplification rules
% 1.67/1.14  ----------------------
% 1.67/1.14  #Subsume      : 0
% 1.67/1.14  #Demod        : 16
% 1.67/1.14  #Tautology    : 15
% 1.67/1.14  #SimpNegUnit  : 1
% 1.67/1.14  #BackRed      : 4
% 1.67/1.14  
% 1.67/1.14  #Partial instantiations: 0
% 1.67/1.14  #Strategies tried      : 1
% 1.67/1.14  
% 1.67/1.14  Timing (in seconds)
% 1.67/1.14  ----------------------
% 1.67/1.14  Preprocessing        : 0.27
% 1.67/1.14  Parsing              : 0.14
% 1.67/1.14  CNF conversion       : 0.02
% 1.67/1.14  Main loop            : 0.10
% 1.67/1.14  Inferencing          : 0.04
% 1.67/1.14  Reduction            : 0.04
% 1.67/1.14  Demodulation         : 0.03
% 1.67/1.14  BG Simplification    : 0.01
% 1.67/1.14  Subsumption          : 0.01
% 1.67/1.14  Abstraction          : 0.00
% 1.67/1.14  MUC search           : 0.00
% 1.67/1.14  Cooper               : 0.00
% 1.67/1.14  Total                : 0.40
% 1.67/1.14  Index Insertion      : 0.00
% 1.67/1.14  Index Deletion       : 0.00
% 1.67/1.14  Index Matching       : 0.00
% 1.67/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
