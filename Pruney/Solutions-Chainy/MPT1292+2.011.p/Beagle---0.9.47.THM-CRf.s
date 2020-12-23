%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:30 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   49 (  82 expanded)
%              Number of leaves         :   24 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :   62 ( 142 expanded)
%              Number of equality atoms :   15 (  39 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(f_70,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ~ ( m1_setfam_1(B,u1_struct_0(A))
                & B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tops_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_44,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_38,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_30,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_24,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_36,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2])).

tff(c_26,plain,(
    m1_setfam_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_34,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_10])).

tff(c_16,plain,(
    ! [A_7] : k3_tarski(k1_zfmisc_1(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_130,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(k3_tarski(A_30),k3_tarski(B_31))
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_177,plain,(
    ! [A_38,A_39] :
      ( r1_tarski(k3_tarski(A_38),A_39)
      | ~ r1_tarski(A_38,k1_zfmisc_1(A_39)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_130])).

tff(c_12,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_33,plain,(
    ! [A_4] :
      ( A_4 = '#skF_2'
      | ~ r1_tarski(A_4,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_12])).

tff(c_194,plain,(
    ! [A_40] :
      ( k3_tarski(A_40) = '#skF_2'
      | ~ r1_tarski(A_40,k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_177,c_33])).

tff(c_208,plain,(
    k3_tarski('#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_34,c_194])).

tff(c_18,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,k3_tarski(B_9))
      | ~ m1_setfam_1(B_9,A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_93,plain,(
    ! [B_23,A_24] :
      ( B_23 = A_24
      | ~ r1_tarski(B_23,A_24)
      | ~ r1_tarski(A_24,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_100,plain,(
    ! [B_9,A_8] :
      ( k3_tarski(B_9) = A_8
      | ~ r1_tarski(k3_tarski(B_9),A_8)
      | ~ m1_setfam_1(B_9,A_8) ) ),
    inference(resolution,[status(thm)],[c_18,c_93])).

tff(c_240,plain,(
    ! [A_8] :
      ( k3_tarski('#skF_2') = A_8
      | ~ r1_tarski('#skF_2',A_8)
      | ~ m1_setfam_1('#skF_2',A_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_100])).

tff(c_274,plain,(
    ! [A_43] :
      ( A_43 = '#skF_2'
      | ~ m1_setfam_1('#skF_2',A_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_208,c_240])).

tff(c_295,plain,(
    u1_struct_0('#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_26,c_274])).

tff(c_22,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(u1_struct_0(A_10))
      | ~ l1_struct_0(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_302,plain,
    ( ~ v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_22])).

tff(c_306,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_36,c_302])).

tff(c_308,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_306])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n014.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:15:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.27  
% 1.98/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.27  %$ r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.98/1.27  
% 1.98/1.27  %Foreground sorts:
% 1.98/1.27  
% 1.98/1.27  
% 1.98/1.27  %Background operators:
% 1.98/1.27  
% 1.98/1.27  
% 1.98/1.27  %Foreground operators:
% 1.98/1.27  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.98/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.98/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.98/1.27  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.27  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.27  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 1.98/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.98/1.27  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.98/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.27  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.98/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.98/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.98/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.98/1.27  
% 1.98/1.28  tff(f_70, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~(m1_setfam_1(B, u1_struct_0(A)) & (B = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_tops_2)).
% 1.98/1.28  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.98/1.28  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.98/1.28  tff(f_44, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 1.98/1.28  tff(f_42, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 1.98/1.28  tff(f_38, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.98/1.28  tff(f_48, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_setfam_1)).
% 1.98/1.28  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.98/1.28  tff(f_56, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 1.98/1.28  tff(c_32, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.98/1.28  tff(c_30, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.98/1.28  tff(c_24, plain, (k1_xboole_0='#skF_2'), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.98/1.28  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.98/1.28  tff(c_36, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2])).
% 1.98/1.28  tff(c_26, plain, (m1_setfam_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.98/1.28  tff(c_10, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.98/1.28  tff(c_34, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_10])).
% 1.98/1.28  tff(c_16, plain, (![A_7]: (k3_tarski(k1_zfmisc_1(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.98/1.28  tff(c_130, plain, (![A_30, B_31]: (r1_tarski(k3_tarski(A_30), k3_tarski(B_31)) | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.98/1.28  tff(c_177, plain, (![A_38, A_39]: (r1_tarski(k3_tarski(A_38), A_39) | ~r1_tarski(A_38, k1_zfmisc_1(A_39)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_130])).
% 1.98/1.28  tff(c_12, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.98/1.28  tff(c_33, plain, (![A_4]: (A_4='#skF_2' | ~r1_tarski(A_4, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_12])).
% 1.98/1.28  tff(c_194, plain, (![A_40]: (k3_tarski(A_40)='#skF_2' | ~r1_tarski(A_40, k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_177, c_33])).
% 1.98/1.28  tff(c_208, plain, (k3_tarski('#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_34, c_194])).
% 1.98/1.28  tff(c_18, plain, (![A_8, B_9]: (r1_tarski(A_8, k3_tarski(B_9)) | ~m1_setfam_1(B_9, A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.98/1.28  tff(c_93, plain, (![B_23, A_24]: (B_23=A_24 | ~r1_tarski(B_23, A_24) | ~r1_tarski(A_24, B_23))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.98/1.28  tff(c_100, plain, (![B_9, A_8]: (k3_tarski(B_9)=A_8 | ~r1_tarski(k3_tarski(B_9), A_8) | ~m1_setfam_1(B_9, A_8))), inference(resolution, [status(thm)], [c_18, c_93])).
% 1.98/1.28  tff(c_240, plain, (![A_8]: (k3_tarski('#skF_2')=A_8 | ~r1_tarski('#skF_2', A_8) | ~m1_setfam_1('#skF_2', A_8))), inference(superposition, [status(thm), theory('equality')], [c_208, c_100])).
% 1.98/1.28  tff(c_274, plain, (![A_43]: (A_43='#skF_2' | ~m1_setfam_1('#skF_2', A_43))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_208, c_240])).
% 1.98/1.28  tff(c_295, plain, (u1_struct_0('#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_26, c_274])).
% 1.98/1.28  tff(c_22, plain, (![A_10]: (~v1_xboole_0(u1_struct_0(A_10)) | ~l1_struct_0(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.98/1.28  tff(c_302, plain, (~v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_295, c_22])).
% 1.98/1.28  tff(c_306, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_36, c_302])).
% 1.98/1.28  tff(c_308, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_306])).
% 1.98/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.28  
% 1.98/1.28  Inference rules
% 1.98/1.28  ----------------------
% 1.98/1.28  #Ref     : 0
% 1.98/1.28  #Sup     : 58
% 1.98/1.28  #Fact    : 0
% 1.98/1.28  #Define  : 0
% 1.98/1.28  #Split   : 0
% 1.98/1.28  #Chain   : 0
% 1.98/1.28  #Close   : 0
% 1.98/1.28  
% 1.98/1.28  Ordering : KBO
% 1.98/1.28  
% 1.98/1.28  Simplification rules
% 1.98/1.28  ----------------------
% 1.98/1.28  #Subsume      : 1
% 1.98/1.28  #Demod        : 31
% 1.98/1.28  #Tautology    : 27
% 1.98/1.28  #SimpNegUnit  : 1
% 1.98/1.28  #BackRed      : 2
% 1.98/1.28  
% 1.98/1.28  #Partial instantiations: 0
% 1.98/1.28  #Strategies tried      : 1
% 1.98/1.28  
% 1.98/1.28  Timing (in seconds)
% 1.98/1.28  ----------------------
% 1.98/1.29  Preprocessing        : 0.30
% 1.98/1.29  Parsing              : 0.16
% 1.98/1.29  CNF conversion       : 0.02
% 1.98/1.29  Main loop            : 0.17
% 1.98/1.29  Inferencing          : 0.06
% 1.98/1.29  Reduction            : 0.06
% 1.98/1.29  Demodulation         : 0.04
% 1.98/1.29  BG Simplification    : 0.01
% 1.98/1.29  Subsumption          : 0.03
% 1.98/1.29  Abstraction          : 0.01
% 1.98/1.29  MUC search           : 0.00
% 1.98/1.29  Cooper               : 0.00
% 1.98/1.29  Total                : 0.50
% 1.98/1.29  Index Insertion      : 0.00
% 1.98/1.29  Index Deletion       : 0.00
% 1.98/1.29  Index Matching       : 0.00
% 1.98/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
