%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:10 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   44 (  59 expanded)
%              Number of leaves         :   22 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   73 ( 135 expanded)
%              Number of equality atoms :   10 (  20 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tops_1 > v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v3_pre_topc(B,A)
                & v3_tops_1(B,A) )
             => B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_22,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_20,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_42,plain,(
    ! [B_22,A_23] :
      ( v2_tops_1(B_22,A_23)
      | ~ v3_tops_1(B_22,A_23)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_45,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_42])).

tff(c_48,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_20,c_45])).

tff(c_69,plain,(
    ! [A_27,B_28] :
      ( k1_tops_1(A_27,B_28) = k1_xboole_0
      | ~ v2_tops_1(B_28,A_27)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_72,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_69])).

tff(c_75,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_48,c_72])).

tff(c_80,plain,(
    ! [B_29,A_30,C_31] :
      ( r1_tarski(B_29,k1_tops_1(A_30,C_31))
      | ~ r1_tarski(B_29,C_31)
      | ~ v3_pre_topc(B_29,A_30)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_82,plain,(
    ! [B_29] :
      ( r1_tarski(B_29,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_29,'#skF_2')
      | ~ v3_pre_topc(B_29,'#skF_1')
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_80])).

tff(c_86,plain,(
    ! [B_32] :
      ( r1_tarski(B_32,k1_xboole_0)
      | ~ r1_tarski(B_32,'#skF_2')
      | ~ v3_pre_topc(B_32,'#skF_1')
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_75,c_82])).

tff(c_89,plain,
    ( r1_tarski('#skF_2',k1_xboole_0)
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_86])).

tff(c_92,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_6,c_89])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_32,plain,(
    ! [B_20,A_21] :
      ( B_20 = A_21
      | ~ r1_tarski(B_20,A_21)
      | ~ r1_tarski(A_21,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_41,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_32])).

tff(c_95,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_92,c_41])).

tff(c_101,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_95])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.08  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.07/0.27  % Computer   : n002.cluster.edu
% 0.07/0.27  % Model      : x86_64 x86_64
% 0.07/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.27  % Memory     : 8042.1875MB
% 0.07/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.27  % CPULimit   : 60
% 0.07/0.27  % DateTime   : Tue Dec  1 09:39:21 EST 2020
% 0.07/0.27  % CPUTime    : 
% 0.07/0.28  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.04  
% 1.65/1.04  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.04  %$ v3_tops_1 > v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.65/1.04  
% 1.65/1.04  %Foreground sorts:
% 1.65/1.04  
% 1.65/1.04  
% 1.65/1.04  %Background operators:
% 1.65/1.04  
% 1.65/1.04  
% 1.65/1.04  %Foreground operators:
% 1.65/1.04  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 1.65/1.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.65/1.04  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 1.65/1.04  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.65/1.04  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 1.65/1.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.65/1.04  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 1.65/1.04  tff('#skF_2', type, '#skF_2': $i).
% 1.65/1.04  tff('#skF_1', type, '#skF_1': $i).
% 1.65/1.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.65/1.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.04  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.65/1.04  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.65/1.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.65/1.04  
% 1.65/1.05  tff(f_79, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tops_1(B, A)) => (B = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_tops_1)).
% 1.65/1.05  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.65/1.05  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_tops_1)).
% 1.65/1.05  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 1.65/1.05  tff(f_47, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 1.65/1.05  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.65/1.05  tff(c_18, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.65/1.05  tff(c_22, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.65/1.05  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.65/1.05  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.65/1.05  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.65/1.05  tff(c_20, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.65/1.05  tff(c_42, plain, (![B_22, A_23]: (v2_tops_1(B_22, A_23) | ~v3_tops_1(B_22, A_23) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.65/1.05  tff(c_45, plain, (v2_tops_1('#skF_2', '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_42])).
% 1.65/1.05  tff(c_48, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_20, c_45])).
% 1.65/1.05  tff(c_69, plain, (![A_27, B_28]: (k1_tops_1(A_27, B_28)=k1_xboole_0 | ~v2_tops_1(B_28, A_27) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.65/1.05  tff(c_72, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_69])).
% 1.65/1.05  tff(c_75, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_48, c_72])).
% 1.65/1.05  tff(c_80, plain, (![B_29, A_30, C_31]: (r1_tarski(B_29, k1_tops_1(A_30, C_31)) | ~r1_tarski(B_29, C_31) | ~v3_pre_topc(B_29, A_30) | ~m1_subset_1(C_31, k1_zfmisc_1(u1_struct_0(A_30))) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.65/1.05  tff(c_82, plain, (![B_29]: (r1_tarski(B_29, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_29, '#skF_2') | ~v3_pre_topc(B_29, '#skF_1') | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_80])).
% 1.65/1.05  tff(c_86, plain, (![B_32]: (r1_tarski(B_32, k1_xboole_0) | ~r1_tarski(B_32, '#skF_2') | ~v3_pre_topc(B_32, '#skF_1') | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_75, c_82])).
% 1.65/1.05  tff(c_89, plain, (r1_tarski('#skF_2', k1_xboole_0) | ~r1_tarski('#skF_2', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_24, c_86])).
% 1.65/1.05  tff(c_92, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_6, c_89])).
% 1.65/1.05  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.65/1.05  tff(c_32, plain, (![B_20, A_21]: (B_20=A_21 | ~r1_tarski(B_20, A_21) | ~r1_tarski(A_21, B_20))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.65/1.05  tff(c_41, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_32])).
% 1.65/1.05  tff(c_95, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_92, c_41])).
% 1.65/1.05  tff(c_101, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_95])).
% 1.65/1.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.05  
% 1.65/1.05  Inference rules
% 1.65/1.05  ----------------------
% 1.65/1.05  #Ref     : 0
% 1.65/1.05  #Sup     : 13
% 1.65/1.05  #Fact    : 0
% 1.65/1.05  #Define  : 0
% 1.65/1.05  #Split   : 0
% 1.65/1.05  #Chain   : 0
% 1.65/1.05  #Close   : 0
% 1.65/1.05  
% 1.65/1.05  Ordering : KBO
% 1.65/1.05  
% 1.65/1.05  Simplification rules
% 1.65/1.05  ----------------------
% 1.65/1.05  #Subsume      : 0
% 1.65/1.05  #Demod        : 12
% 1.65/1.05  #Tautology    : 7
% 1.65/1.05  #SimpNegUnit  : 1
% 1.65/1.05  #BackRed      : 0
% 1.65/1.05  
% 1.65/1.05  #Partial instantiations: 0
% 1.65/1.05  #Strategies tried      : 1
% 1.65/1.05  
% 1.65/1.05  Timing (in seconds)
% 1.65/1.05  ----------------------
% 1.65/1.05  Preprocessing        : 0.30
% 1.65/1.05  Parsing              : 0.16
% 1.65/1.05  CNF conversion       : 0.02
% 1.65/1.05  Main loop            : 0.12
% 1.65/1.05  Inferencing          : 0.05
% 1.65/1.05  Reduction            : 0.04
% 1.65/1.05  Demodulation         : 0.03
% 1.65/1.05  BG Simplification    : 0.01
% 1.65/1.05  Subsumption          : 0.02
% 1.65/1.05  Abstraction          : 0.00
% 1.65/1.05  MUC search           : 0.00
% 1.65/1.06  Cooper               : 0.00
% 1.65/1.06  Total                : 0.44
% 1.65/1.06  Index Insertion      : 0.00
% 1.65/1.06  Index Deletion       : 0.00
% 1.65/1.06  Index Matching       : 0.00
% 1.65/1.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
