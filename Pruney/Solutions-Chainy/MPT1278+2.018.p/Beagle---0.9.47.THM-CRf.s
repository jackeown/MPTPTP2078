%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:11 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   48 (  63 expanded)
%              Number of leaves         :   24 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   78 ( 140 expanded)
%              Number of equality atoms :   10 (  20 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tops_1 > v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v3_pre_topc(B,A)
                & v3_tops_1(B,A) )
             => B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_28,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_26,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_92,plain,(
    ! [B_39,A_40] :
      ( v2_tops_1(B_39,A_40)
      | ~ v3_tops_1(B_39,A_40)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_99,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_92])).

tff(c_107,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_26,c_99])).

tff(c_165,plain,(
    ! [A_54,B_55] :
      ( k1_tops_1(A_54,B_55) = k1_xboole_0
      | ~ v2_tops_1(B_55,A_54)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_172,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_165])).

tff(c_180,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_107,c_172])).

tff(c_213,plain,(
    ! [B_60,A_61,C_62] :
      ( r1_tarski(B_60,k1_tops_1(A_61,C_62))
      | ~ r1_tarski(B_60,C_62)
      | ~ v3_pre_topc(B_60,A_61)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_218,plain,(
    ! [B_60] :
      ( r1_tarski(B_60,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_60,'#skF_2')
      | ~ v3_pre_topc(B_60,'#skF_1')
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_213])).

tff(c_227,plain,(
    ! [B_63] :
      ( r1_tarski(B_63,k1_xboole_0)
      | ~ r1_tarski(B_63,'#skF_2')
      | ~ v3_pre_topc(B_63,'#skF_1')
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_180,c_218])).

tff(c_234,plain,
    ( r1_tarski('#skF_2',k1_xboole_0)
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_227])).

tff(c_242,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_6,c_234])).

tff(c_8,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_38,plain,(
    ! [A_25,B_26] :
      ( r1_tarski(A_25,B_26)
      | ~ m1_subset_1(A_25,k1_zfmisc_1(B_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_46,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(resolution,[status(thm)],[c_8,c_38])).

tff(c_53,plain,(
    ! [B_30,A_31] :
      ( B_30 = A_31
      | ~ r1_tarski(B_30,A_31)
      | ~ r1_tarski(A_31,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_46,c_53])).

tff(c_248,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_242,c_60])).

tff(c_254,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_248])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:21:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.34  
% 2.21/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.34  %$ v3_tops_1 > v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.21/1.34  
% 2.21/1.34  %Foreground sorts:
% 2.21/1.34  
% 2.21/1.34  
% 2.21/1.34  %Background operators:
% 2.21/1.34  
% 2.21/1.34  
% 2.21/1.34  %Foreground operators:
% 2.21/1.34  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.21/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.21/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.21/1.34  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 2.21/1.34  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.21/1.34  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 2.21/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.21/1.34  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.21/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.21/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.21/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.21/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.34  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.21/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.21/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.21/1.34  
% 2.21/1.36  tff(f_89, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tops_1(B, A)) => (B = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_tops_1)).
% 2.21/1.36  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.21/1.36  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_tops_1)).
% 2.21/1.36  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 2.21/1.36  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 2.21/1.36  tff(f_33, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.21/1.36  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.21/1.36  tff(c_24, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.21/1.36  tff(c_28, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.21/1.36  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.21/1.36  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.21/1.36  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.21/1.36  tff(c_26, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.21/1.36  tff(c_92, plain, (![B_39, A_40]: (v2_tops_1(B_39, A_40) | ~v3_tops_1(B_39, A_40) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_40))) | ~l1_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.21/1.36  tff(c_99, plain, (v2_tops_1('#skF_2', '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_92])).
% 2.21/1.36  tff(c_107, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_26, c_99])).
% 2.21/1.36  tff(c_165, plain, (![A_54, B_55]: (k1_tops_1(A_54, B_55)=k1_xboole_0 | ~v2_tops_1(B_55, A_54) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.21/1.36  tff(c_172, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_165])).
% 2.21/1.36  tff(c_180, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_107, c_172])).
% 2.21/1.36  tff(c_213, plain, (![B_60, A_61, C_62]: (r1_tarski(B_60, k1_tops_1(A_61, C_62)) | ~r1_tarski(B_60, C_62) | ~v3_pre_topc(B_60, A_61) | ~m1_subset_1(C_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.21/1.36  tff(c_218, plain, (![B_60]: (r1_tarski(B_60, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_60, '#skF_2') | ~v3_pre_topc(B_60, '#skF_1') | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_213])).
% 2.21/1.36  tff(c_227, plain, (![B_63]: (r1_tarski(B_63, k1_xboole_0) | ~r1_tarski(B_63, '#skF_2') | ~v3_pre_topc(B_63, '#skF_1') | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_180, c_218])).
% 2.21/1.36  tff(c_234, plain, (r1_tarski('#skF_2', k1_xboole_0) | ~r1_tarski('#skF_2', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_227])).
% 2.21/1.36  tff(c_242, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_6, c_234])).
% 2.21/1.36  tff(c_8, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.21/1.36  tff(c_38, plain, (![A_25, B_26]: (r1_tarski(A_25, B_26) | ~m1_subset_1(A_25, k1_zfmisc_1(B_26)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.21/1.36  tff(c_46, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(resolution, [status(thm)], [c_8, c_38])).
% 2.21/1.36  tff(c_53, plain, (![B_30, A_31]: (B_30=A_31 | ~r1_tarski(B_30, A_31) | ~r1_tarski(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.21/1.36  tff(c_60, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_46, c_53])).
% 2.21/1.36  tff(c_248, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_242, c_60])).
% 2.21/1.36  tff(c_254, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_248])).
% 2.21/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.36  
% 2.21/1.36  Inference rules
% 2.21/1.36  ----------------------
% 2.21/1.36  #Ref     : 0
% 2.21/1.36  #Sup     : 41
% 2.21/1.36  #Fact    : 0
% 2.21/1.36  #Define  : 0
% 2.21/1.36  #Split   : 1
% 2.21/1.36  #Chain   : 0
% 2.21/1.36  #Close   : 0
% 2.21/1.36  
% 2.21/1.36  Ordering : KBO
% 2.21/1.36  
% 2.21/1.36  Simplification rules
% 2.21/1.36  ----------------------
% 2.21/1.36  #Subsume      : 3
% 2.21/1.36  #Demod        : 22
% 2.21/1.36  #Tautology    : 14
% 2.21/1.36  #SimpNegUnit  : 1
% 2.21/1.36  #BackRed      : 0
% 2.21/1.36  
% 2.21/1.36  #Partial instantiations: 0
% 2.21/1.36  #Strategies tried      : 1
% 2.21/1.36  
% 2.21/1.36  Timing (in seconds)
% 2.21/1.36  ----------------------
% 2.21/1.36  Preprocessing        : 0.33
% 2.21/1.36  Parsing              : 0.18
% 2.21/1.36  CNF conversion       : 0.02
% 2.21/1.36  Main loop            : 0.20
% 2.21/1.36  Inferencing          : 0.07
% 2.21/1.36  Reduction            : 0.06
% 2.21/1.36  Demodulation         : 0.04
% 2.21/1.36  BG Simplification    : 0.01
% 2.21/1.36  Subsumption          : 0.04
% 2.21/1.36  Abstraction          : 0.01
% 2.21/1.36  MUC search           : 0.00
% 2.21/1.36  Cooper               : 0.00
% 2.21/1.36  Total                : 0.56
% 2.21/1.36  Index Insertion      : 0.00
% 2.21/1.36  Index Deletion       : 0.00
% 2.21/1.36  Index Matching       : 0.00
% 2.21/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
