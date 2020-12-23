%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:07 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   50 (  81 expanded)
%              Number of leaves         :   20 (  38 expanded)
%              Depth                    :    7
%              Number of atoms          :   88 ( 191 expanded)
%              Number of equality atoms :    8 (  28 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k2_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => ( v3_tops_1(B,A)
              <=> B = k2_tops_1(A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v2_tops_1(B,A)
              & v4_pre_topc(B,A) )
           => v3_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_tops_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(c_24,plain,
    ( k2_tops_1('#skF_1','#skF_2') != '#skF_2'
    | ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_33,plain,(
    ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_22,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_34,plain,(
    k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_30])).

tff(c_59,plain,(
    ! [B_23,A_24] :
      ( v2_tops_1(B_23,A_24)
      | ~ r1_tarski(B_23,k2_tops_1(A_24,B_23))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_61,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_59])).

tff(c_63,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_6,c_61])).

tff(c_18,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_70,plain,(
    ! [B_27,A_28] :
      ( v3_tops_1(B_27,A_28)
      | ~ v4_pre_topc(B_27,A_28)
      | ~ v2_tops_1(B_27,A_28)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_73,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_70])).

tff(c_76,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_63,c_18,c_73])).

tff(c_78,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_76])).

tff(c_79,plain,(
    k2_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_80,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_90,plain,(
    ! [B_31,A_32] :
      ( v2_tops_1(B_31,A_32)
      | ~ v3_tops_1(B_31,A_32)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_93,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_90])).

tff(c_96,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_80,c_93])).

tff(c_98,plain,(
    ! [B_35,A_36] :
      ( r1_tarski(B_35,k2_tops_1(A_36,B_35))
      | ~ v2_tops_1(B_35,A_36)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_100,plain,
    ( r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_98])).

tff(c_103,plain,(
    r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_96,c_100])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_107,plain,
    ( k2_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_103,c_2])).

tff(c_113,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_107])).

tff(c_114,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(k2_tops_1(A_37,B_38),B_38)
      | ~ v4_pre_topc(B_38,A_37)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_116,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_114])).

tff(c_119,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_116])).

tff(c_121,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_119])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:47:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.77/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.15  
% 1.77/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.15  %$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k2_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.77/1.15  
% 1.77/1.15  %Foreground sorts:
% 1.77/1.15  
% 1.77/1.15  
% 1.77/1.15  %Background operators:
% 1.77/1.15  
% 1.77/1.15  
% 1.77/1.15  %Foreground operators:
% 1.77/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.77/1.15  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 1.77/1.15  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 1.77/1.15  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.77/1.15  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 1.77/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.77/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.77/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.77/1.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.77/1.15  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 1.77/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.77/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.77/1.15  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.77/1.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.77/1.15  
% 1.87/1.17  tff(f_81, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => (v3_tops_1(B, A) <=> (B = k2_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_tops_1)).
% 1.87/1.17  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.87/1.17  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tops_1)).
% 1.87/1.17  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tops_1(B, A) & v4_pre_topc(B, A)) => v3_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_tops_1)).
% 1.87/1.17  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_tops_1)).
% 1.87/1.17  tff(f_40, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 1.87/1.17  tff(c_24, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2' | ~v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.87/1.17  tff(c_33, plain, (~v3_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_24])).
% 1.87/1.17  tff(c_22, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.87/1.17  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.87/1.17  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.87/1.17  tff(c_30, plain, (v3_tops_1('#skF_2', '#skF_1') | k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.87/1.17  tff(c_34, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_33, c_30])).
% 1.87/1.17  tff(c_59, plain, (![B_23, A_24]: (v2_tops_1(B_23, A_24) | ~r1_tarski(B_23, k2_tops_1(A_24, B_23)) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.87/1.17  tff(c_61, plain, (v2_tops_1('#skF_2', '#skF_1') | ~r1_tarski('#skF_2', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_34, c_59])).
% 1.87/1.17  tff(c_63, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_6, c_61])).
% 1.87/1.17  tff(c_18, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.87/1.17  tff(c_70, plain, (![B_27, A_28]: (v3_tops_1(B_27, A_28) | ~v4_pre_topc(B_27, A_28) | ~v2_tops_1(B_27, A_28) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.87/1.17  tff(c_73, plain, (v3_tops_1('#skF_2', '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_70])).
% 1.87/1.17  tff(c_76, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_63, c_18, c_73])).
% 1.87/1.17  tff(c_78, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33, c_76])).
% 1.87/1.17  tff(c_79, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(splitRight, [status(thm)], [c_24])).
% 1.87/1.17  tff(c_80, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_24])).
% 1.87/1.17  tff(c_90, plain, (![B_31, A_32]: (v2_tops_1(B_31, A_32) | ~v3_tops_1(B_31, A_32) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.87/1.17  tff(c_93, plain, (v2_tops_1('#skF_2', '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_90])).
% 1.87/1.17  tff(c_96, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_80, c_93])).
% 1.87/1.17  tff(c_98, plain, (![B_35, A_36]: (r1_tarski(B_35, k2_tops_1(A_36, B_35)) | ~v2_tops_1(B_35, A_36) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.87/1.17  tff(c_100, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_98])).
% 1.87/1.17  tff(c_103, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_96, c_100])).
% 1.87/1.17  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.87/1.17  tff(c_107, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2' | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_103, c_2])).
% 1.87/1.17  tff(c_113, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_79, c_107])).
% 1.87/1.17  tff(c_114, plain, (![A_37, B_38]: (r1_tarski(k2_tops_1(A_37, B_38), B_38) | ~v4_pre_topc(B_38, A_37) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(A_37))) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.87/1.17  tff(c_116, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_114])).
% 1.87/1.17  tff(c_119, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_116])).
% 1.87/1.17  tff(c_121, plain, $false, inference(negUnitSimplification, [status(thm)], [c_113, c_119])).
% 1.87/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.17  
% 1.87/1.17  Inference rules
% 1.87/1.17  ----------------------
% 1.87/1.17  #Ref     : 0
% 1.87/1.17  #Sup     : 14
% 1.87/1.17  #Fact    : 0
% 1.87/1.17  #Define  : 0
% 1.87/1.17  #Split   : 1
% 1.87/1.17  #Chain   : 0
% 1.87/1.17  #Close   : 0
% 1.87/1.17  
% 1.87/1.17  Ordering : KBO
% 1.87/1.17  
% 1.87/1.17  Simplification rules
% 1.87/1.17  ----------------------
% 1.87/1.17  #Subsume      : 1
% 1.87/1.17  #Demod        : 28
% 1.87/1.17  #Tautology    : 11
% 1.87/1.17  #SimpNegUnit  : 5
% 1.87/1.17  #BackRed      : 0
% 1.87/1.17  
% 1.87/1.17  #Partial instantiations: 0
% 1.87/1.17  #Strategies tried      : 1
% 1.87/1.17  
% 1.87/1.17  Timing (in seconds)
% 1.87/1.17  ----------------------
% 1.87/1.17  Preprocessing        : 0.27
% 1.87/1.17  Parsing              : 0.15
% 1.87/1.17  CNF conversion       : 0.02
% 1.87/1.17  Main loop            : 0.13
% 1.87/1.17  Inferencing          : 0.05
% 1.87/1.17  Reduction            : 0.04
% 1.87/1.17  Demodulation         : 0.03
% 1.87/1.17  BG Simplification    : 0.01
% 1.87/1.17  Subsumption          : 0.02
% 1.87/1.17  Abstraction          : 0.01
% 1.87/1.17  MUC search           : 0.00
% 1.87/1.17  Cooper               : 0.00
% 1.87/1.17  Total                : 0.43
% 1.87/1.17  Index Insertion      : 0.00
% 1.87/1.17  Index Deletion       : 0.00
% 1.87/1.17  Index Matching       : 0.00
% 1.87/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
