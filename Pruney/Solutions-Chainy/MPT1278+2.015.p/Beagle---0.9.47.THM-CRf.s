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
% DateTime   : Thu Dec  3 10:22:10 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   46 (  60 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :   73 ( 132 expanded)
%              Number of equality atoms :   13 (  22 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tops_1 > v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v3_pre_topc(B,A)
                & v3_tops_1(B,A) )
             => B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_tops_1)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_51,axiom,(
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

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_10,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_22,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_73,plain,(
    ! [B_27,A_28] :
      ( v2_tops_1(B_27,A_28)
      | ~ v3_tops_1(B_27,A_28)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_76,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_73])).

tff(c_79,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_22,c_76])).

tff(c_80,plain,(
    ! [A_29,B_30] :
      ( k1_tops_1(A_29,B_30) = k1_xboole_0
      | ~ v2_tops_1(B_30,A_29)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_83,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_80])).

tff(c_86,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_79,c_83])).

tff(c_98,plain,(
    ! [B_33,A_34,C_35] :
      ( r1_tarski(B_33,k1_tops_1(A_34,C_35))
      | ~ r1_tarski(B_33,C_35)
      | ~ v3_pre_topc(B_33,A_34)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_100,plain,(
    ! [B_33] :
      ( r1_tarski(B_33,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_33,'#skF_2')
      | ~ v3_pre_topc(B_33,'#skF_1')
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_98])).

tff(c_104,plain,(
    ! [B_36] :
      ( r1_tarski(B_36,k1_xboole_0)
      | ~ r1_tarski(B_36,'#skF_2')
      | ~ v3_pre_topc(B_36,'#skF_1')
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_86,c_100])).

tff(c_107,plain,
    ( r1_tarski('#skF_2',k1_xboole_0)
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_104])).

tff(c_110,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_6,c_107])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_115,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_110,c_8])).

tff(c_120,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_115])).

tff(c_122,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_120])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:16:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.22  
% 1.86/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.22  %$ v3_tops_1 > v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.86/1.22  
% 1.86/1.22  %Foreground sorts:
% 1.86/1.22  
% 1.86/1.22  
% 1.86/1.22  %Background operators:
% 1.86/1.22  
% 1.86/1.22  
% 1.86/1.22  %Foreground operators:
% 1.86/1.22  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 1.86/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.86/1.22  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 1.86/1.22  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.86/1.22  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 1.86/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.86/1.22  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 1.86/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.86/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.86/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.86/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.22  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.86/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.86/1.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.86/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.86/1.22  
% 1.98/1.24  tff(f_83, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tops_1(B, A)) => (B = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_tops_1)).
% 1.98/1.24  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 1.98/1.24  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.98/1.24  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_tops_1)).
% 1.98/1.24  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 1.98/1.24  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 1.98/1.24  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.98/1.24  tff(c_20, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.98/1.24  tff(c_10, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.98/1.24  tff(c_24, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.98/1.24  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.98/1.24  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.98/1.24  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.98/1.24  tff(c_22, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.98/1.24  tff(c_73, plain, (![B_27, A_28]: (v2_tops_1(B_27, A_28) | ~v3_tops_1(B_27, A_28) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.98/1.24  tff(c_76, plain, (v2_tops_1('#skF_2', '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_73])).
% 1.98/1.24  tff(c_79, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_22, c_76])).
% 1.98/1.24  tff(c_80, plain, (![A_29, B_30]: (k1_tops_1(A_29, B_30)=k1_xboole_0 | ~v2_tops_1(B_30, A_29) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.98/1.24  tff(c_83, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_80])).
% 1.98/1.24  tff(c_86, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_79, c_83])).
% 1.98/1.24  tff(c_98, plain, (![B_33, A_34, C_35]: (r1_tarski(B_33, k1_tops_1(A_34, C_35)) | ~r1_tarski(B_33, C_35) | ~v3_pre_topc(B_33, A_34) | ~m1_subset_1(C_35, k1_zfmisc_1(u1_struct_0(A_34))) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.98/1.24  tff(c_100, plain, (![B_33]: (r1_tarski(B_33, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_33, '#skF_2') | ~v3_pre_topc(B_33, '#skF_1') | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_98])).
% 1.98/1.24  tff(c_104, plain, (![B_36]: (r1_tarski(B_36, k1_xboole_0) | ~r1_tarski(B_36, '#skF_2') | ~v3_pre_topc(B_36, '#skF_1') | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_86, c_100])).
% 1.98/1.24  tff(c_107, plain, (r1_tarski('#skF_2', k1_xboole_0) | ~r1_tarski('#skF_2', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_26, c_104])).
% 1.98/1.24  tff(c_110, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_6, c_107])).
% 1.98/1.24  tff(c_8, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.98/1.24  tff(c_115, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_110, c_8])).
% 1.98/1.24  tff(c_120, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_115])).
% 1.98/1.24  tff(c_122, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_120])).
% 1.98/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.24  
% 1.98/1.24  Inference rules
% 1.98/1.24  ----------------------
% 1.98/1.24  #Ref     : 0
% 1.98/1.24  #Sup     : 17
% 1.98/1.24  #Fact    : 0
% 1.98/1.24  #Define  : 0
% 1.98/1.24  #Split   : 0
% 1.98/1.24  #Chain   : 0
% 1.98/1.24  #Close   : 0
% 1.98/1.24  
% 1.98/1.24  Ordering : KBO
% 1.98/1.24  
% 1.98/1.24  Simplification rules
% 1.98/1.24  ----------------------
% 1.98/1.24  #Subsume      : 0
% 1.98/1.24  #Demod        : 14
% 1.98/1.24  #Tautology    : 11
% 1.98/1.24  #SimpNegUnit  : 2
% 1.98/1.24  #BackRed      : 0
% 1.98/1.24  
% 1.98/1.24  #Partial instantiations: 0
% 1.98/1.24  #Strategies tried      : 1
% 1.98/1.24  
% 1.98/1.24  Timing (in seconds)
% 1.98/1.24  ----------------------
% 1.98/1.24  Preprocessing        : 0.31
% 1.98/1.24  Parsing              : 0.17
% 1.98/1.24  CNF conversion       : 0.02
% 1.98/1.24  Main loop            : 0.12
% 1.98/1.24  Inferencing          : 0.04
% 1.98/1.24  Reduction            : 0.04
% 1.98/1.24  Demodulation         : 0.03
% 1.98/1.24  BG Simplification    : 0.01
% 1.98/1.24  Subsumption          : 0.02
% 1.98/1.24  Abstraction          : 0.01
% 1.98/1.24  MUC search           : 0.00
% 1.98/1.24  Cooper               : 0.00
% 1.98/1.24  Total                : 0.46
% 1.98/1.24  Index Insertion      : 0.00
% 1.98/1.24  Index Deletion       : 0.00
% 1.98/1.24  Index Matching       : 0.00
% 1.98/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
