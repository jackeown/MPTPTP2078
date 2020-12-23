%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:11 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   47 (  84 expanded)
%              Number of leaves         :   22 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :   81 ( 216 expanded)
%              Number of equality atoms :    9 (  30 expanded)
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

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v3_pre_topc(B,A)
                & v3_tops_1(B,A) )
             => B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_tops_1)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
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

tff(c_18,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_20,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_48,plain,(
    ! [B_25,A_26] :
      ( v2_tops_1(B_25,A_26)
      | ~ v3_tops_1(B_25,A_26)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_51,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_48])).

tff(c_54,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_20,c_51])).

tff(c_55,plain,(
    ! [A_27,B_28] :
      ( k1_tops_1(A_27,B_28) = k1_xboole_0
      | ~ v2_tops_1(B_28,A_27)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_58,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_55])).

tff(c_61,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_54,c_58])).

tff(c_38,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(k1_tops_1(A_23,B_24),B_24)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_40,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_38])).

tff(c_43,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_40])).

tff(c_70,plain,(
    r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_43])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_76,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_70,c_2])).

tff(c_79,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_76])).

tff(c_22,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_80,plain,(
    ! [B_31,A_32,C_33] :
      ( r1_tarski(B_31,k1_tops_1(A_32,C_33))
      | ~ r1_tarski(B_31,C_33)
      | ~ v3_pre_topc(B_31,A_32)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_82,plain,(
    ! [B_31] :
      ( r1_tarski(B_31,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_31,'#skF_2')
      | ~ v3_pre_topc(B_31,'#skF_1')
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_80])).

tff(c_86,plain,(
    ! [B_34] :
      ( r1_tarski(B_34,k1_xboole_0)
      | ~ r1_tarski(B_34,'#skF_2')
      | ~ v3_pre_topc(B_34,'#skF_1')
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_61,c_82])).

tff(c_89,plain,
    ( r1_tarski('#skF_2',k1_xboole_0)
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_86])).

tff(c_92,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_6,c_89])).

tff(c_94,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_92])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:44:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.16  
% 1.87/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.17  %$ v3_tops_1 > v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.87/1.17  
% 1.87/1.17  %Foreground sorts:
% 1.87/1.17  
% 1.87/1.17  
% 1.87/1.17  %Background operators:
% 1.87/1.17  
% 1.87/1.17  
% 1.87/1.17  %Foreground operators:
% 1.87/1.17  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 1.87/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.87/1.17  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 1.87/1.17  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.87/1.17  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 1.87/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.17  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 1.87/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.87/1.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.87/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.17  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.87/1.17  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.87/1.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.87/1.17  
% 1.87/1.18  tff(f_84, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tops_1(B, A)) => (B = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_tops_1)).
% 1.87/1.18  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_tops_1)).
% 1.87/1.18  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 1.87/1.18  tff(f_38, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 1.87/1.18  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.87/1.18  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 1.87/1.18  tff(c_18, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.87/1.18  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.87/1.18  tff(c_20, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.87/1.18  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.87/1.18  tff(c_48, plain, (![B_25, A_26]: (v2_tops_1(B_25, A_26) | ~v3_tops_1(B_25, A_26) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.87/1.18  tff(c_51, plain, (v2_tops_1('#skF_2', '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_48])).
% 1.87/1.18  tff(c_54, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_20, c_51])).
% 1.87/1.18  tff(c_55, plain, (![A_27, B_28]: (k1_tops_1(A_27, B_28)=k1_xboole_0 | ~v2_tops_1(B_28, A_27) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.87/1.18  tff(c_58, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_55])).
% 1.87/1.18  tff(c_61, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_54, c_58])).
% 1.87/1.18  tff(c_38, plain, (![A_23, B_24]: (r1_tarski(k1_tops_1(A_23, B_24), B_24) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.87/1.18  tff(c_40, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_38])).
% 1.87/1.18  tff(c_43, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_40])).
% 1.87/1.18  tff(c_70, plain, (r1_tarski(k1_xboole_0, '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_43])).
% 1.87/1.18  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.87/1.18  tff(c_76, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', k1_xboole_0)), inference(resolution, [status(thm)], [c_70, c_2])).
% 1.87/1.18  tff(c_79, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_18, c_76])).
% 1.87/1.18  tff(c_22, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.87/1.18  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.87/1.18  tff(c_80, plain, (![B_31, A_32, C_33]: (r1_tarski(B_31, k1_tops_1(A_32, C_33)) | ~r1_tarski(B_31, C_33) | ~v3_pre_topc(B_31, A_32) | ~m1_subset_1(C_33, k1_zfmisc_1(u1_struct_0(A_32))) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.87/1.18  tff(c_82, plain, (![B_31]: (r1_tarski(B_31, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_31, '#skF_2') | ~v3_pre_topc(B_31, '#skF_1') | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_80])).
% 1.87/1.18  tff(c_86, plain, (![B_34]: (r1_tarski(B_34, k1_xboole_0) | ~r1_tarski(B_34, '#skF_2') | ~v3_pre_topc(B_34, '#skF_1') | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_61, c_82])).
% 1.87/1.18  tff(c_89, plain, (r1_tarski('#skF_2', k1_xboole_0) | ~r1_tarski('#skF_2', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_24, c_86])).
% 1.87/1.18  tff(c_92, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_6, c_89])).
% 1.87/1.18  tff(c_94, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79, c_92])).
% 1.87/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.18  
% 1.87/1.18  Inference rules
% 1.87/1.18  ----------------------
% 1.87/1.18  #Ref     : 0
% 1.87/1.18  #Sup     : 11
% 1.87/1.18  #Fact    : 0
% 1.87/1.18  #Define  : 0
% 1.87/1.18  #Split   : 1
% 1.87/1.18  #Chain   : 0
% 1.87/1.18  #Close   : 0
% 1.87/1.18  
% 1.87/1.18  Ordering : KBO
% 1.87/1.18  
% 1.87/1.18  Simplification rules
% 1.87/1.18  ----------------------
% 1.87/1.18  #Subsume      : 1
% 1.87/1.18  #Demod        : 15
% 1.87/1.18  #Tautology    : 5
% 1.87/1.18  #SimpNegUnit  : 2
% 1.87/1.18  #BackRed      : 2
% 1.87/1.18  
% 1.87/1.18  #Partial instantiations: 0
% 1.87/1.18  #Strategies tried      : 1
% 1.87/1.18  
% 1.87/1.18  Timing (in seconds)
% 1.87/1.18  ----------------------
% 1.87/1.18  Preprocessing        : 0.30
% 1.87/1.18  Parsing              : 0.16
% 1.87/1.18  CNF conversion       : 0.02
% 1.87/1.18  Main loop            : 0.13
% 1.87/1.18  Inferencing          : 0.04
% 1.87/1.18  Reduction            : 0.04
% 1.87/1.18  Demodulation         : 0.03
% 1.87/1.18  BG Simplification    : 0.01
% 1.87/1.18  Subsumption          : 0.03
% 1.87/1.19  Abstraction          : 0.00
% 1.87/1.19  MUC search           : 0.00
% 1.87/1.19  Cooper               : 0.00
% 1.87/1.19  Total                : 0.45
% 1.87/1.19  Index Insertion      : 0.00
% 1.87/1.19  Index Deletion       : 0.00
% 1.87/1.19  Index Matching       : 0.00
% 1.87/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
