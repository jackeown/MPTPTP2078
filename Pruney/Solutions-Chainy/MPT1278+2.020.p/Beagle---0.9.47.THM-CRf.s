%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:11 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   46 (  60 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   81 ( 140 expanded)
%              Number of equality atoms :   13 (  22 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tops_1 > v3_pre_topc > v2_tops_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_97,negated_conjecture,(
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

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_65,axiom,(
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

tff(f_43,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(B,C) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_26,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_24,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_59,plain,(
    ! [B_29,A_30] :
      ( v2_tops_1(B_29,A_30)
      | ~ v3_tops_1(B_29,A_30)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_62,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_59])).

tff(c_65,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_24,c_62])).

tff(c_73,plain,(
    ! [A_33,B_34] :
      ( k1_tops_1(A_33,B_34) = k1_xboole_0
      | ~ v2_tops_1(B_34,A_33)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_76,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_73])).

tff(c_79,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_65,c_76])).

tff(c_84,plain,(
    ! [B_35,A_36,C_37] :
      ( r1_tarski(B_35,k1_tops_1(A_36,C_37))
      | ~ r1_tarski(B_35,C_37)
      | ~ v3_pre_topc(B_35,A_36)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_86,plain,(
    ! [B_35] :
      ( r1_tarski(B_35,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_35,'#skF_2')
      | ~ v3_pre_topc(B_35,'#skF_1')
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_84])).

tff(c_90,plain,(
    ! [B_38] :
      ( r1_tarski(B_38,k1_xboole_0)
      | ~ r1_tarski(B_38,'#skF_2')
      | ~ v3_pre_topc(B_38,'#skF_1')
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_79,c_86])).

tff(c_93,plain,
    ( r1_tarski('#skF_2',k1_xboole_0)
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_90])).

tff(c_96,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_6,c_93])).

tff(c_8,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_48,plain,(
    ! [A_25,B_26,C_27] :
      ( k1_xboole_0 = A_25
      | ~ r1_xboole_0(B_26,C_27)
      | ~ r1_tarski(A_25,C_27)
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_51,plain,(
    ! [A_25] :
      ( k1_xboole_0 = A_25
      | ~ r1_tarski(A_25,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_48])).

tff(c_99,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_96,c_51])).

tff(c_105,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_99])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:23:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.17  
% 1.78/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.17  %$ v3_tops_1 > v3_pre_topc > v2_tops_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.78/1.17  
% 1.78/1.17  %Foreground sorts:
% 1.78/1.17  
% 1.78/1.17  
% 1.78/1.17  %Background operators:
% 1.78/1.17  
% 1.78/1.17  
% 1.78/1.17  %Foreground operators:
% 1.78/1.17  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 1.78/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.78/1.17  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 1.78/1.17  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.78/1.17  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 1.78/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.78/1.17  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 1.78/1.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.78/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.78/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.78/1.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.78/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.17  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.78/1.17  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.78/1.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.78/1.17  
% 1.78/1.18  tff(f_97, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tops_1(B, A)) => (B = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_tops_1)).
% 1.78/1.18  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.78/1.18  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_tops_1)).
% 1.78/1.18  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 1.78/1.18  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 1.78/1.18  tff(f_43, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 1.78/1.18  tff(f_51, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_xboole_1)).
% 1.78/1.18  tff(c_22, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_97])).
% 1.78/1.18  tff(c_26, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 1.78/1.18  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.78/1.18  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 1.78/1.18  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 1.78/1.18  tff(c_24, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 1.78/1.18  tff(c_59, plain, (![B_29, A_30]: (v2_tops_1(B_29, A_30) | ~v3_tops_1(B_29, A_30) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.78/1.18  tff(c_62, plain, (v2_tops_1('#skF_2', '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_59])).
% 1.78/1.18  tff(c_65, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_24, c_62])).
% 1.78/1.18  tff(c_73, plain, (![A_33, B_34]: (k1_tops_1(A_33, B_34)=k1_xboole_0 | ~v2_tops_1(B_34, A_33) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.78/1.18  tff(c_76, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_73])).
% 1.78/1.18  tff(c_79, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_65, c_76])).
% 1.78/1.18  tff(c_84, plain, (![B_35, A_36, C_37]: (r1_tarski(B_35, k1_tops_1(A_36, C_37)) | ~r1_tarski(B_35, C_37) | ~v3_pre_topc(B_35, A_36) | ~m1_subset_1(C_37, k1_zfmisc_1(u1_struct_0(A_36))) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.78/1.18  tff(c_86, plain, (![B_35]: (r1_tarski(B_35, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_35, '#skF_2') | ~v3_pre_topc(B_35, '#skF_1') | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_84])).
% 1.78/1.18  tff(c_90, plain, (![B_38]: (r1_tarski(B_38, k1_xboole_0) | ~r1_tarski(B_38, '#skF_2') | ~v3_pre_topc(B_38, '#skF_1') | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_79, c_86])).
% 1.78/1.18  tff(c_93, plain, (r1_tarski('#skF_2', k1_xboole_0) | ~r1_tarski('#skF_2', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_28, c_90])).
% 1.78/1.18  tff(c_96, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_6, c_93])).
% 1.78/1.18  tff(c_8, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.78/1.18  tff(c_48, plain, (![A_25, B_26, C_27]: (k1_xboole_0=A_25 | ~r1_xboole_0(B_26, C_27) | ~r1_tarski(A_25, C_27) | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.78/1.18  tff(c_51, plain, (![A_25]: (k1_xboole_0=A_25 | ~r1_tarski(A_25, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_48])).
% 1.78/1.18  tff(c_99, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_96, c_51])).
% 1.78/1.18  tff(c_105, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_99])).
% 1.78/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.18  
% 1.78/1.18  Inference rules
% 1.78/1.18  ----------------------
% 1.78/1.18  #Ref     : 0
% 1.78/1.18  #Sup     : 13
% 1.78/1.18  #Fact    : 0
% 1.78/1.18  #Define  : 0
% 1.78/1.18  #Split   : 0
% 1.78/1.18  #Chain   : 0
% 1.78/1.18  #Close   : 0
% 1.78/1.18  
% 1.78/1.18  Ordering : KBO
% 1.78/1.18  
% 1.78/1.18  Simplification rules
% 1.78/1.18  ----------------------
% 1.78/1.18  #Subsume      : 0
% 1.78/1.18  #Demod        : 12
% 1.78/1.18  #Tautology    : 7
% 1.78/1.18  #SimpNegUnit  : 1
% 1.78/1.18  #BackRed      : 0
% 1.78/1.18  
% 1.78/1.18  #Partial instantiations: 0
% 1.78/1.18  #Strategies tried      : 1
% 1.78/1.18  
% 1.78/1.18  Timing (in seconds)
% 1.78/1.18  ----------------------
% 1.78/1.18  Preprocessing        : 0.30
% 1.78/1.18  Parsing              : 0.16
% 1.78/1.18  CNF conversion       : 0.02
% 1.78/1.18  Main loop            : 0.12
% 1.78/1.18  Inferencing          : 0.04
% 1.78/1.18  Reduction            : 0.04
% 1.78/1.19  Demodulation         : 0.03
% 1.78/1.19  BG Simplification    : 0.01
% 1.78/1.19  Subsumption          : 0.02
% 1.78/1.19  Abstraction          : 0.00
% 1.78/1.19  MUC search           : 0.00
% 1.78/1.19  Cooper               : 0.00
% 1.78/1.19  Total                : 0.45
% 1.78/1.19  Index Insertion      : 0.00
% 1.78/1.19  Index Deletion       : 0.00
% 1.78/1.19  Index Matching       : 0.00
% 1.78/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
