%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:56 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   41 (  51 expanded)
%              Number of leaves         :   20 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :   68 (  99 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v2_tops_2,type,(
    v2_tops_2: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( v2_tops_2(B,A)
                 => v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tops_2)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( ( r1_tarski(B,C)
                  & v2_tops_2(C,A) )
               => v2_tops_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tops_2)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_tarski(k4_xboole_0(A_4,B_5),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    v2_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_22,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(A_24,B_25)
      | ~ m1_subset_1(A_24,k1_zfmisc_1(B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_32,plain,(
    r1_tarski('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_20,c_24])).

tff(c_38,plain,(
    ! [A_28,C_29,B_30] :
      ( r1_tarski(A_28,C_29)
      | ~ r1_tarski(B_30,C_29)
      | ~ r1_tarski(A_28,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_45,plain,(
    ! [A_28] :
      ( r1_tarski(A_28,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_28,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_38])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_193,plain,(
    ! [B_62,A_63,C_64] :
      ( v2_tops_2(B_62,A_63)
      | ~ v2_tops_2(C_64,A_63)
      | ~ r1_tarski(B_62,C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_63))))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_63))))
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_413,plain,(
    ! [A_87,B_88,A_89] :
      ( v2_tops_2(k4_xboole_0(A_87,B_88),A_89)
      | ~ v2_tops_2(A_87,A_89)
      | ~ m1_subset_1(A_87,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_89))))
      | ~ m1_subset_1(k4_xboole_0(A_87,B_88),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_89))))
      | ~ l1_pre_topc(A_89) ) ),
    inference(resolution,[status(thm)],[c_4,c_193])).

tff(c_546,plain,(
    ! [A_114,B_115,A_116] :
      ( v2_tops_2(k4_xboole_0(A_114,B_115),A_116)
      | ~ v2_tops_2(A_114,A_116)
      | ~ m1_subset_1(A_114,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_116))))
      | ~ l1_pre_topc(A_116)
      | ~ r1_tarski(k4_xboole_0(A_114,B_115),k1_zfmisc_1(u1_struct_0(A_116))) ) ),
    inference(resolution,[status(thm)],[c_10,c_413])).

tff(c_584,plain,(
    ! [A_114,B_115] :
      ( v2_tops_2(k4_xboole_0(A_114,B_115),'#skF_1')
      | ~ v2_tops_2(A_114,'#skF_1')
      | ~ m1_subset_1(A_114,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(k4_xboole_0(A_114,B_115),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_45,c_546])).

tff(c_829,plain,(
    ! [A_146,B_147] :
      ( v2_tops_2(k4_xboole_0(A_146,B_147),'#skF_1')
      | ~ v2_tops_2(A_146,'#skF_1')
      | ~ m1_subset_1(A_146,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ r1_tarski(k4_xboole_0(A_146,B_147),'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_584])).

tff(c_836,plain,(
    ! [B_147] :
      ( v2_tops_2(k4_xboole_0('#skF_2',B_147),'#skF_1')
      | ~ v2_tops_2('#skF_2','#skF_1')
      | ~ r1_tarski(k4_xboole_0('#skF_2',B_147),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_20,c_829])).

tff(c_841,plain,(
    ! [B_147] : v2_tops_2(k4_xboole_0('#skF_2',B_147),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_16,c_836])).

tff(c_71,plain,(
    ! [A_39,B_40,C_41] :
      ( k7_subset_1(A_39,B_40,C_41) = k4_xboole_0(B_40,C_41)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_80,plain,(
    ! [C_41] : k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_41) = k4_xboole_0('#skF_2',C_41) ),
    inference(resolution,[status(thm)],[c_20,c_71])).

tff(c_14,plain,(
    ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_90,plain,(
    ~ v2_tops_2(k4_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_14])).

tff(c_845,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_841,c_90])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:08:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.42  
% 2.80/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.42  %$ v2_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.80/1.42  
% 2.80/1.42  %Foreground sorts:
% 2.80/1.42  
% 2.80/1.42  
% 2.80/1.42  %Background operators:
% 2.80/1.42  
% 2.80/1.42  
% 2.80/1.42  %Foreground operators:
% 2.80/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.80/1.42  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.80/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.80/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.80/1.42  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.80/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.80/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.80/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.80/1.42  tff(v2_tops_2, type, v2_tops_2: ($i * $i) > $o).
% 2.80/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.80/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.80/1.42  
% 2.80/1.43  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.80/1.43  tff(f_68, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) => v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_tops_2)).
% 2.80/1.43  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.80/1.43  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.80/1.43  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v2_tops_2(C, A)) => v2_tops_2(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_tops_2)).
% 2.80/1.43  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.80/1.43  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(k4_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.80/1.43  tff(c_16, plain, (v2_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.80/1.43  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.80/1.43  tff(c_22, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.80/1.43  tff(c_24, plain, (![A_24, B_25]: (r1_tarski(A_24, B_25) | ~m1_subset_1(A_24, k1_zfmisc_1(B_25)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.80/1.43  tff(c_32, plain, (r1_tarski('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_20, c_24])).
% 2.80/1.43  tff(c_38, plain, (![A_28, C_29, B_30]: (r1_tarski(A_28, C_29) | ~r1_tarski(B_30, C_29) | ~r1_tarski(A_28, B_30))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.80/1.43  tff(c_45, plain, (![A_28]: (r1_tarski(A_28, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_28, '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_38])).
% 2.80/1.43  tff(c_10, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.80/1.43  tff(c_193, plain, (![B_62, A_63, C_64]: (v2_tops_2(B_62, A_63) | ~v2_tops_2(C_64, A_63) | ~r1_tarski(B_62, C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_63)))) | ~m1_subset_1(B_62, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_63)))) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.80/1.43  tff(c_413, plain, (![A_87, B_88, A_89]: (v2_tops_2(k4_xboole_0(A_87, B_88), A_89) | ~v2_tops_2(A_87, A_89) | ~m1_subset_1(A_87, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_89)))) | ~m1_subset_1(k4_xboole_0(A_87, B_88), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_89)))) | ~l1_pre_topc(A_89))), inference(resolution, [status(thm)], [c_4, c_193])).
% 2.80/1.43  tff(c_546, plain, (![A_114, B_115, A_116]: (v2_tops_2(k4_xboole_0(A_114, B_115), A_116) | ~v2_tops_2(A_114, A_116) | ~m1_subset_1(A_114, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_116)))) | ~l1_pre_topc(A_116) | ~r1_tarski(k4_xboole_0(A_114, B_115), k1_zfmisc_1(u1_struct_0(A_116))))), inference(resolution, [status(thm)], [c_10, c_413])).
% 2.80/1.43  tff(c_584, plain, (![A_114, B_115]: (v2_tops_2(k4_xboole_0(A_114, B_115), '#skF_1') | ~v2_tops_2(A_114, '#skF_1') | ~m1_subset_1(A_114, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(k4_xboole_0(A_114, B_115), '#skF_2'))), inference(resolution, [status(thm)], [c_45, c_546])).
% 2.80/1.43  tff(c_829, plain, (![A_146, B_147]: (v2_tops_2(k4_xboole_0(A_146, B_147), '#skF_1') | ~v2_tops_2(A_146, '#skF_1') | ~m1_subset_1(A_146, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~r1_tarski(k4_xboole_0(A_146, B_147), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_584])).
% 2.80/1.43  tff(c_836, plain, (![B_147]: (v2_tops_2(k4_xboole_0('#skF_2', B_147), '#skF_1') | ~v2_tops_2('#skF_2', '#skF_1') | ~r1_tarski(k4_xboole_0('#skF_2', B_147), '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_829])).
% 2.80/1.43  tff(c_841, plain, (![B_147]: (v2_tops_2(k4_xboole_0('#skF_2', B_147), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_16, c_836])).
% 2.80/1.43  tff(c_71, plain, (![A_39, B_40, C_41]: (k7_subset_1(A_39, B_40, C_41)=k4_xboole_0(B_40, C_41) | ~m1_subset_1(B_40, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.80/1.43  tff(c_80, plain, (![C_41]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_41)=k4_xboole_0('#skF_2', C_41))), inference(resolution, [status(thm)], [c_20, c_71])).
% 2.80/1.43  tff(c_14, plain, (~v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.80/1.43  tff(c_90, plain, (~v2_tops_2(k4_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_14])).
% 2.80/1.43  tff(c_845, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_841, c_90])).
% 2.80/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.43  
% 2.80/1.43  Inference rules
% 2.80/1.43  ----------------------
% 2.80/1.43  #Ref     : 0
% 2.80/1.43  #Sup     : 190
% 2.80/1.43  #Fact    : 0
% 2.80/1.43  #Define  : 0
% 2.80/1.43  #Split   : 3
% 2.80/1.43  #Chain   : 0
% 2.80/1.43  #Close   : 0
% 2.80/1.43  
% 2.80/1.43  Ordering : KBO
% 2.80/1.43  
% 2.80/1.43  Simplification rules
% 2.80/1.43  ----------------------
% 2.80/1.43  #Subsume      : 23
% 2.80/1.43  #Demod        : 33
% 2.80/1.43  #Tautology    : 46
% 2.80/1.43  #SimpNegUnit  : 0
% 2.80/1.43  #BackRed      : 2
% 2.80/1.43  
% 2.80/1.43  #Partial instantiations: 0
% 2.80/1.43  #Strategies tried      : 1
% 2.80/1.43  
% 2.80/1.43  Timing (in seconds)
% 2.80/1.43  ----------------------
% 2.80/1.44  Preprocessing        : 0.29
% 2.80/1.44  Parsing              : 0.15
% 2.80/1.44  CNF conversion       : 0.02
% 2.80/1.44  Main loop            : 0.40
% 2.80/1.44  Inferencing          : 0.15
% 2.80/1.44  Reduction            : 0.12
% 2.80/1.44  Demodulation         : 0.08
% 2.80/1.44  BG Simplification    : 0.02
% 2.80/1.44  Subsumption          : 0.09
% 2.80/1.44  Abstraction          : 0.02
% 2.80/1.44  MUC search           : 0.00
% 2.80/1.44  Cooper               : 0.00
% 2.80/1.44  Total                : 0.72
% 2.80/1.44  Index Insertion      : 0.00
% 2.80/1.44  Index Deletion       : 0.00
% 2.80/1.44  Index Matching       : 0.00
% 2.80/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
