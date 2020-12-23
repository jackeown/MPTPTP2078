%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:44 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   47 (  71 expanded)
%              Number of leaves         :   19 (  36 expanded)
%              Depth                    :   15
%              Number of atoms          :   80 ( 182 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_61,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( ( r1_tarski(B,C)
                    & v1_tops_2(C,A) )
                 => v1_tops_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tops_2)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r2_hidden(C,B)
                 => v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_16,plain,(
    ~ v1_tops_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_26,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    v1_tops_2('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14,plain,(
    ! [A_6,B_12] :
      ( m1_subset_1('#skF_2'(A_6,B_12),k1_zfmisc_1(u1_struct_0(A_6)))
      | v1_tops_2(B_12,A_6)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_6))))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28,plain,(
    ! [A_22,B_23] :
      ( ~ r2_hidden('#skF_1'(A_22,B_23),B_23)
      | r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_33,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_28])).

tff(c_20,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_77,plain,(
    ! [A_41,B_42] :
      ( r2_hidden('#skF_2'(A_41,B_42),B_42)
      | v1_tops_2(B_42,A_41)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_41))))
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_81,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v1_tops_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_77])).

tff(c_87,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v1_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_81])).

tff(c_88,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_87])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_92,plain,(
    ! [B_43] :
      ( r2_hidden('#skF_2'('#skF_3','#skF_4'),B_43)
      | ~ r1_tarski('#skF_4',B_43) ) ),
    inference(resolution,[status(thm)],[c_88,c_2])).

tff(c_105,plain,(
    ! [B_46,B_47] :
      ( r2_hidden('#skF_2'('#skF_3','#skF_4'),B_46)
      | ~ r1_tarski(B_47,B_46)
      | ~ r1_tarski('#skF_4',B_47) ) ),
    inference(resolution,[status(thm)],[c_92,c_2])).

tff(c_111,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_5')
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_105])).

tff(c_116,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_111])).

tff(c_160,plain,(
    ! [C_62,A_63,B_64] :
      ( v3_pre_topc(C_62,A_63)
      | ~ r2_hidden(C_62,B_64)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ v1_tops_2(B_64,A_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_63))))
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_194,plain,(
    ! [A_66] :
      ( v3_pre_topc('#skF_2'('#skF_3','#skF_4'),A_66)
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ v1_tops_2('#skF_5',A_66)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_66))))
      | ~ l1_pre_topc(A_66) ) ),
    inference(resolution,[status(thm)],[c_116,c_160])).

tff(c_198,plain,
    ( v3_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | ~ v1_tops_2('#skF_5','#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | v1_tops_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_194])).

tff(c_201,plain,
    ( v3_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v1_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_18,c_198])).

tff(c_202,plain,(
    v3_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_201])).

tff(c_10,plain,(
    ! [A_6,B_12] :
      ( ~ v3_pre_topc('#skF_2'(A_6,B_12),A_6)
      | v1_tops_2(B_12,A_6)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_6))))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_204,plain,
    ( v1_tops_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_202,c_10])).

tff(c_207,plain,(
    v1_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_204])).

tff(c_209,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_207])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:17:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.33  
% 2.07/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.33  %$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.07/1.33  
% 2.07/1.33  %Foreground sorts:
% 2.07/1.33  
% 2.07/1.33  
% 2.07/1.33  %Background operators:
% 2.07/1.33  
% 2.07/1.33  
% 2.07/1.33  %Foreground operators:
% 2.07/1.33  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.07/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.07/1.33  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 2.07/1.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.07/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.07/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.07/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.07/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.07/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.07/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.07/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.07/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.07/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.07/1.33  
% 2.07/1.34  tff(f_61, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v1_tops_2(C, A)) => v1_tops_2(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_tops_2)).
% 2.07/1.34  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, B) => v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_2)).
% 2.07/1.34  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.07/1.34  tff(c_16, plain, (~v1_tops_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.07/1.34  tff(c_26, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.07/1.34  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.07/1.34  tff(c_22, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.07/1.34  tff(c_18, plain, (v1_tops_2('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.07/1.34  tff(c_14, plain, (![A_6, B_12]: (m1_subset_1('#skF_2'(A_6, B_12), k1_zfmisc_1(u1_struct_0(A_6))) | v1_tops_2(B_12, A_6) | ~m1_subset_1(B_12, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_6)))) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.07/1.34  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.07/1.34  tff(c_28, plain, (![A_22, B_23]: (~r2_hidden('#skF_1'(A_22, B_23), B_23) | r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.07/1.34  tff(c_33, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_28])).
% 2.07/1.34  tff(c_20, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.07/1.34  tff(c_77, plain, (![A_41, B_42]: (r2_hidden('#skF_2'(A_41, B_42), B_42) | v1_tops_2(B_42, A_41) | ~m1_subset_1(B_42, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_41)))) | ~l1_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.07/1.34  tff(c_81, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | v1_tops_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_24, c_77])).
% 2.07/1.34  tff(c_87, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | v1_tops_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_81])).
% 2.07/1.34  tff(c_88, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_16, c_87])).
% 2.07/1.34  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.07/1.34  tff(c_92, plain, (![B_43]: (r2_hidden('#skF_2'('#skF_3', '#skF_4'), B_43) | ~r1_tarski('#skF_4', B_43))), inference(resolution, [status(thm)], [c_88, c_2])).
% 2.07/1.34  tff(c_105, plain, (![B_46, B_47]: (r2_hidden('#skF_2'('#skF_3', '#skF_4'), B_46) | ~r1_tarski(B_47, B_46) | ~r1_tarski('#skF_4', B_47))), inference(resolution, [status(thm)], [c_92, c_2])).
% 2.07/1.34  tff(c_111, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_5') | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_20, c_105])).
% 2.07/1.34  tff(c_116, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_33, c_111])).
% 2.07/1.34  tff(c_160, plain, (![C_62, A_63, B_64]: (v3_pre_topc(C_62, A_63) | ~r2_hidden(C_62, B_64) | ~m1_subset_1(C_62, k1_zfmisc_1(u1_struct_0(A_63))) | ~v1_tops_2(B_64, A_63) | ~m1_subset_1(B_64, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_63)))) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.07/1.34  tff(c_194, plain, (![A_66]: (v3_pre_topc('#skF_2'('#skF_3', '#skF_4'), A_66) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0(A_66))) | ~v1_tops_2('#skF_5', A_66) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_66)))) | ~l1_pre_topc(A_66))), inference(resolution, [status(thm)], [c_116, c_160])).
% 2.07/1.35  tff(c_198, plain, (v3_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | ~v1_tops_2('#skF_5', '#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | v1_tops_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_14, c_194])).
% 2.07/1.35  tff(c_201, plain, (v3_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v1_tops_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_18, c_198])).
% 2.07/1.35  tff(c_202, plain, (v3_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_16, c_201])).
% 2.07/1.35  tff(c_10, plain, (![A_6, B_12]: (~v3_pre_topc('#skF_2'(A_6, B_12), A_6) | v1_tops_2(B_12, A_6) | ~m1_subset_1(B_12, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_6)))) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.07/1.35  tff(c_204, plain, (v1_tops_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_202, c_10])).
% 2.07/1.35  tff(c_207, plain, (v1_tops_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_204])).
% 2.07/1.35  tff(c_209, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_207])).
% 2.07/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.35  
% 2.07/1.35  Inference rules
% 2.07/1.35  ----------------------
% 2.07/1.35  #Ref     : 0
% 2.07/1.35  #Sup     : 42
% 2.07/1.35  #Fact    : 0
% 2.07/1.35  #Define  : 0
% 2.07/1.35  #Split   : 1
% 2.07/1.35  #Chain   : 0
% 2.07/1.35  #Close   : 0
% 2.35/1.35  
% 2.35/1.35  Ordering : KBO
% 2.35/1.35  
% 2.35/1.35  Simplification rules
% 2.35/1.35  ----------------------
% 2.35/1.35  #Subsume      : 11
% 2.35/1.35  #Demod        : 15
% 2.35/1.35  #Tautology    : 5
% 2.35/1.35  #SimpNegUnit  : 4
% 2.35/1.35  #BackRed      : 0
% 2.35/1.35  
% 2.35/1.35  #Partial instantiations: 0
% 2.35/1.35  #Strategies tried      : 1
% 2.35/1.35  
% 2.35/1.35  Timing (in seconds)
% 2.35/1.35  ----------------------
% 2.35/1.35  Preprocessing        : 0.27
% 2.35/1.35  Parsing              : 0.15
% 2.35/1.35  CNF conversion       : 0.02
% 2.35/1.35  Main loop            : 0.29
% 2.35/1.35  Inferencing          : 0.12
% 2.35/1.35  Reduction            : 0.07
% 2.35/1.35  Demodulation         : 0.05
% 2.35/1.35  BG Simplification    : 0.01
% 2.35/1.35  Subsumption          : 0.06
% 2.35/1.35  Abstraction          : 0.01
% 2.35/1.35  MUC search           : 0.00
% 2.35/1.35  Cooper               : 0.00
% 2.35/1.35  Total                : 0.59
% 2.35/1.35  Index Insertion      : 0.00
% 2.35/1.35  Index Deletion       : 0.00
% 2.35/1.35  Index Matching       : 0.00
% 2.35/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
