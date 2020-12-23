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
% DateTime   : Thu Dec  3 10:23:52 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :   54 (  87 expanded)
%              Number of leaves         :   20 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :  103 ( 196 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_2 > v1_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_70,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ( v2_tops_2(B,A)
            <=> r1_tarski(B,k7_setfam_1(u1_struct_0(A),u1_pre_topc(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tops_2)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( r1_tarski(k7_setfam_1(A,B),C)
          <=> r1_tarski(B,k7_setfam_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_setfam_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> r1_tarski(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v2_tops_2(B,A)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tops_2)).

tff(c_20,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_22,plain,
    ( ~ r1_tarski('#skF_2',k7_setfam_1(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_30,plain,(
    ~ v2_tops_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_28,plain,
    ( v2_tops_2('#skF_2','#skF_1')
    | r1_tarski('#skF_2',k7_setfam_1(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_31,plain,(
    r1_tarski('#skF_2',k7_setfam_1(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28])).

tff(c_8,plain,(
    ! [A_7] :
      ( m1_subset_1(u1_pre_topc(A_7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_7))))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_92,plain,(
    ! [A_32,B_33,C_34] :
      ( r1_tarski(k7_setfam_1(A_32,B_33),C_34)
      | ~ r1_tarski(B_33,k7_setfam_1(A_32,C_34))
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k1_zfmisc_1(A_32)))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k1_zfmisc_1(A_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_130,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(k7_setfam_1(u1_struct_0(A_40),B_41),u1_pre_topc(A_40))
      | ~ r1_tarski(B_41,k7_setfam_1(u1_struct_0(A_40),u1_pre_topc(A_40)))
      | ~ m1_subset_1(B_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_40))))
      | ~ l1_pre_topc(A_40) ) ),
    inference(resolution,[status(thm)],[c_8,c_92])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k7_setfam_1(A_1,B_2),k1_zfmisc_1(k1_zfmisc_1(A_1)))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(k1_zfmisc_1(A_1))) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_33,plain,(
    ! [B_18,A_19] :
      ( v1_tops_2(B_18,A_19)
      | ~ r1_tarski(B_18,u1_pre_topc(A_19))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_19))))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_44,plain,(
    ! [A_19,B_2] :
      ( v1_tops_2(k7_setfam_1(u1_struct_0(A_19),B_2),A_19)
      | ~ r1_tarski(k7_setfam_1(u1_struct_0(A_19),B_2),u1_pre_topc(A_19))
      | ~ l1_pre_topc(A_19)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_19)))) ) ),
    inference(resolution,[status(thm)],[c_2,c_33])).

tff(c_138,plain,(
    ! [A_42,B_43] :
      ( v1_tops_2(k7_setfam_1(u1_struct_0(A_42),B_43),A_42)
      | ~ r1_tarski(B_43,k7_setfam_1(u1_struct_0(A_42),u1_pre_topc(A_42)))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_42))))
      | ~ l1_pre_topc(A_42) ) ),
    inference(resolution,[status(thm)],[c_130,c_44])).

tff(c_141,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_31,c_138])).

tff(c_144,plain,(
    v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_141])).

tff(c_10,plain,(
    ! [B_10,A_8] :
      ( v2_tops_2(B_10,A_8)
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0(A_8),B_10),A_8)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_8))))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_146,plain,
    ( v2_tops_2('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_144,c_10])).

tff(c_149,plain,(
    v2_tops_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_146])).

tff(c_151,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_149])).

tff(c_153,plain,(
    v2_tops_2('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_201,plain,(
    ! [A_54,B_55] :
      ( v1_tops_2(k7_setfam_1(u1_struct_0(A_54),B_55),A_54)
      | ~ v2_tops_2(B_55,A_54)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_54))))
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_208,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v2_tops_2('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_201])).

tff(c_213,plain,(
    v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_153,c_208])).

tff(c_178,plain,(
    ! [B_49,A_50] :
      ( r1_tarski(B_49,u1_pre_topc(A_50))
      | ~ v1_tops_2(B_49,A_50)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_50))))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_253,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(k7_setfam_1(u1_struct_0(A_64),B_65),u1_pre_topc(A_64))
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0(A_64),B_65),A_64)
      | ~ l1_pre_topc(A_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_64)))) ) ),
    inference(resolution,[status(thm)],[c_2,c_178])).

tff(c_6,plain,(
    ! [B_4,A_3,C_6] :
      ( r1_tarski(B_4,k7_setfam_1(A_3,C_6))
      | ~ r1_tarski(k7_setfam_1(A_3,B_4),C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k1_zfmisc_1(A_3)))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(k1_zfmisc_1(A_3))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_290,plain,(
    ! [B_78,A_79] :
      ( r1_tarski(B_78,k7_setfam_1(u1_struct_0(A_79),u1_pre_topc(A_79)))
      | ~ m1_subset_1(u1_pre_topc(A_79),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_79))))
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0(A_79),B_78),A_79)
      | ~ l1_pre_topc(A_79)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_79)))) ) ),
    inference(resolution,[status(thm)],[c_253,c_6])).

tff(c_294,plain,(
    ! [B_80,A_81] :
      ( r1_tarski(B_80,k7_setfam_1(u1_struct_0(A_81),u1_pre_topc(A_81)))
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0(A_81),B_80),A_81)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_81))))
      | ~ l1_pre_topc(A_81) ) ),
    inference(resolution,[status(thm)],[c_8,c_290])).

tff(c_152,plain,(
    ~ r1_tarski('#skF_2',k7_setfam_1(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_154,plain,(
    r1_tarski('#skF_2',k7_setfam_1(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_154])).

tff(c_157,plain,(
    ~ r1_tarski('#skF_2',k7_setfam_1(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_303,plain,
    ( ~ v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_294,c_157])).

tff(c_309,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_213,c_303])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % DateTime   : Tue Dec  1 10:41:22 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.32  
% 2.26/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.32  %$ v2_tops_2 > v1_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.26/1.32  
% 2.26/1.32  %Foreground sorts:
% 2.26/1.32  
% 2.26/1.32  
% 2.26/1.32  %Background operators:
% 2.26/1.32  
% 2.26/1.32  
% 2.26/1.32  %Foreground operators:
% 2.26/1.32  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.26/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.32  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 2.26/1.32  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.26/1.32  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.26/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.26/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.26/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.26/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.26/1.32  tff(v2_tops_2, type, v2_tops_2: ($i * $i) > $o).
% 2.26/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.26/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.26/1.32  
% 2.64/1.34  tff(f_70, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) <=> r1_tarski(B, k7_setfam_1(u1_struct_0(A), u1_pre_topc(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_tops_2)).
% 2.64/1.34  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 2.64/1.34  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(k7_setfam_1(A, B), C) <=> r1_tarski(B, k7_setfam_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_setfam_1)).
% 2.64/1.34  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 2.64/1.34  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> r1_tarski(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_tops_2)).
% 2.64/1.34  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) <=> v1_tops_2(k7_setfam_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tops_2)).
% 2.64/1.34  tff(c_20, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.64/1.34  tff(c_18, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.64/1.34  tff(c_22, plain, (~r1_tarski('#skF_2', k7_setfam_1(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.64/1.34  tff(c_30, plain, (~v2_tops_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_22])).
% 2.64/1.34  tff(c_28, plain, (v2_tops_2('#skF_2', '#skF_1') | r1_tarski('#skF_2', k7_setfam_1(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.64/1.34  tff(c_31, plain, (r1_tarski('#skF_2', k7_setfam_1(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_30, c_28])).
% 2.64/1.34  tff(c_8, plain, (![A_7]: (m1_subset_1(u1_pre_topc(A_7), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_7)))) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.64/1.34  tff(c_92, plain, (![A_32, B_33, C_34]: (r1_tarski(k7_setfam_1(A_32, B_33), C_34) | ~r1_tarski(B_33, k7_setfam_1(A_32, C_34)) | ~m1_subset_1(C_34, k1_zfmisc_1(k1_zfmisc_1(A_32))) | ~m1_subset_1(B_33, k1_zfmisc_1(k1_zfmisc_1(A_32))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.64/1.34  tff(c_130, plain, (![A_40, B_41]: (r1_tarski(k7_setfam_1(u1_struct_0(A_40), B_41), u1_pre_topc(A_40)) | ~r1_tarski(B_41, k7_setfam_1(u1_struct_0(A_40), u1_pre_topc(A_40))) | ~m1_subset_1(B_41, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_40)))) | ~l1_pre_topc(A_40))), inference(resolution, [status(thm)], [c_8, c_92])).
% 2.64/1.34  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k7_setfam_1(A_1, B_2), k1_zfmisc_1(k1_zfmisc_1(A_1))) | ~m1_subset_1(B_2, k1_zfmisc_1(k1_zfmisc_1(A_1))))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.64/1.34  tff(c_33, plain, (![B_18, A_19]: (v1_tops_2(B_18, A_19) | ~r1_tarski(B_18, u1_pre_topc(A_19)) | ~m1_subset_1(B_18, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_19)))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.64/1.34  tff(c_44, plain, (![A_19, B_2]: (v1_tops_2(k7_setfam_1(u1_struct_0(A_19), B_2), A_19) | ~r1_tarski(k7_setfam_1(u1_struct_0(A_19), B_2), u1_pre_topc(A_19)) | ~l1_pre_topc(A_19) | ~m1_subset_1(B_2, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_19)))))), inference(resolution, [status(thm)], [c_2, c_33])).
% 2.64/1.34  tff(c_138, plain, (![A_42, B_43]: (v1_tops_2(k7_setfam_1(u1_struct_0(A_42), B_43), A_42) | ~r1_tarski(B_43, k7_setfam_1(u1_struct_0(A_42), u1_pre_topc(A_42))) | ~m1_subset_1(B_43, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_42)))) | ~l1_pre_topc(A_42))), inference(resolution, [status(thm)], [c_130, c_44])).
% 2.64/1.34  tff(c_141, plain, (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_31, c_138])).
% 2.64/1.34  tff(c_144, plain, (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_141])).
% 2.64/1.34  tff(c_10, plain, (![B_10, A_8]: (v2_tops_2(B_10, A_8) | ~v1_tops_2(k7_setfam_1(u1_struct_0(A_8), B_10), A_8) | ~m1_subset_1(B_10, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_8)))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.64/1.34  tff(c_146, plain, (v2_tops_2('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_144, c_10])).
% 2.64/1.34  tff(c_149, plain, (v2_tops_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_146])).
% 2.64/1.34  tff(c_151, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_149])).
% 2.64/1.34  tff(c_153, plain, (v2_tops_2('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_22])).
% 2.64/1.34  tff(c_201, plain, (![A_54, B_55]: (v1_tops_2(k7_setfam_1(u1_struct_0(A_54), B_55), A_54) | ~v2_tops_2(B_55, A_54) | ~m1_subset_1(B_55, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_54)))) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.64/1.34  tff(c_208, plain, (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v2_tops_2('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_201])).
% 2.64/1.34  tff(c_213, plain, (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_153, c_208])).
% 2.64/1.34  tff(c_178, plain, (![B_49, A_50]: (r1_tarski(B_49, u1_pre_topc(A_50)) | ~v1_tops_2(B_49, A_50) | ~m1_subset_1(B_49, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_50)))) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.64/1.34  tff(c_253, plain, (![A_64, B_65]: (r1_tarski(k7_setfam_1(u1_struct_0(A_64), B_65), u1_pre_topc(A_64)) | ~v1_tops_2(k7_setfam_1(u1_struct_0(A_64), B_65), A_64) | ~l1_pre_topc(A_64) | ~m1_subset_1(B_65, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_64)))))), inference(resolution, [status(thm)], [c_2, c_178])).
% 2.64/1.34  tff(c_6, plain, (![B_4, A_3, C_6]: (r1_tarski(B_4, k7_setfam_1(A_3, C_6)) | ~r1_tarski(k7_setfam_1(A_3, B_4), C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(k1_zfmisc_1(A_3))) | ~m1_subset_1(B_4, k1_zfmisc_1(k1_zfmisc_1(A_3))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.64/1.34  tff(c_290, plain, (![B_78, A_79]: (r1_tarski(B_78, k7_setfam_1(u1_struct_0(A_79), u1_pre_topc(A_79))) | ~m1_subset_1(u1_pre_topc(A_79), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_79)))) | ~v1_tops_2(k7_setfam_1(u1_struct_0(A_79), B_78), A_79) | ~l1_pre_topc(A_79) | ~m1_subset_1(B_78, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_79)))))), inference(resolution, [status(thm)], [c_253, c_6])).
% 2.64/1.34  tff(c_294, plain, (![B_80, A_81]: (r1_tarski(B_80, k7_setfam_1(u1_struct_0(A_81), u1_pre_topc(A_81))) | ~v1_tops_2(k7_setfam_1(u1_struct_0(A_81), B_80), A_81) | ~m1_subset_1(B_80, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_81)))) | ~l1_pre_topc(A_81))), inference(resolution, [status(thm)], [c_8, c_290])).
% 2.64/1.34  tff(c_152, plain, (~r1_tarski('#skF_2', k7_setfam_1(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_22])).
% 2.64/1.34  tff(c_154, plain, (r1_tarski('#skF_2', k7_setfam_1(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_28])).
% 2.64/1.34  tff(c_155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_152, c_154])).
% 2.64/1.34  tff(c_157, plain, (~r1_tarski('#skF_2', k7_setfam_1(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_28])).
% 2.64/1.34  tff(c_303, plain, (~v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_294, c_157])).
% 2.64/1.34  tff(c_309, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_213, c_303])).
% 2.64/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.34  
% 2.64/1.34  Inference rules
% 2.64/1.34  ----------------------
% 2.64/1.34  #Ref     : 0
% 2.64/1.34  #Sup     : 53
% 2.64/1.34  #Fact    : 0
% 2.64/1.34  #Define  : 0
% 2.64/1.34  #Split   : 8
% 2.64/1.34  #Chain   : 0
% 2.64/1.34  #Close   : 0
% 2.64/1.34  
% 2.64/1.34  Ordering : KBO
% 2.64/1.34  
% 2.64/1.34  Simplification rules
% 2.64/1.34  ----------------------
% 2.64/1.34  #Subsume      : 3
% 2.64/1.34  #Demod        : 21
% 2.64/1.34  #Tautology    : 16
% 2.64/1.34  #SimpNegUnit  : 5
% 2.64/1.34  #BackRed      : 0
% 2.64/1.34  
% 2.64/1.34  #Partial instantiations: 0
% 2.64/1.34  #Strategies tried      : 1
% 2.64/1.34  
% 2.64/1.34  Timing (in seconds)
% 2.64/1.34  ----------------------
% 2.64/1.34  Preprocessing        : 0.29
% 2.64/1.34  Parsing              : 0.16
% 2.64/1.34  CNF conversion       : 0.02
% 2.64/1.34  Main loop            : 0.27
% 2.64/1.34  Inferencing          : 0.11
% 2.64/1.34  Reduction            : 0.07
% 2.64/1.34  Demodulation         : 0.04
% 2.64/1.34  BG Simplification    : 0.02
% 2.64/1.34  Subsumption          : 0.06
% 2.64/1.34  Abstraction          : 0.01
% 2.64/1.34  MUC search           : 0.00
% 2.64/1.34  Cooper               : 0.00
% 2.64/1.34  Total                : 0.59
% 2.64/1.34  Index Insertion      : 0.00
% 2.64/1.34  Index Deletion       : 0.00
% 2.64/1.34  Index Matching       : 0.00
% 2.64/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
