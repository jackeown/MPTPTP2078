%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:34 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 112 expanded)
%              Number of leaves         :   30 (  53 expanded)
%              Depth                    :   10
%              Number of atoms          :  113 ( 271 expanded)
%              Number of equality atoms :   15 (  17 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => m2_connsp_2(k2_struct_0(A),A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m2_connsp_2(C,A,B)
              <=> r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k7_subset_1(u1_struct_0(A),k2_struct_0(A),k7_subset_1(u1_struct_0(A),k2_struct_0(A),B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_pre_topc)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

tff(c_22,plain,(
    ~ m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_12,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_10] :
      ( m1_subset_1(k2_struct_0(A_10),k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_286,plain,(
    ! [B_54,A_55,C_56] :
      ( r1_tarski(B_54,k1_tops_1(A_55,C_56))
      | ~ m2_connsp_2(C_56,A_55,B_54)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_pre_topc(A_55)
      | ~ v2_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_290,plain,(
    ! [B_54] :
      ( r1_tarski(B_54,k1_tops_1('#skF_1','#skF_2'))
      | ~ m2_connsp_2('#skF_2','#skF_1',B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_286])).

tff(c_295,plain,(
    ! [B_57] :
      ( r1_tarski(B_57,k1_tops_1('#skF_1','#skF_2'))
      | ~ m2_connsp_2('#skF_2','#skF_1',B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_290])).

tff(c_303,plain,
    ( r1_tarski(k2_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'))
    | ~ m2_connsp_2('#skF_2','#skF_1',k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_295])).

tff(c_306,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_303])).

tff(c_309,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_306])).

tff(c_313,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_309])).

tff(c_315,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_303])).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_80,plain,(
    ! [A_35,B_36,C_37] :
      ( k7_subset_1(A_35,B_36,C_37) = k4_xboole_0(B_36,C_37)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_85,plain,(
    ! [A_10,C_37] :
      ( k7_subset_1(u1_struct_0(A_10),k2_struct_0(A_10),C_37) = k4_xboole_0(k2_struct_0(A_10),C_37)
      | ~ l1_struct_0(A_10) ) ),
    inference(resolution,[status(thm)],[c_10,c_80])).

tff(c_14,plain,(
    ! [A_12,B_14] :
      ( k7_subset_1(u1_struct_0(A_12),k2_struct_0(A_12),k7_subset_1(u1_struct_0(A_12),k2_struct_0(A_12),B_14)) = B_14
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_113,plain,(
    ! [A_41,C_42] :
      ( k7_subset_1(u1_struct_0(A_41),k2_struct_0(A_41),C_42) = k4_xboole_0(k2_struct_0(A_41),C_42)
      | ~ l1_struct_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_10,c_80])).

tff(c_326,plain,(
    ! [A_60,B_61] :
      ( k4_xboole_0(k2_struct_0(A_60),k7_subset_1(u1_struct_0(A_60),k2_struct_0(A_60),B_61)) = B_61
      | ~ l1_struct_0(A_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_struct_0(A_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_113])).

tff(c_344,plain,(
    ! [A_10,C_37] :
      ( k4_xboole_0(k2_struct_0(A_10),k4_xboole_0(k2_struct_0(A_10),C_37)) = C_37
      | ~ l1_struct_0(A_10)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_struct_0(A_10)
      | ~ l1_struct_0(A_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_326])).

tff(c_353,plain,(
    ! [A_62,C_63] :
      ( k3_xboole_0(k2_struct_0(A_62),C_63) = C_63
      | ~ l1_struct_0(A_62)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_struct_0(A_62)
      | ~ l1_struct_0(A_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_344])).

tff(c_359,plain,
    ( k3_xboole_0(k2_struct_0('#skF_1'),'#skF_2') = '#skF_2'
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_353])).

tff(c_363,plain,(
    k3_xboole_0(k2_struct_0('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_359])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_376,plain,(
    r1_tarski('#skF_2',k2_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_2])).

tff(c_16,plain,(
    ! [A_15] :
      ( k1_tops_1(A_15,k2_struct_0(A_15)) = k2_struct_0(A_15)
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_189,plain,(
    ! [C_47,A_48,B_49] :
      ( m2_connsp_2(C_47,A_48,B_49)
      | ~ r1_tarski(B_49,k1_tops_1(A_48,C_47))
      | ~ m1_subset_1(C_47,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_646,plain,(
    ! [A_76,B_77] :
      ( m2_connsp_2(k2_struct_0(A_76),A_76,B_77)
      | ~ r1_tarski(B_77,k2_struct_0(A_76))
      | ~ m1_subset_1(k2_struct_0(A_76),k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76)
      | ~ v2_pre_topc(A_76)
      | ~ l1_pre_topc(A_76)
      | ~ v2_pre_topc(A_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_189])).

tff(c_650,plain,(
    ! [A_78,B_79] :
      ( m2_connsp_2(k2_struct_0(A_78),A_78,B_79)
      | ~ r1_tarski(B_79,k2_struct_0(A_78))
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78)
      | ~ v2_pre_topc(A_78)
      | ~ l1_struct_0(A_78) ) ),
    inference(resolution,[status(thm)],[c_10,c_646])).

tff(c_654,plain,
    ( m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1','#skF_2')
    | ~ r1_tarski('#skF_2',k2_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_650])).

tff(c_658,plain,(
    m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_28,c_26,c_376,c_654])).

tff(c_660,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_658])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:24:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.43  
% 2.81/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.44  %$ m2_connsp_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 2.81/1.44  
% 2.81/1.44  %Foreground sorts:
% 2.81/1.44  
% 2.81/1.44  
% 2.81/1.44  %Background operators:
% 2.81/1.44  
% 2.81/1.44  
% 2.81/1.44  %Foreground operators:
% 2.81/1.44  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.81/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.81/1.44  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.81/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.81/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.81/1.44  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.81/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.81/1.44  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.81/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.81/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.81/1.44  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.81/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.44  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.81/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.81/1.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.81/1.44  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.81/1.44  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 2.81/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.81/1.44  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.81/1.44  
% 2.81/1.45  tff(f_83, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => m2_connsp_2(k2_struct_0(A), A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_connsp_2)).
% 2.81/1.45  tff(f_43, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.81/1.45  tff(f_39, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 2.81/1.45  tff(f_70, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_connsp_2)).
% 2.81/1.45  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.81/1.45  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.81/1.45  tff(f_50, axiom, (![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k7_subset_1(u1_struct_0(A), k2_struct_0(A), k7_subset_1(u1_struct_0(A), k2_struct_0(A), B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_pre_topc)).
% 2.81/1.45  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.81/1.45  tff(f_56, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tops_1)).
% 2.81/1.45  tff(c_22, plain, (~m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.81/1.45  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.81/1.45  tff(c_12, plain, (![A_11]: (l1_struct_0(A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.81/1.45  tff(c_10, plain, (![A_10]: (m1_subset_1(k2_struct_0(A_10), k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.81/1.45  tff(c_28, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.81/1.45  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.81/1.45  tff(c_286, plain, (![B_54, A_55, C_56]: (r1_tarski(B_54, k1_tops_1(A_55, C_56)) | ~m2_connsp_2(C_56, A_55, B_54) | ~m1_subset_1(C_56, k1_zfmisc_1(u1_struct_0(A_55))) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_pre_topc(A_55) | ~v2_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.81/1.45  tff(c_290, plain, (![B_54]: (r1_tarski(B_54, k1_tops_1('#skF_1', '#skF_2')) | ~m2_connsp_2('#skF_2', '#skF_1', B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_286])).
% 2.81/1.45  tff(c_295, plain, (![B_57]: (r1_tarski(B_57, k1_tops_1('#skF_1', '#skF_2')) | ~m2_connsp_2('#skF_2', '#skF_1', B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_290])).
% 2.81/1.45  tff(c_303, plain, (r1_tarski(k2_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2')) | ~m2_connsp_2('#skF_2', '#skF_1', k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_10, c_295])).
% 2.81/1.45  tff(c_306, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_303])).
% 2.81/1.45  tff(c_309, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_306])).
% 2.81/1.45  tff(c_313, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_309])).
% 2.81/1.45  tff(c_315, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_303])).
% 2.81/1.45  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k4_xboole_0(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.81/1.45  tff(c_80, plain, (![A_35, B_36, C_37]: (k7_subset_1(A_35, B_36, C_37)=k4_xboole_0(B_36, C_37) | ~m1_subset_1(B_36, k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.81/1.45  tff(c_85, plain, (![A_10, C_37]: (k7_subset_1(u1_struct_0(A_10), k2_struct_0(A_10), C_37)=k4_xboole_0(k2_struct_0(A_10), C_37) | ~l1_struct_0(A_10))), inference(resolution, [status(thm)], [c_10, c_80])).
% 2.81/1.45  tff(c_14, plain, (![A_12, B_14]: (k7_subset_1(u1_struct_0(A_12), k2_struct_0(A_12), k7_subset_1(u1_struct_0(A_12), k2_struct_0(A_12), B_14))=B_14 | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.81/1.45  tff(c_113, plain, (![A_41, C_42]: (k7_subset_1(u1_struct_0(A_41), k2_struct_0(A_41), C_42)=k4_xboole_0(k2_struct_0(A_41), C_42) | ~l1_struct_0(A_41))), inference(resolution, [status(thm)], [c_10, c_80])).
% 2.81/1.45  tff(c_326, plain, (![A_60, B_61]: (k4_xboole_0(k2_struct_0(A_60), k7_subset_1(u1_struct_0(A_60), k2_struct_0(A_60), B_61))=B_61 | ~l1_struct_0(A_60) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_struct_0(A_60))), inference(superposition, [status(thm), theory('equality')], [c_14, c_113])).
% 2.81/1.45  tff(c_344, plain, (![A_10, C_37]: (k4_xboole_0(k2_struct_0(A_10), k4_xboole_0(k2_struct_0(A_10), C_37))=C_37 | ~l1_struct_0(A_10) | ~m1_subset_1(C_37, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_struct_0(A_10) | ~l1_struct_0(A_10))), inference(superposition, [status(thm), theory('equality')], [c_85, c_326])).
% 2.81/1.45  tff(c_353, plain, (![A_62, C_63]: (k3_xboole_0(k2_struct_0(A_62), C_63)=C_63 | ~l1_struct_0(A_62) | ~m1_subset_1(C_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_struct_0(A_62) | ~l1_struct_0(A_62))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_344])).
% 2.81/1.45  tff(c_359, plain, (k3_xboole_0(k2_struct_0('#skF_1'), '#skF_2')='#skF_2' | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_24, c_353])).
% 2.81/1.45  tff(c_363, plain, (k3_xboole_0(k2_struct_0('#skF_1'), '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_315, c_359])).
% 2.81/1.45  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.81/1.45  tff(c_376, plain, (r1_tarski('#skF_2', k2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_363, c_2])).
% 2.81/1.45  tff(c_16, plain, (![A_15]: (k1_tops_1(A_15, k2_struct_0(A_15))=k2_struct_0(A_15) | ~l1_pre_topc(A_15) | ~v2_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.81/1.45  tff(c_189, plain, (![C_47, A_48, B_49]: (m2_connsp_2(C_47, A_48, B_49) | ~r1_tarski(B_49, k1_tops_1(A_48, C_47)) | ~m1_subset_1(C_47, k1_zfmisc_1(u1_struct_0(A_48))) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.81/1.45  tff(c_646, plain, (![A_76, B_77]: (m2_connsp_2(k2_struct_0(A_76), A_76, B_77) | ~r1_tarski(B_77, k2_struct_0(A_76)) | ~m1_subset_1(k2_struct_0(A_76), k1_zfmisc_1(u1_struct_0(A_76))) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76) | ~v2_pre_topc(A_76) | ~l1_pre_topc(A_76) | ~v2_pre_topc(A_76))), inference(superposition, [status(thm), theory('equality')], [c_16, c_189])).
% 2.81/1.45  tff(c_650, plain, (![A_78, B_79]: (m2_connsp_2(k2_struct_0(A_78), A_78, B_79) | ~r1_tarski(B_79, k2_struct_0(A_78)) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78) | ~v2_pre_topc(A_78) | ~l1_struct_0(A_78))), inference(resolution, [status(thm)], [c_10, c_646])).
% 2.81/1.45  tff(c_654, plain, (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', '#skF_2') | ~r1_tarski('#skF_2', k2_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_24, c_650])).
% 2.81/1.45  tff(c_658, plain, (m2_connsp_2(k2_struct_0('#skF_1'), '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_315, c_28, c_26, c_376, c_654])).
% 2.81/1.45  tff(c_660, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_658])).
% 2.81/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.45  
% 2.81/1.45  Inference rules
% 2.81/1.45  ----------------------
% 2.81/1.45  #Ref     : 0
% 2.81/1.45  #Sup     : 157
% 2.81/1.45  #Fact    : 0
% 2.81/1.45  #Define  : 0
% 2.81/1.45  #Split   : 3
% 2.81/1.45  #Chain   : 0
% 2.81/1.45  #Close   : 0
% 2.81/1.45  
% 2.81/1.45  Ordering : KBO
% 2.81/1.45  
% 2.81/1.45  Simplification rules
% 2.81/1.45  ----------------------
% 2.81/1.45  #Subsume      : 6
% 2.81/1.45  #Demod        : 81
% 2.81/1.45  #Tautology    : 77
% 2.81/1.45  #SimpNegUnit  : 1
% 2.81/1.45  #BackRed      : 0
% 2.81/1.45  
% 2.81/1.45  #Partial instantiations: 0
% 2.81/1.45  #Strategies tried      : 1
% 2.81/1.45  
% 2.81/1.45  Timing (in seconds)
% 2.81/1.45  ----------------------
% 2.93/1.45  Preprocessing        : 0.32
% 2.93/1.45  Parsing              : 0.18
% 2.93/1.45  CNF conversion       : 0.02
% 2.93/1.45  Main loop            : 0.33
% 2.93/1.45  Inferencing          : 0.13
% 2.93/1.45  Reduction            : 0.11
% 2.93/1.45  Demodulation         : 0.08
% 2.93/1.45  BG Simplification    : 0.02
% 2.93/1.45  Subsumption          : 0.05
% 2.93/1.45  Abstraction          : 0.02
% 2.93/1.45  MUC search           : 0.00
% 2.93/1.45  Cooper               : 0.00
% 2.93/1.45  Total                : 0.67
% 2.93/1.45  Index Insertion      : 0.00
% 2.93/1.45  Index Deletion       : 0.00
% 2.93/1.45  Index Matching       : 0.00
% 2.93/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
