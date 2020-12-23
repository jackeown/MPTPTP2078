%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:08 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 116 expanded)
%              Number of leaves         :   22 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :  140 ( 328 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > k1_tex_2 > #nlpp > u1_struct_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_tex_2,type,(
    k1_tex_2: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v2_pre_topc(k1_tex_2(A,B))
             => ( v1_tdlat_3(k1_tex_2(A,B))
                & v2_tdlat_3(k1_tex_2(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tex_2)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & ~ v1_tdlat_3(A) )
       => ( ~ v2_struct_0(A)
          & ~ v7_struct_0(A)
          & v2_pre_topc(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_tex_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_32,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & ~ v2_tdlat_3(A) )
       => ( ~ v2_struct_0(A)
          & ~ v7_struct_0(A)
          & v2_pre_topc(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_tex_1)).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_106,plain,(
    ! [A_27,B_28] :
      ( ~ v2_struct_0(k1_tex_2(A_27,B_28))
      | ~ m1_subset_1(B_28,u1_struct_0(A_27))
      | ~ l1_pre_topc(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_109,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_106])).

tff(c_112,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_109])).

tff(c_113,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_112])).

tff(c_49,plain,(
    ! [A_17,B_18] :
      ( ~ v2_struct_0(k1_tex_2(A_17,B_18))
      | ~ m1_subset_1(B_18,u1_struct_0(A_17))
      | ~ l1_pre_topc(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_52,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_49])).

tff(c_55,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_52])).

tff(c_56,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_55])).

tff(c_28,plain,
    ( ~ v2_tdlat_3(k1_tex_2('#skF_1','#skF_2'))
    | ~ v1_tdlat_3(k1_tex_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_38,plain,(
    ~ v1_tdlat_3(k1_tex_2('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_30,plain,(
    v2_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_57,plain,(
    ! [A_19,B_20] :
      ( v7_struct_0(k1_tex_2(A_19,B_20))
      | ~ m1_subset_1(B_20,u1_struct_0(A_19))
      | ~ l1_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_60,plain,
    ( v7_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_57])).

tff(c_63,plain,
    ( v7_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_60])).

tff(c_64,plain,(
    v7_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_63])).

tff(c_6,plain,(
    ! [A_4] :
      ( ~ v7_struct_0(A_4)
      | v1_tdlat_3(A_4)
      | ~ v2_pre_topc(A_4)
      | v2_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_70,plain,
    ( v1_tdlat_3(k1_tex_2('#skF_1','#skF_2'))
    | ~ v2_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_64,c_6])).

tff(c_77,plain,
    ( v1_tdlat_3(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_70])).

tff(c_78,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_38,c_77])).

tff(c_79,plain,(
    ! [A_21,B_22] :
      ( m1_pre_topc(k1_tex_2(A_21,B_22),A_21)
      | ~ m1_subset_1(B_22,u1_struct_0(A_21))
      | ~ l1_pre_topc(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_81,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_79])).

tff(c_84,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_81])).

tff(c_85,plain,(
    m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_84])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( l1_pre_topc(B_3)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_88,plain,
    ( l1_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_85,c_2])).

tff(c_91,plain,(
    l1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_88])).

tff(c_93,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_91])).

tff(c_94,plain,(
    ~ v2_tdlat_3(k1_tex_2('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_114,plain,(
    ! [A_29,B_30] :
      ( v7_struct_0(k1_tex_2(A_29,B_30))
      | ~ m1_subset_1(B_30,u1_struct_0(A_29))
      | ~ l1_pre_topc(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_117,plain,
    ( v7_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_114])).

tff(c_120,plain,
    ( v7_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_117])).

tff(c_121,plain,(
    v7_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_120])).

tff(c_12,plain,(
    ! [A_5] :
      ( ~ v7_struct_0(A_5)
      | v2_tdlat_3(A_5)
      | ~ v2_pre_topc(A_5)
      | v2_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_127,plain,
    ( v2_tdlat_3(k1_tex_2('#skF_1','#skF_2'))
    | ~ v2_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_121,c_12])).

tff(c_134,plain,
    ( v2_tdlat_3(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_127])).

tff(c_135,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_94,c_134])).

tff(c_136,plain,(
    ! [A_31,B_32] :
      ( m1_pre_topc(k1_tex_2(A_31,B_32),A_31)
      | ~ m1_subset_1(B_32,u1_struct_0(A_31))
      | ~ l1_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_138,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_136])).

tff(c_141,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_138])).

tff(c_142,plain,(
    m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_141])).

tff(c_145,plain,
    ( l1_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_142,c_2])).

tff(c_148,plain,(
    l1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_145])).

tff(c_150,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_148])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:59:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.18  
% 1.98/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.19  %$ m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > k1_tex_2 > #nlpp > u1_struct_0 > #skF_2 > #skF_1
% 1.98/1.19  
% 1.98/1.19  %Foreground sorts:
% 1.98/1.19  
% 1.98/1.19  
% 1.98/1.19  %Background operators:
% 1.98/1.19  
% 1.98/1.19  
% 1.98/1.19  %Foreground operators:
% 1.98/1.19  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.98/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.19  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 1.98/1.19  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.98/1.19  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 1.98/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.19  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 1.98/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.19  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 1.98/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.19  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 1.98/1.19  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.98/1.19  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.98/1.19  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 1.98/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.98/1.19  
% 1.98/1.20  tff(f_111, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v2_pre_topc(k1_tex_2(A, B)) => (v1_tdlat_3(k1_tex_2(A, B)) & v2_tdlat_3(k1_tex_2(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tex_2)).
% 1.98/1.20  tff(f_96, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tex_2)).
% 1.98/1.20  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => (((~v2_struct_0(A) & v2_pre_topc(A)) & ~v1_tdlat_3(A)) => ((~v2_struct_0(A) & ~v7_struct_0(A)) & v2_pre_topc(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_tex_1)).
% 1.98/1.20  tff(f_82, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 1.98/1.20  tff(f_32, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 1.98/1.20  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (((~v2_struct_0(A) & v2_pre_topc(A)) & ~v2_tdlat_3(A)) => ((~v2_struct_0(A) & ~v7_struct_0(A)) & v2_pre_topc(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_tex_1)).
% 1.98/1.20  tff(c_36, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 1.98/1.20  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 1.98/1.20  tff(c_32, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 1.98/1.20  tff(c_106, plain, (![A_27, B_28]: (~v2_struct_0(k1_tex_2(A_27, B_28)) | ~m1_subset_1(B_28, u1_struct_0(A_27)) | ~l1_pre_topc(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_96])).
% 1.98/1.20  tff(c_109, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_106])).
% 1.98/1.20  tff(c_112, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_109])).
% 1.98/1.20  tff(c_113, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_36, c_112])).
% 1.98/1.20  tff(c_49, plain, (![A_17, B_18]: (~v2_struct_0(k1_tex_2(A_17, B_18)) | ~m1_subset_1(B_18, u1_struct_0(A_17)) | ~l1_pre_topc(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_96])).
% 1.98/1.20  tff(c_52, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_49])).
% 1.98/1.20  tff(c_55, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_52])).
% 1.98/1.20  tff(c_56, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_36, c_55])).
% 1.98/1.20  tff(c_28, plain, (~v2_tdlat_3(k1_tex_2('#skF_1', '#skF_2')) | ~v1_tdlat_3(k1_tex_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 1.98/1.20  tff(c_38, plain, (~v1_tdlat_3(k1_tex_2('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_28])).
% 1.98/1.20  tff(c_30, plain, (v2_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 1.98/1.20  tff(c_57, plain, (![A_19, B_20]: (v7_struct_0(k1_tex_2(A_19, B_20)) | ~m1_subset_1(B_20, u1_struct_0(A_19)) | ~l1_pre_topc(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_96])).
% 1.98/1.20  tff(c_60, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_57])).
% 1.98/1.20  tff(c_63, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_60])).
% 1.98/1.20  tff(c_64, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_36, c_63])).
% 1.98/1.20  tff(c_6, plain, (![A_4]: (~v7_struct_0(A_4) | v1_tdlat_3(A_4) | ~v2_pre_topc(A_4) | v2_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.98/1.20  tff(c_70, plain, (v1_tdlat_3(k1_tex_2('#skF_1', '#skF_2')) | ~v2_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_64, c_6])).
% 1.98/1.20  tff(c_77, plain, (v1_tdlat_3(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_70])).
% 1.98/1.20  tff(c_78, plain, (~l1_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_38, c_77])).
% 1.98/1.20  tff(c_79, plain, (![A_21, B_22]: (m1_pre_topc(k1_tex_2(A_21, B_22), A_21) | ~m1_subset_1(B_22, u1_struct_0(A_21)) | ~l1_pre_topc(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.98/1.20  tff(c_81, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_79])).
% 1.98/1.20  tff(c_84, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_81])).
% 1.98/1.20  tff(c_85, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_36, c_84])).
% 1.98/1.20  tff(c_2, plain, (![B_3, A_1]: (l1_pre_topc(B_3) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.98/1.20  tff(c_88, plain, (l1_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_85, c_2])).
% 1.98/1.20  tff(c_91, plain, (l1_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_88])).
% 1.98/1.20  tff(c_93, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_91])).
% 1.98/1.20  tff(c_94, plain, (~v2_tdlat_3(k1_tex_2('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_28])).
% 1.98/1.20  tff(c_114, plain, (![A_29, B_30]: (v7_struct_0(k1_tex_2(A_29, B_30)) | ~m1_subset_1(B_30, u1_struct_0(A_29)) | ~l1_pre_topc(A_29) | v2_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_96])).
% 1.98/1.20  tff(c_117, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_114])).
% 1.98/1.20  tff(c_120, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_117])).
% 1.98/1.20  tff(c_121, plain, (v7_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_36, c_120])).
% 1.98/1.20  tff(c_12, plain, (![A_5]: (~v7_struct_0(A_5) | v2_tdlat_3(A_5) | ~v2_pre_topc(A_5) | v2_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.98/1.20  tff(c_127, plain, (v2_tdlat_3(k1_tex_2('#skF_1', '#skF_2')) | ~v2_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_121, c_12])).
% 1.98/1.20  tff(c_134, plain, (v2_tdlat_3(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_127])).
% 1.98/1.20  tff(c_135, plain, (~l1_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_113, c_94, c_134])).
% 1.98/1.20  tff(c_136, plain, (![A_31, B_32]: (m1_pre_topc(k1_tex_2(A_31, B_32), A_31) | ~m1_subset_1(B_32, u1_struct_0(A_31)) | ~l1_pre_topc(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.98/1.20  tff(c_138, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_136])).
% 1.98/1.20  tff(c_141, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_138])).
% 1.98/1.20  tff(c_142, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_36, c_141])).
% 1.98/1.20  tff(c_145, plain, (l1_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_142, c_2])).
% 1.98/1.20  tff(c_148, plain, (l1_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_145])).
% 1.98/1.20  tff(c_150, plain, $false, inference(negUnitSimplification, [status(thm)], [c_135, c_148])).
% 1.98/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.20  
% 1.98/1.20  Inference rules
% 1.98/1.20  ----------------------
% 1.98/1.20  #Ref     : 0
% 1.98/1.20  #Sup     : 14
% 1.98/1.20  #Fact    : 0
% 1.98/1.20  #Define  : 0
% 1.98/1.20  #Split   : 1
% 1.98/1.20  #Chain   : 0
% 1.98/1.20  #Close   : 0
% 1.98/1.20  
% 1.98/1.20  Ordering : KBO
% 1.98/1.20  
% 1.98/1.20  Simplification rules
% 1.98/1.20  ----------------------
% 1.98/1.20  #Subsume      : 2
% 1.98/1.20  #Demod        : 15
% 1.98/1.20  #Tautology    : 5
% 1.98/1.20  #SimpNegUnit  : 14
% 1.98/1.20  #BackRed      : 0
% 1.98/1.20  
% 1.98/1.20  #Partial instantiations: 0
% 1.98/1.20  #Strategies tried      : 1
% 1.98/1.20  
% 1.98/1.20  Timing (in seconds)
% 1.98/1.20  ----------------------
% 1.98/1.21  Preprocessing        : 0.28
% 1.98/1.21  Parsing              : 0.16
% 1.98/1.21  CNF conversion       : 0.02
% 1.98/1.21  Main loop            : 0.14
% 1.98/1.21  Inferencing          : 0.06
% 1.98/1.21  Reduction            : 0.04
% 1.98/1.21  Demodulation         : 0.03
% 1.98/1.21  BG Simplification    : 0.01
% 1.98/1.21  Subsumption          : 0.02
% 1.98/1.21  Abstraction          : 0.01
% 1.98/1.21  MUC search           : 0.00
% 1.98/1.21  Cooper               : 0.00
% 1.98/1.21  Total                : 0.46
% 1.98/1.21  Index Insertion      : 0.00
% 1.98/1.21  Index Deletion       : 0.00
% 1.98/1.21  Index Matching       : 0.00
% 1.98/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
