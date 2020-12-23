%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:58 EST 2020

% Result     : Theorem 6.04s
% Output     : CNFRefutation 6.41s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 912 expanded)
%              Number of leaves         :   31 ( 320 expanded)
%              Depth                    :   19
%              Number of atoms          :  325 (2660 expanded)
%              Number of equality atoms :   19 ( 313 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tops_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_tdlat_3 > v2_pre_topc > l1_pre_topc > k2_tarski > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_155,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                & v2_tdlat_3(A) )
             => v2_tdlat_3(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tex_2)).

tff(f_143,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_tdlat_3(A)
      <=> u1_pre_topc(A) = k2_tarski(k1_xboole_0,u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tdlat_3)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> r1_tarski(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( v1_tops_2(B,A)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C))))
                   => ( D = B
                     => v1_tops_2(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tops_2)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B))))
             => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_2)).

tff(f_137,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_tdlat_3(A)
       => v2_pre_topc(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).

tff(f_119,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_44,plain,(
    v2_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_40,plain,(
    ! [A_57] :
      ( k2_tarski(k1_xboole_0,u1_struct_0(A_57)) = u1_pre_topc(A_57)
      | ~ v2_tdlat_3(A_57)
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_42,plain,(
    ~ v2_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_26,plain,(
    ! [A_38] :
      ( m1_pre_topc(A_38,A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_118,plain,(
    ! [A_77,B_78] :
      ( m1_pre_topc(A_77,g1_pre_topc(u1_struct_0(B_78),u1_pre_topc(B_78)))
      | ~ m1_pre_topc(A_77,B_78)
      | ~ l1_pre_topc(B_78)
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_46,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_96,plain,(
    ! [B_71,A_72] :
      ( m1_pre_topc(B_71,A_72)
      | ~ m1_pre_topc(B_71,g1_pre_topc(u1_struct_0(A_72),u1_pre_topc(A_72)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_99,plain,(
    ! [B_71] :
      ( m1_pre_topc(B_71,'#skF_2')
      | ~ m1_pre_topc(B_71,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_96])).

tff(c_105,plain,(
    ! [B_71] :
      ( m1_pre_topc(B_71,'#skF_2')
      | ~ m1_pre_topc(B_71,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_99])).

tff(c_124,plain,(
    ! [A_77] :
      ( m1_pre_topc(A_77,'#skF_2')
      | ~ m1_pre_topc(A_77,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ l1_pre_topc(A_77) ) ),
    inference(resolution,[status(thm)],[c_118,c_105])).

tff(c_137,plain,(
    ! [A_77] :
      ( m1_pre_topc(A_77,'#skF_2')
      | ~ m1_pre_topc(A_77,'#skF_1')
      | ~ l1_pre_topc(A_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_124])).

tff(c_133,plain,(
    ! [A_77] :
      ( m1_pre_topc(A_77,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_pre_topc(A_77,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_118])).

tff(c_152,plain,(
    ! [A_80] :
      ( m1_pre_topc(A_80,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_pre_topc(A_80,'#skF_2')
      | ~ l1_pre_topc(A_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_133])).

tff(c_12,plain,(
    ! [B_9,A_7] :
      ( m1_pre_topc(B_9,A_7)
      | ~ m1_pre_topc(B_9,g1_pre_topc(u1_struct_0(A_7),u1_pre_topc(A_7)))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_160,plain,(
    ! [A_80] :
      ( m1_pre_topc(A_80,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_pre_topc(A_80,'#skF_2')
      | ~ l1_pre_topc(A_80) ) ),
    inference(resolution,[status(thm)],[c_152,c_12])).

tff(c_170,plain,(
    ! [A_81] :
      ( m1_pre_topc(A_81,'#skF_1')
      | ~ m1_pre_topc(A_81,'#skF_2')
      | ~ l1_pre_topc(A_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_160])).

tff(c_177,plain,
    ( m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_170])).

tff(c_181,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_177])).

tff(c_28,plain,(
    ! [B_41,A_39] :
      ( r1_tarski(u1_struct_0(B_41),u1_struct_0(A_39))
      | ~ m1_pre_topc(B_41,A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_92,plain,(
    ! [B_69,A_70] :
      ( r1_tarski(u1_struct_0(B_69),u1_struct_0(A_70))
      | ~ m1_pre_topc(B_69,A_70)
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_223,plain,(
    ! [B_85,A_86] :
      ( u1_struct_0(B_85) = u1_struct_0(A_86)
      | ~ r1_tarski(u1_struct_0(A_86),u1_struct_0(B_85))
      | ~ m1_pre_topc(B_85,A_86)
      | ~ l1_pre_topc(A_86) ) ),
    inference(resolution,[status(thm)],[c_92,c_2])).

tff(c_234,plain,(
    ! [B_87,A_88] :
      ( u1_struct_0(B_87) = u1_struct_0(A_88)
      | ~ m1_pre_topc(A_88,B_87)
      | ~ l1_pre_topc(B_87)
      | ~ m1_pre_topc(B_87,A_88)
      | ~ l1_pre_topc(A_88) ) ),
    inference(resolution,[status(thm)],[c_28,c_223])).

tff(c_238,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_181,c_234])).

tff(c_252,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50,c_238])).

tff(c_279,plain,(
    ~ m1_pre_topc('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_252])).

tff(c_282,plain,
    ( ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_137,c_279])).

tff(c_285,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_282])).

tff(c_288,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_285])).

tff(c_292,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_288])).

tff(c_293,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_38,plain,(
    ! [A_57] :
      ( v2_tdlat_3(A_57)
      | k2_tarski(k1_xboole_0,u1_struct_0(A_57)) != u1_pre_topc(A_57)
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_368,plain,
    ( v2_tdlat_3('#skF_2')
    | k2_tarski(k1_xboole_0,u1_struct_0('#skF_1')) != u1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_38])).

tff(c_390,plain,
    ( v2_tdlat_3('#skF_2')
    | k2_tarski(k1_xboole_0,u1_struct_0('#skF_1')) != u1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_368])).

tff(c_391,plain,(
    k2_tarski(k1_xboole_0,u1_struct_0('#skF_1')) != u1_pre_topc('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_390])).

tff(c_399,plain,
    ( u1_pre_topc('#skF_2') != u1_pre_topc('#skF_1')
    | ~ v2_tdlat_3('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_391])).

tff(c_401,plain,(
    u1_pre_topc('#skF_2') != u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_399])).

tff(c_10,plain,(
    ! [A_6] :
      ( m1_subset_1(u1_pre_topc(A_6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_6))))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_371,plain,
    ( m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_10])).

tff(c_393,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_371])).

tff(c_294,plain,(
    m1_pre_topc('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [B_37,A_35] :
      ( v1_tops_2(B_37,A_35)
      | ~ r1_tarski(B_37,u1_pre_topc(A_35))
      | ~ m1_subset_1(B_37,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_35))))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_341,plain,(
    ! [B_37] :
      ( v1_tops_2(B_37,'#skF_2')
      | ~ r1_tarski(B_37,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_37,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_22])).

tff(c_977,plain,(
    ! [B_120] :
      ( v1_tops_2(B_120,'#skF_2')
      | ~ r1_tarski(B_120,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_120,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_341])).

tff(c_984,plain,
    ( v1_tops_2(u1_pre_topc('#skF_2'),'#skF_2')
    | ~ r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_2')) ),
    inference(resolution,[status(thm)],[c_393,c_977])).

tff(c_994,plain,(
    v1_tops_2(u1_pre_topc('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_984])).

tff(c_404,plain,
    ( v1_tops_2(u1_pre_topc('#skF_2'),'#skF_1')
    | ~ r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_393,c_22])).

tff(c_410,plain,
    ( v1_tops_2(u1_pre_topc('#skF_2'),'#skF_1')
    | ~ r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_404])).

tff(c_426,plain,(
    ~ r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_410])).

tff(c_24,plain,(
    ! [B_37,A_35] :
      ( r1_tarski(B_37,u1_pre_topc(A_35))
      | ~ v1_tops_2(B_37,A_35)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_35))))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_407,plain,
    ( r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_1'))
    | ~ v1_tops_2(u1_pre_topc('#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_393,c_24])).

tff(c_413,plain,
    ( r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_1'))
    | ~ v1_tops_2(u1_pre_topc('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_407])).

tff(c_436,plain,(
    ~ v1_tops_2(u1_pre_topc('#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_426,c_413])).

tff(c_1000,plain,(
    ! [D_121,C_122,A_123] :
      ( v1_tops_2(D_121,C_122)
      | ~ m1_subset_1(D_121,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C_122))))
      | ~ v1_tops_2(D_121,A_123)
      | ~ m1_pre_topc(C_122,A_123)
      | ~ m1_subset_1(D_121,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_123))))
      | ~ l1_pre_topc(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1004,plain,(
    ! [A_123] :
      ( v1_tops_2(u1_pre_topc('#skF_2'),'#skF_1')
      | ~ v1_tops_2(u1_pre_topc('#skF_2'),A_123)
      | ~ m1_pre_topc('#skF_1',A_123)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_123))))
      | ~ l1_pre_topc(A_123) ) ),
    inference(resolution,[status(thm)],[c_393,c_1000])).

tff(c_1549,plain,(
    ! [A_150] :
      ( ~ v1_tops_2(u1_pre_topc('#skF_2'),A_150)
      | ~ m1_pre_topc('#skF_1',A_150)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_150))))
      | ~ l1_pre_topc(A_150) ) ),
    inference(negUnitSimplification,[status(thm)],[c_436,c_1004])).

tff(c_1566,plain,
    ( ~ v1_tops_2(u1_pre_topc('#skF_2'),'#skF_2')
    | ~ m1_pre_topc('#skF_1','#skF_2')
    | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_1549])).

tff(c_1583,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_393,c_294,c_994,c_1566])).

tff(c_1585,plain,(
    r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_410])).

tff(c_1587,plain,
    ( u1_pre_topc('#skF_2') = u1_pre_topc('#skF_1')
    | ~ r1_tarski(u1_pre_topc('#skF_1'),u1_pre_topc('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1585,c_2])).

tff(c_1590,plain,(
    ~ r1_tarski(u1_pre_topc('#skF_1'),u1_pre_topc('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_401,c_1587])).

tff(c_350,plain,(
    ! [B_37] :
      ( r1_tarski(B_37,u1_pre_topc('#skF_2'))
      | ~ v1_tops_2(B_37,'#skF_2')
      | ~ m1_subset_1(B_37,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_24])).

tff(c_2167,plain,(
    ! [B_177] :
      ( r1_tarski(B_177,u1_pre_topc('#skF_2'))
      | ~ v1_tops_2(B_177,'#skF_2')
      | ~ m1_subset_1(B_177,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_350])).

tff(c_2178,plain,
    ( r1_tarski(u1_pre_topc('#skF_1'),u1_pre_topc('#skF_2'))
    | ~ v1_tops_2(u1_pre_topc('#skF_1'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_2167])).

tff(c_2186,plain,
    ( r1_tarski(u1_pre_topc('#skF_1'),u1_pre_topc('#skF_2'))
    | ~ v1_tops_2(u1_pre_topc('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2178])).

tff(c_2187,plain,(
    ~ v1_tops_2(u1_pre_topc('#skF_1'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_1590,c_2186])).

tff(c_168,plain,(
    ! [A_80] :
      ( m1_pre_topc(A_80,'#skF_1')
      | ~ m1_pre_topc(A_80,'#skF_2')
      | ~ l1_pre_topc(A_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_160])).

tff(c_299,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_294,c_168])).

tff(c_310,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_299])).

tff(c_1591,plain,(
    ! [C_151,A_152,B_153] :
      ( m1_subset_1(C_151,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_152))))
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B_153))))
      | ~ m1_pre_topc(B_153,A_152)
      | ~ l1_pre_topc(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2224,plain,(
    ! [A_182,A_183] :
      ( m1_subset_1(u1_pre_topc(A_182),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_183))))
      | ~ m1_pre_topc(A_182,A_183)
      | ~ l1_pre_topc(A_183)
      | ~ l1_pre_topc(A_182) ) ),
    inference(resolution,[status(thm)],[c_10,c_1591])).

tff(c_2245,plain,(
    ! [A_182] :
      ( m1_subset_1(u1_pre_topc(A_182),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_pre_topc(A_182,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_182) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_2224])).

tff(c_2301,plain,(
    ! [A_186] :
      ( m1_subset_1(u1_pre_topc(A_186),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_pre_topc(A_186,'#skF_2')
      | ~ l1_pre_topc(A_186) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2245])).

tff(c_2314,plain,(
    ! [A_186] :
      ( v1_tops_2(u1_pre_topc(A_186),'#skF_1')
      | ~ r1_tarski(u1_pre_topc(A_186),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_pre_topc(A_186,'#skF_2')
      | ~ l1_pre_topc(A_186) ) ),
    inference(resolution,[status(thm)],[c_2301,c_22])).

tff(c_2503,plain,(
    ! [A_195] :
      ( v1_tops_2(u1_pre_topc(A_195),'#skF_1')
      | ~ r1_tarski(u1_pre_topc(A_195),u1_pre_topc('#skF_1'))
      | ~ m1_pre_topc(A_195,'#skF_2')
      | ~ l1_pre_topc(A_195) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2314])).

tff(c_2513,plain,
    ( v1_tops_2(u1_pre_topc('#skF_1'),'#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_2503])).

tff(c_2520,plain,(
    v1_tops_2(u1_pre_topc('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_294,c_2513])).

tff(c_54,plain,(
    ! [A_61] :
      ( v2_pre_topc(A_61)
      | ~ v2_tdlat_3(A_61)
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_57,plain,
    ( v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_54])).

tff(c_60,plain,(
    v2_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_57])).

tff(c_1760,plain,(
    ! [B_160,C_161,A_162] :
      ( m1_pre_topc(B_160,C_161)
      | ~ r1_tarski(u1_struct_0(B_160),u1_struct_0(C_161))
      | ~ m1_pre_topc(C_161,A_162)
      | ~ m1_pre_topc(B_160,A_162)
      | ~ l1_pre_topc(A_162)
      | ~ v2_pre_topc(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1778,plain,(
    ! [B_163,A_164] :
      ( m1_pre_topc(B_163,B_163)
      | ~ m1_pre_topc(B_163,A_164)
      | ~ l1_pre_topc(A_164)
      | ~ v2_pre_topc(A_164) ) ),
    inference(resolution,[status(thm)],[c_6,c_1760])).

tff(c_1786,plain,
    ( m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_181,c_1778])).

tff(c_1804,plain,(
    m1_pre_topc('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_1786])).

tff(c_2735,plain,(
    ! [C_207,A_208] :
      ( m1_subset_1(C_207,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_208))))
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_pre_topc('#skF_2',A_208)
      | ~ l1_pre_topc(A_208) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_1591])).

tff(c_2748,plain,(
    ! [A_208] :
      ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_208))))
      | ~ m1_pre_topc('#skF_2',A_208)
      | ~ l1_pre_topc(A_208)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_10,c_2735])).

tff(c_2800,plain,(
    ! [A_210] :
      ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_210))))
      | ~ m1_pre_topc('#skF_2',A_210)
      | ~ l1_pre_topc(A_210) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2748])).

tff(c_2824,plain,
    ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_2800])).

tff(c_2841,plain,(
    m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1804,c_2824])).

tff(c_18,plain,(
    ! [C_19,A_13,B_17] :
      ( m1_subset_1(C_19,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_13))))
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B_17))))
      | ~ m1_pre_topc(B_17,A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2913,plain,(
    ! [A_13] :
      ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_13))))
      | ~ m1_pre_topc('#skF_1',A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(resolution,[status(thm)],[c_2841,c_18])).

tff(c_20,plain,(
    ! [D_34,C_32,A_20] :
      ( v1_tops_2(D_34,C_32)
      | ~ m1_subset_1(D_34,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C_32))))
      | ~ v1_tops_2(D_34,A_20)
      | ~ m1_pre_topc(C_32,A_20)
      | ~ m1_subset_1(D_34,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_20))))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3575,plain,(
    ! [A_234,A_235,A_236] :
      ( v1_tops_2(u1_pre_topc(A_234),A_235)
      | ~ v1_tops_2(u1_pre_topc(A_234),A_236)
      | ~ m1_pre_topc(A_235,A_236)
      | ~ m1_subset_1(u1_pre_topc(A_234),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_236))))
      | ~ l1_pre_topc(A_236)
      | ~ m1_pre_topc(A_234,A_235)
      | ~ l1_pre_topc(A_235)
      | ~ l1_pre_topc(A_234) ) ),
    inference(resolution,[status(thm)],[c_2224,c_20])).

tff(c_3591,plain,(
    ! [A_234] :
      ( v1_tops_2(u1_pre_topc(A_234),'#skF_2')
      | ~ v1_tops_2(u1_pre_topc(A_234),'#skF_1')
      | ~ m1_subset_1(u1_pre_topc(A_234),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_pre_topc(A_234,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_234) ) ),
    inference(resolution,[status(thm)],[c_181,c_3575])).

tff(c_6004,plain,(
    ! [A_303] :
      ( v1_tops_2(u1_pre_topc(A_303),'#skF_2')
      | ~ v1_tops_2(u1_pre_topc(A_303),'#skF_1')
      | ~ m1_subset_1(u1_pre_topc(A_303),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_pre_topc(A_303,'#skF_2')
      | ~ l1_pre_topc(A_303) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50,c_3591])).

tff(c_6027,plain,
    ( v1_tops_2(u1_pre_topc('#skF_1'),'#skF_2')
    | ~ v1_tops_2(u1_pre_topc('#skF_1'),'#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_2')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2913,c_6004])).

tff(c_6075,plain,(
    v1_tops_2(u1_pre_topc('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_310,c_294,c_2520,c_6027])).

tff(c_6077,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2187,c_6075])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:30:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.04/2.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.04/2.23  
% 6.04/2.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.04/2.23  %$ v1_tops_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_tdlat_3 > v2_pre_topc > l1_pre_topc > k2_tarski > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 6.04/2.23  
% 6.04/2.23  %Foreground sorts:
% 6.04/2.23  
% 6.04/2.23  
% 6.04/2.23  %Background operators:
% 6.04/2.23  
% 6.04/2.23  
% 6.04/2.23  %Foreground operators:
% 6.04/2.23  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 6.04/2.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.04/2.23  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 6.04/2.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.04/2.23  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 6.04/2.23  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.04/2.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.04/2.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.04/2.23  tff('#skF_2', type, '#skF_2': $i).
% 6.04/2.23  tff('#skF_1', type, '#skF_1': $i).
% 6.04/2.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.04/2.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.04/2.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.04/2.23  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.04/2.23  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.04/2.23  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.04/2.23  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 6.04/2.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.04/2.23  
% 6.41/2.25  tff(f_155, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & v2_tdlat_3(A)) => v2_tdlat_3(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_tex_2)).
% 6.41/2.25  tff(f_143, axiom, (![A]: (l1_pre_topc(A) => (v2_tdlat_3(A) <=> (u1_pre_topc(A) = k2_tarski(k1_xboole_0, u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tdlat_3)).
% 6.41/2.25  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 6.41/2.25  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 6.41/2.25  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 6.41/2.25  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_borsuk_1)).
% 6.41/2.25  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.41/2.25  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 6.41/2.25  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> r1_tarski(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_tops_2)).
% 6.41/2.25  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_pre_topc(C, A) => (v1_tops_2(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C)))) => ((D = B) => v1_tops_2(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tops_2)).
% 6.41/2.25  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B)))) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tops_2)).
% 6.41/2.25  tff(f_137, axiom, (![A]: (l1_pre_topc(A) => (v2_tdlat_3(A) => v2_pre_topc(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tdlat_3)).
% 6.41/2.25  tff(f_119, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 6.41/2.25  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.41/2.25  tff(c_44, plain, (v2_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.41/2.25  tff(c_40, plain, (![A_57]: (k2_tarski(k1_xboole_0, u1_struct_0(A_57))=u1_pre_topc(A_57) | ~v2_tdlat_3(A_57) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.41/2.25  tff(c_42, plain, (~v2_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.41/2.25  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.41/2.25  tff(c_26, plain, (![A_38]: (m1_pre_topc(A_38, A_38) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.41/2.25  tff(c_118, plain, (![A_77, B_78]: (m1_pre_topc(A_77, g1_pre_topc(u1_struct_0(B_78), u1_pre_topc(B_78))) | ~m1_pre_topc(A_77, B_78) | ~l1_pre_topc(B_78) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.41/2.25  tff(c_46, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.41/2.25  tff(c_96, plain, (![B_71, A_72]: (m1_pre_topc(B_71, A_72) | ~m1_pre_topc(B_71, g1_pre_topc(u1_struct_0(A_72), u1_pre_topc(A_72))) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.41/2.25  tff(c_99, plain, (![B_71]: (m1_pre_topc(B_71, '#skF_2') | ~m1_pre_topc(B_71, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_96])).
% 6.41/2.25  tff(c_105, plain, (![B_71]: (m1_pre_topc(B_71, '#skF_2') | ~m1_pre_topc(B_71, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_99])).
% 6.41/2.25  tff(c_124, plain, (![A_77]: (m1_pre_topc(A_77, '#skF_2') | ~m1_pre_topc(A_77, '#skF_1') | ~l1_pre_topc('#skF_1') | ~l1_pre_topc(A_77))), inference(resolution, [status(thm)], [c_118, c_105])).
% 6.41/2.25  tff(c_137, plain, (![A_77]: (m1_pre_topc(A_77, '#skF_2') | ~m1_pre_topc(A_77, '#skF_1') | ~l1_pre_topc(A_77))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_124])).
% 6.41/2.25  tff(c_133, plain, (![A_77]: (m1_pre_topc(A_77, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_pre_topc(A_77, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_77))), inference(superposition, [status(thm), theory('equality')], [c_46, c_118])).
% 6.41/2.25  tff(c_152, plain, (![A_80]: (m1_pre_topc(A_80, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_pre_topc(A_80, '#skF_2') | ~l1_pre_topc(A_80))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_133])).
% 6.41/2.25  tff(c_12, plain, (![B_9, A_7]: (m1_pre_topc(B_9, A_7) | ~m1_pre_topc(B_9, g1_pre_topc(u1_struct_0(A_7), u1_pre_topc(A_7))) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.41/2.25  tff(c_160, plain, (![A_80]: (m1_pre_topc(A_80, '#skF_1') | ~l1_pre_topc('#skF_1') | ~m1_pre_topc(A_80, '#skF_2') | ~l1_pre_topc(A_80))), inference(resolution, [status(thm)], [c_152, c_12])).
% 6.41/2.25  tff(c_170, plain, (![A_81]: (m1_pre_topc(A_81, '#skF_1') | ~m1_pre_topc(A_81, '#skF_2') | ~l1_pre_topc(A_81))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_160])).
% 6.41/2.25  tff(c_177, plain, (m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_170])).
% 6.41/2.25  tff(c_181, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_177])).
% 6.41/2.25  tff(c_28, plain, (![B_41, A_39]: (r1_tarski(u1_struct_0(B_41), u1_struct_0(A_39)) | ~m1_pre_topc(B_41, A_39) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.41/2.25  tff(c_92, plain, (![B_69, A_70]: (r1_tarski(u1_struct_0(B_69), u1_struct_0(A_70)) | ~m1_pre_topc(B_69, A_70) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.41/2.25  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.41/2.25  tff(c_223, plain, (![B_85, A_86]: (u1_struct_0(B_85)=u1_struct_0(A_86) | ~r1_tarski(u1_struct_0(A_86), u1_struct_0(B_85)) | ~m1_pre_topc(B_85, A_86) | ~l1_pre_topc(A_86))), inference(resolution, [status(thm)], [c_92, c_2])).
% 6.41/2.25  tff(c_234, plain, (![B_87, A_88]: (u1_struct_0(B_87)=u1_struct_0(A_88) | ~m1_pre_topc(A_88, B_87) | ~l1_pre_topc(B_87) | ~m1_pre_topc(B_87, A_88) | ~l1_pre_topc(A_88))), inference(resolution, [status(thm)], [c_28, c_223])).
% 6.41/2.25  tff(c_238, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1') | ~m1_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_181, c_234])).
% 6.41/2.25  tff(c_252, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1') | ~m1_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50, c_238])).
% 6.41/2.25  tff(c_279, plain, (~m1_pre_topc('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_252])).
% 6.41/2.25  tff(c_282, plain, (~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_137, c_279])).
% 6.41/2.25  tff(c_285, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_282])).
% 6.41/2.25  tff(c_288, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_285])).
% 6.41/2.25  tff(c_292, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_288])).
% 6.41/2.25  tff(c_293, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_252])).
% 6.41/2.25  tff(c_38, plain, (![A_57]: (v2_tdlat_3(A_57) | k2_tarski(k1_xboole_0, u1_struct_0(A_57))!=u1_pre_topc(A_57) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.41/2.25  tff(c_368, plain, (v2_tdlat_3('#skF_2') | k2_tarski(k1_xboole_0, u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_293, c_38])).
% 6.41/2.25  tff(c_390, plain, (v2_tdlat_3('#skF_2') | k2_tarski(k1_xboole_0, u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_368])).
% 6.41/2.25  tff(c_391, plain, (k2_tarski(k1_xboole_0, u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_42, c_390])).
% 6.41/2.25  tff(c_399, plain, (u1_pre_topc('#skF_2')!=u1_pre_topc('#skF_1') | ~v2_tdlat_3('#skF_1') | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_40, c_391])).
% 6.41/2.25  tff(c_401, plain, (u1_pre_topc('#skF_2')!=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_44, c_399])).
% 6.41/2.25  tff(c_10, plain, (![A_6]: (m1_subset_1(u1_pre_topc(A_6), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_6)))) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.41/2.25  tff(c_371, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_293, c_10])).
% 6.41/2.25  tff(c_393, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_371])).
% 6.41/2.25  tff(c_294, plain, (m1_pre_topc('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_252])).
% 6.41/2.25  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.41/2.25  tff(c_22, plain, (![B_37, A_35]: (v1_tops_2(B_37, A_35) | ~r1_tarski(B_37, u1_pre_topc(A_35)) | ~m1_subset_1(B_37, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_35)))) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.41/2.25  tff(c_341, plain, (![B_37]: (v1_tops_2(B_37, '#skF_2') | ~r1_tarski(B_37, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_37, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_293, c_22])).
% 6.41/2.25  tff(c_977, plain, (![B_120]: (v1_tops_2(B_120, '#skF_2') | ~r1_tarski(B_120, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_120, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_341])).
% 6.41/2.25  tff(c_984, plain, (v1_tops_2(u1_pre_topc('#skF_2'), '#skF_2') | ~r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_393, c_977])).
% 6.41/2.25  tff(c_994, plain, (v1_tops_2(u1_pre_topc('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_984])).
% 6.41/2.25  tff(c_404, plain, (v1_tops_2(u1_pre_topc('#skF_2'), '#skF_1') | ~r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_393, c_22])).
% 6.41/2.25  tff(c_410, plain, (v1_tops_2(u1_pre_topc('#skF_2'), '#skF_1') | ~r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_404])).
% 6.41/2.25  tff(c_426, plain, (~r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_1'))), inference(splitLeft, [status(thm)], [c_410])).
% 6.41/2.25  tff(c_24, plain, (![B_37, A_35]: (r1_tarski(B_37, u1_pre_topc(A_35)) | ~v1_tops_2(B_37, A_35) | ~m1_subset_1(B_37, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_35)))) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.41/2.25  tff(c_407, plain, (r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_1')) | ~v1_tops_2(u1_pre_topc('#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_393, c_24])).
% 6.41/2.25  tff(c_413, plain, (r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_1')) | ~v1_tops_2(u1_pre_topc('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_407])).
% 6.41/2.25  tff(c_436, plain, (~v1_tops_2(u1_pre_topc('#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_426, c_413])).
% 6.41/2.25  tff(c_1000, plain, (![D_121, C_122, A_123]: (v1_tops_2(D_121, C_122) | ~m1_subset_1(D_121, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C_122)))) | ~v1_tops_2(D_121, A_123) | ~m1_pre_topc(C_122, A_123) | ~m1_subset_1(D_121, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_123)))) | ~l1_pre_topc(A_123))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.41/2.25  tff(c_1004, plain, (![A_123]: (v1_tops_2(u1_pre_topc('#skF_2'), '#skF_1') | ~v1_tops_2(u1_pre_topc('#skF_2'), A_123) | ~m1_pre_topc('#skF_1', A_123) | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_123)))) | ~l1_pre_topc(A_123))), inference(resolution, [status(thm)], [c_393, c_1000])).
% 6.41/2.25  tff(c_1549, plain, (![A_150]: (~v1_tops_2(u1_pre_topc('#skF_2'), A_150) | ~m1_pre_topc('#skF_1', A_150) | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_150)))) | ~l1_pre_topc(A_150))), inference(negUnitSimplification, [status(thm)], [c_436, c_1004])).
% 6.41/2.25  tff(c_1566, plain, (~v1_tops_2(u1_pre_topc('#skF_2'), '#skF_2') | ~m1_pre_topc('#skF_1', '#skF_2') | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_293, c_1549])).
% 6.41/2.25  tff(c_1583, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_393, c_294, c_994, c_1566])).
% 6.41/2.25  tff(c_1585, plain, (r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_1'))), inference(splitRight, [status(thm)], [c_410])).
% 6.41/2.25  tff(c_1587, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_1') | ~r1_tarski(u1_pre_topc('#skF_1'), u1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_1585, c_2])).
% 6.41/2.25  tff(c_1590, plain, (~r1_tarski(u1_pre_topc('#skF_1'), u1_pre_topc('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_401, c_1587])).
% 6.41/2.25  tff(c_350, plain, (![B_37]: (r1_tarski(B_37, u1_pre_topc('#skF_2')) | ~v1_tops_2(B_37, '#skF_2') | ~m1_subset_1(B_37, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_293, c_24])).
% 6.41/2.25  tff(c_2167, plain, (![B_177]: (r1_tarski(B_177, u1_pre_topc('#skF_2')) | ~v1_tops_2(B_177, '#skF_2') | ~m1_subset_1(B_177, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_350])).
% 6.41/2.25  tff(c_2178, plain, (r1_tarski(u1_pre_topc('#skF_1'), u1_pre_topc('#skF_2')) | ~v1_tops_2(u1_pre_topc('#skF_1'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_10, c_2167])).
% 6.41/2.25  tff(c_2186, plain, (r1_tarski(u1_pre_topc('#skF_1'), u1_pre_topc('#skF_2')) | ~v1_tops_2(u1_pre_topc('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2178])).
% 6.41/2.25  tff(c_2187, plain, (~v1_tops_2(u1_pre_topc('#skF_1'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_1590, c_2186])).
% 6.41/2.25  tff(c_168, plain, (![A_80]: (m1_pre_topc(A_80, '#skF_1') | ~m1_pre_topc(A_80, '#skF_2') | ~l1_pre_topc(A_80))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_160])).
% 6.41/2.25  tff(c_299, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_294, c_168])).
% 6.41/2.25  tff(c_310, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_299])).
% 6.41/2.25  tff(c_1591, plain, (![C_151, A_152, B_153]: (m1_subset_1(C_151, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_152)))) | ~m1_subset_1(C_151, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B_153)))) | ~m1_pre_topc(B_153, A_152) | ~l1_pre_topc(A_152))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.41/2.25  tff(c_2224, plain, (![A_182, A_183]: (m1_subset_1(u1_pre_topc(A_182), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_183)))) | ~m1_pre_topc(A_182, A_183) | ~l1_pre_topc(A_183) | ~l1_pre_topc(A_182))), inference(resolution, [status(thm)], [c_10, c_1591])).
% 6.41/2.25  tff(c_2245, plain, (![A_182]: (m1_subset_1(u1_pre_topc(A_182), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_pre_topc(A_182, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_182))), inference(superposition, [status(thm), theory('equality')], [c_293, c_2224])).
% 6.41/2.25  tff(c_2301, plain, (![A_186]: (m1_subset_1(u1_pre_topc(A_186), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_pre_topc(A_186, '#skF_2') | ~l1_pre_topc(A_186))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2245])).
% 6.41/2.25  tff(c_2314, plain, (![A_186]: (v1_tops_2(u1_pre_topc(A_186), '#skF_1') | ~r1_tarski(u1_pre_topc(A_186), u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1') | ~m1_pre_topc(A_186, '#skF_2') | ~l1_pre_topc(A_186))), inference(resolution, [status(thm)], [c_2301, c_22])).
% 6.41/2.25  tff(c_2503, plain, (![A_195]: (v1_tops_2(u1_pre_topc(A_195), '#skF_1') | ~r1_tarski(u1_pre_topc(A_195), u1_pre_topc('#skF_1')) | ~m1_pre_topc(A_195, '#skF_2') | ~l1_pre_topc(A_195))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2314])).
% 6.41/2.25  tff(c_2513, plain, (v1_tops_2(u1_pre_topc('#skF_1'), '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6, c_2503])).
% 6.41/2.25  tff(c_2520, plain, (v1_tops_2(u1_pre_topc('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_294, c_2513])).
% 6.41/2.25  tff(c_54, plain, (![A_61]: (v2_pre_topc(A_61) | ~v2_tdlat_3(A_61) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.41/2.25  tff(c_57, plain, (v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_54])).
% 6.41/2.25  tff(c_60, plain, (v2_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_57])).
% 6.41/2.25  tff(c_1760, plain, (![B_160, C_161, A_162]: (m1_pre_topc(B_160, C_161) | ~r1_tarski(u1_struct_0(B_160), u1_struct_0(C_161)) | ~m1_pre_topc(C_161, A_162) | ~m1_pre_topc(B_160, A_162) | ~l1_pre_topc(A_162) | ~v2_pre_topc(A_162))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.41/2.25  tff(c_1778, plain, (![B_163, A_164]: (m1_pre_topc(B_163, B_163) | ~m1_pre_topc(B_163, A_164) | ~l1_pre_topc(A_164) | ~v2_pre_topc(A_164))), inference(resolution, [status(thm)], [c_6, c_1760])).
% 6.41/2.25  tff(c_1786, plain, (m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_181, c_1778])).
% 6.41/2.25  tff(c_1804, plain, (m1_pre_topc('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_1786])).
% 6.41/2.25  tff(c_2735, plain, (![C_207, A_208]: (m1_subset_1(C_207, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_208)))) | ~m1_subset_1(C_207, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_pre_topc('#skF_2', A_208) | ~l1_pre_topc(A_208))), inference(superposition, [status(thm), theory('equality')], [c_293, c_1591])).
% 6.41/2.25  tff(c_2748, plain, (![A_208]: (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_208)))) | ~m1_pre_topc('#skF_2', A_208) | ~l1_pre_topc(A_208) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_2735])).
% 6.41/2.25  tff(c_2800, plain, (![A_210]: (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_210)))) | ~m1_pre_topc('#skF_2', A_210) | ~l1_pre_topc(A_210))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2748])).
% 6.41/2.25  tff(c_2824, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_293, c_2800])).
% 6.41/2.25  tff(c_2841, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1804, c_2824])).
% 6.41/2.25  tff(c_18, plain, (![C_19, A_13, B_17]: (m1_subset_1(C_19, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_13)))) | ~m1_subset_1(C_19, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B_17)))) | ~m1_pre_topc(B_17, A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.41/2.25  tff(c_2913, plain, (![A_13]: (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_13)))) | ~m1_pre_topc('#skF_1', A_13) | ~l1_pre_topc(A_13))), inference(resolution, [status(thm)], [c_2841, c_18])).
% 6.41/2.25  tff(c_20, plain, (![D_34, C_32, A_20]: (v1_tops_2(D_34, C_32) | ~m1_subset_1(D_34, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C_32)))) | ~v1_tops_2(D_34, A_20) | ~m1_pre_topc(C_32, A_20) | ~m1_subset_1(D_34, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_20)))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.41/2.25  tff(c_3575, plain, (![A_234, A_235, A_236]: (v1_tops_2(u1_pre_topc(A_234), A_235) | ~v1_tops_2(u1_pre_topc(A_234), A_236) | ~m1_pre_topc(A_235, A_236) | ~m1_subset_1(u1_pre_topc(A_234), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_236)))) | ~l1_pre_topc(A_236) | ~m1_pre_topc(A_234, A_235) | ~l1_pre_topc(A_235) | ~l1_pre_topc(A_234))), inference(resolution, [status(thm)], [c_2224, c_20])).
% 6.41/2.25  tff(c_3591, plain, (![A_234]: (v1_tops_2(u1_pre_topc(A_234), '#skF_2') | ~v1_tops_2(u1_pre_topc(A_234), '#skF_1') | ~m1_subset_1(u1_pre_topc(A_234), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1') | ~m1_pre_topc(A_234, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_234))), inference(resolution, [status(thm)], [c_181, c_3575])).
% 6.41/2.25  tff(c_6004, plain, (![A_303]: (v1_tops_2(u1_pre_topc(A_303), '#skF_2') | ~v1_tops_2(u1_pre_topc(A_303), '#skF_1') | ~m1_subset_1(u1_pre_topc(A_303), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_pre_topc(A_303, '#skF_2') | ~l1_pre_topc(A_303))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50, c_3591])).
% 6.41/2.25  tff(c_6027, plain, (v1_tops_2(u1_pre_topc('#skF_1'), '#skF_2') | ~v1_tops_2(u1_pre_topc('#skF_1'), '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_2') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2913, c_6004])).
% 6.41/2.25  tff(c_6075, plain, (v1_tops_2(u1_pre_topc('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_310, c_294, c_2520, c_6027])).
% 6.41/2.25  tff(c_6077, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2187, c_6075])).
% 6.41/2.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.41/2.25  
% 6.41/2.25  Inference rules
% 6.41/2.25  ----------------------
% 6.41/2.25  #Ref     : 0
% 6.41/2.25  #Sup     : 1133
% 6.41/2.25  #Fact    : 0
% 6.41/2.25  #Define  : 0
% 6.41/2.25  #Split   : 6
% 6.41/2.25  #Chain   : 0
% 6.41/2.25  #Close   : 0
% 6.41/2.25  
% 6.41/2.25  Ordering : KBO
% 6.41/2.25  
% 6.41/2.25  Simplification rules
% 6.41/2.25  ----------------------
% 6.41/2.25  #Subsume      : 321
% 6.41/2.25  #Demod        : 1762
% 6.41/2.25  #Tautology    : 431
% 6.41/2.25  #SimpNegUnit  : 46
% 6.41/2.25  #BackRed      : 1
% 6.41/2.25  
% 6.41/2.25  #Partial instantiations: 0
% 6.41/2.25  #Strategies tried      : 1
% 6.41/2.25  
% 6.41/2.25  Timing (in seconds)
% 6.41/2.25  ----------------------
% 6.41/2.26  Preprocessing        : 0.34
% 6.41/2.26  Parsing              : 0.19
% 6.41/2.26  CNF conversion       : 0.02
% 6.41/2.26  Main loop            : 1.14
% 6.41/2.26  Inferencing          : 0.34
% 6.41/2.26  Reduction            : 0.38
% 6.41/2.26  Demodulation         : 0.27
% 6.41/2.26  BG Simplification    : 0.04
% 6.41/2.26  Subsumption          : 0.32
% 6.41/2.26  Abstraction          : 0.05
% 6.41/2.26  MUC search           : 0.00
% 6.41/2.26  Cooper               : 0.00
% 6.41/2.26  Total                : 1.52
% 6.41/2.26  Index Insertion      : 0.00
% 6.41/2.26  Index Deletion       : 0.00
% 6.41/2.26  Index Matching       : 0.00
% 6.41/2.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
