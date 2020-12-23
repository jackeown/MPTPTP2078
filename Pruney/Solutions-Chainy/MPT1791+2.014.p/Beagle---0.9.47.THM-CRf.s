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
% DateTime   : Thu Dec  3 10:27:51 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 371 expanded)
%              Number of leaves         :   31 ( 141 expanded)
%              Depth                    :   15
%              Number of atoms          :  253 (1092 expanded)
%              Number of equality atoms :   40 ( 184 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_tmap_1,type,(
    k6_tmap_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_tmap_1,type,(
    k5_tmap_1: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_153,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k6_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_138,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(u1_pre_topc(A),k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_tmap_1)).

tff(f_126,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
            & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> r1_tarski(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_75,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_tops_2(B,A)
            & m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) )
        <=> ( v1_tops_2(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
            & m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_compts_1)).

tff(f_112,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,u1_pre_topc(A))
          <=> u1_pre_topc(A) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

tff(f_87,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k6_tmap_1(A,B) = g1_pre_topc(u1_struct_0(A),k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_tmap_1)).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_58,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_79,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_52,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != k6_tmap_1('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_97,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_52])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_44,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_105,plain,(
    ! [B_42,A_43] :
      ( v3_pre_topc(B_42,A_43)
      | ~ r2_hidden(B_42,u1_pre_topc(A_43))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_108,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_105])).

tff(c_111,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_108])).

tff(c_112,plain,(
    ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_111])).

tff(c_48,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_42,plain,(
    ! [A_26,B_28] :
      ( r1_tarski(u1_pre_topc(A_26),k5_tmap_1(A_26,B_28))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_718,plain,(
    ! [A_99,B_100] :
      ( u1_pre_topc(k6_tmap_1(A_99,B_100)) = k5_tmap_1(A_99,B_100)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99)
      | ~ v2_pre_topc(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_724,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_718])).

tff(c_729,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_724])).

tff(c_730,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_729])).

tff(c_227,plain,(
    ! [A_56,B_57] :
      ( u1_pre_topc(k6_tmap_1(A_56,B_57)) = k5_tmap_1(A_56,B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_233,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_227])).

tff(c_238,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_233])).

tff(c_239,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_238])).

tff(c_70,plain,(
    ! [A_37] :
      ( m1_subset_1(u1_pre_topc(A_37),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_37))))
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( l1_pre_topc(g1_pre_topc(A_6,B_7))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(k1_zfmisc_1(A_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_90,plain,(
    ! [A_39] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_39),u1_pre_topc(A_39)))
      | ~ l1_pre_topc(A_39) ) ),
    inference(resolution,[status(thm)],[c_70,c_12])).

tff(c_93,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_90])).

tff(c_95,plain,(
    l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_93])).

tff(c_127,plain,(
    ! [A_49,B_50] :
      ( u1_struct_0(k6_tmap_1(A_49,B_50)) = u1_struct_0(A_49)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49)
      | ~ v2_pre_topc(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_130,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_127])).

tff(c_133,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_130])).

tff(c_134,plain,(
    u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_133])).

tff(c_16,plain,(
    ! [A_8] :
      ( m1_subset_1(u1_pre_topc(A_8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_8))))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_159,plain,
    ( m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_16])).

tff(c_177,plain,(
    m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_159])).

tff(c_20,plain,(
    ! [B_11,A_9] :
      ( r1_tarski(B_11,u1_pre_topc(A_9))
      | ~ v1_tops_2(B_11,A_9)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_9))))
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_185,plain,
    ( r1_tarski(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),u1_pre_topc('#skF_1'))
    | ~ v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_177,c_20])).

tff(c_197,plain,
    ( r1_tarski(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),u1_pre_topc('#skF_1'))
    | ~ v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_185])).

tff(c_205,plain,(
    ~ v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_197])).

tff(c_244,plain,(
    ~ v1_tops_2(k5_tmap_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_205])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_113,plain,(
    ! [B_44,A_45] :
      ( v1_tops_2(B_44,A_45)
      | ~ r1_tarski(B_44,u1_pre_topc(A_45))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_45))))
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_116,plain,(
    ! [A_8] :
      ( v1_tops_2(u1_pre_topc(A_8),A_8)
      | ~ r1_tarski(u1_pre_topc(A_8),u1_pre_topc(A_8))
      | ~ l1_pre_topc(A_8) ) ),
    inference(resolution,[status(thm)],[c_16,c_113])).

tff(c_119,plain,(
    ! [A_8] :
      ( v1_tops_2(u1_pre_topc(A_8),A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_116])).

tff(c_255,plain,
    ( v1_tops_2(k5_tmap_1('#skF_1','#skF_2'),k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_119])).

tff(c_270,plain,(
    v1_tops_2(k5_tmap_1('#skF_1','#skF_2'),k6_tmap_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_255])).

tff(c_246,plain,(
    m1_subset_1(k5_tmap_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_177])).

tff(c_642,plain,(
    ! [B_93,A_94] :
      ( v1_tops_2(B_93,A_94)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_94),u1_pre_topc(A_94))))))
      | ~ v1_tops_2(B_93,g1_pre_topc(u1_struct_0(A_94),u1_pre_topc(A_94)))
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94)
      | v2_struct_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_658,plain,(
    ! [B_93] :
      ( v1_tops_2(B_93,'#skF_1')
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1','#skF_2')))))
      | ~ v1_tops_2(B_93,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_642])).

tff(c_670,plain,(
    ! [B_93] :
      ( v1_tops_2(B_93,'#skF_1')
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ v1_tops_2(B_93,k6_tmap_1('#skF_1','#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_79,c_134,c_658])).

tff(c_673,plain,(
    ! [B_95] :
      ( v1_tops_2(B_95,'#skF_1')
      | ~ m1_subset_1(B_95,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ v1_tops_2(B_95,k6_tmap_1('#skF_1','#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_670])).

tff(c_676,plain,
    ( v1_tops_2(k5_tmap_1('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_tops_2(k5_tmap_1('#skF_1','#skF_2'),k6_tmap_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_246,c_673])).

tff(c_687,plain,(
    v1_tops_2(k5_tmap_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_676])).

tff(c_689,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_244,c_687])).

tff(c_690,plain,(
    r1_tarski(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),u1_pre_topc('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_197])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_694,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = u1_pre_topc('#skF_1')
    | ~ r1_tarski(u1_pre_topc('#skF_1'),u1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_690,c_2])).

tff(c_698,plain,(
    ~ r1_tarski(u1_pre_topc('#skF_1'),u1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_694])).

tff(c_733,plain,(
    ~ r1_tarski(u1_pre_topc('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_730,c_698])).

tff(c_774,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_733])).

tff(c_777,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_774])).

tff(c_779,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_777])).

tff(c_780,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = u1_pre_topc('#skF_1') ),
    inference(splitRight,[status(thm)],[c_694])).

tff(c_820,plain,(
    ! [A_101,B_102] :
      ( u1_pre_topc(k6_tmap_1(A_101,B_102)) = k5_tmap_1(A_101,B_102)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101)
      | ~ v2_pre_topc(A_101)
      | v2_struct_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_826,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_820])).

tff(c_831,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_780,c_826])).

tff(c_832,plain,(
    k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_831])).

tff(c_994,plain,(
    ! [B_115,A_116] :
      ( r2_hidden(B_115,u1_pre_topc(A_116))
      | k5_tmap_1(A_116,B_115) != u1_pre_topc(A_116)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116)
      | ~ v2_pre_topc(A_116)
      | v2_struct_0(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1000,plain,
    ( r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | k5_tmap_1('#skF_1','#skF_2') != u1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_994])).

tff(c_1005,plain,
    ( r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_832,c_1000])).

tff(c_1007,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_112,c_1005])).

tff(c_1009,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != k6_tmap_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1008,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1014,plain,(
    ! [B_119,A_120] :
      ( r2_hidden(B_119,u1_pre_topc(A_120))
      | ~ v3_pre_topc(B_119,A_120)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_pre_topc(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1017,plain,
    ( r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_1014])).

tff(c_1020,plain,(
    r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1008,c_1017])).

tff(c_1449,plain,(
    ! [A_170,B_171] :
      ( k5_tmap_1(A_170,B_171) = u1_pre_topc(A_170)
      | ~ r2_hidden(B_171,u1_pre_topc(A_170))
      | ~ m1_subset_1(B_171,k1_zfmisc_1(u1_struct_0(A_170)))
      | ~ l1_pre_topc(A_170)
      | ~ v2_pre_topc(A_170)
      | v2_struct_0(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1455,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_1449])).

tff(c_1460,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1020,c_1455])).

tff(c_1461,plain,(
    k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1460])).

tff(c_1419,plain,(
    ! [A_168,B_169] :
      ( g1_pre_topc(u1_struct_0(A_168),k5_tmap_1(A_168,B_169)) = k6_tmap_1(A_168,B_169)
      | ~ m1_subset_1(B_169,k1_zfmisc_1(u1_struct_0(A_168)))
      | ~ l1_pre_topc(A_168)
      | ~ v2_pre_topc(A_168)
      | v2_struct_0(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1423,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_1419])).

tff(c_1428,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1423])).

tff(c_1429,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1428])).

tff(c_1463,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1461,c_1429])).

tff(c_1473,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1009,c_1463])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:32:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.48/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.60  
% 3.48/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.61  %$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1
% 3.48/1.61  
% 3.48/1.61  %Foreground sorts:
% 3.48/1.61  
% 3.48/1.61  
% 3.48/1.61  %Background operators:
% 3.48/1.61  
% 3.48/1.61  
% 3.48/1.61  %Foreground operators:
% 3.48/1.61  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.48/1.61  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.48/1.61  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.48/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.48/1.61  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.48/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.48/1.61  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 3.48/1.61  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.48/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.48/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.48/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.48/1.61  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.48/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.48/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.48/1.61  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 3.48/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.48/1.61  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.48/1.61  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 3.48/1.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.48/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.48/1.61  
% 3.48/1.63  tff(f_153, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k6_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_tmap_1)).
% 3.48/1.63  tff(f_40, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 3.48/1.63  tff(f_138, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(u1_pre_topc(A), k5_tmap_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_tmap_1)).
% 3.48/1.63  tff(f_126, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_tmap_1)).
% 3.48/1.63  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 3.48/1.63  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v1_pre_topc(g1_pre_topc(A, B)) & l1_pre_topc(g1_pre_topc(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 3.48/1.63  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> r1_tarski(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_tops_2)).
% 3.48/1.63  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.48/1.63  tff(f_75, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_tops_2(B, A) & m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))) <=> (v1_tops_2(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_compts_1)).
% 3.48/1.63  tff(f_112, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) <=> (u1_pre_topc(A) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tmap_1)).
% 3.48/1.63  tff(f_87, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k6_tmap_1(A, B) = g1_pre_topc(u1_struct_0(A), k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_tmap_1)).
% 3.48/1.63  tff(c_50, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.48/1.63  tff(c_58, plain, (v3_pre_topc('#skF_2', '#skF_1') | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.48/1.63  tff(c_79, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_58])).
% 3.48/1.63  tff(c_52, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=k6_tmap_1('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.48/1.63  tff(c_97, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_52])).
% 3.48/1.63  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.48/1.63  tff(c_44, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.48/1.63  tff(c_105, plain, (![B_42, A_43]: (v3_pre_topc(B_42, A_43) | ~r2_hidden(B_42, u1_pre_topc(A_43)) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.48/1.63  tff(c_108, plain, (v3_pre_topc('#skF_2', '#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_105])).
% 3.48/1.63  tff(c_111, plain, (v3_pre_topc('#skF_2', '#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_108])).
% 3.48/1.63  tff(c_112, plain, (~r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_97, c_111])).
% 3.48/1.63  tff(c_48, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.48/1.63  tff(c_42, plain, (![A_26, B_28]: (r1_tarski(u1_pre_topc(A_26), k5_tmap_1(A_26, B_28)) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.48/1.63  tff(c_718, plain, (![A_99, B_100]: (u1_pre_topc(k6_tmap_1(A_99, B_100))=k5_tmap_1(A_99, B_100) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99) | ~v2_pre_topc(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.48/1.63  tff(c_724, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_718])).
% 3.48/1.63  tff(c_729, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_724])).
% 3.48/1.63  tff(c_730, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_729])).
% 3.48/1.63  tff(c_227, plain, (![A_56, B_57]: (u1_pre_topc(k6_tmap_1(A_56, B_57))=k5_tmap_1(A_56, B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56) | ~v2_pre_topc(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.48/1.63  tff(c_233, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_227])).
% 3.48/1.63  tff(c_238, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_233])).
% 3.48/1.63  tff(c_239, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_238])).
% 3.48/1.63  tff(c_70, plain, (![A_37]: (m1_subset_1(u1_pre_topc(A_37), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_37)))) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.48/1.63  tff(c_12, plain, (![A_6, B_7]: (l1_pre_topc(g1_pre_topc(A_6, B_7)) | ~m1_subset_1(B_7, k1_zfmisc_1(k1_zfmisc_1(A_6))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.48/1.63  tff(c_90, plain, (![A_39]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_39), u1_pre_topc(A_39))) | ~l1_pre_topc(A_39))), inference(resolution, [status(thm)], [c_70, c_12])).
% 3.48/1.63  tff(c_93, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_79, c_90])).
% 3.48/1.63  tff(c_95, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_93])).
% 3.48/1.63  tff(c_127, plain, (![A_49, B_50]: (u1_struct_0(k6_tmap_1(A_49, B_50))=u1_struct_0(A_49) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_pre_topc(A_49) | ~v2_pre_topc(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.48/1.63  tff(c_130, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_127])).
% 3.48/1.63  tff(c_133, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_130])).
% 3.48/1.63  tff(c_134, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_133])).
% 3.48/1.63  tff(c_16, plain, (![A_8]: (m1_subset_1(u1_pre_topc(A_8), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_8)))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.48/1.63  tff(c_159, plain, (m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_134, c_16])).
% 3.48/1.63  tff(c_177, plain, (m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_159])).
% 3.48/1.63  tff(c_20, plain, (![B_11, A_9]: (r1_tarski(B_11, u1_pre_topc(A_9)) | ~v1_tops_2(B_11, A_9) | ~m1_subset_1(B_11, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_9)))) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.48/1.63  tff(c_185, plain, (r1_tarski(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), u1_pre_topc('#skF_1')) | ~v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_177, c_20])).
% 3.48/1.63  tff(c_197, plain, (r1_tarski(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), u1_pre_topc('#skF_1')) | ~v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_185])).
% 3.48/1.63  tff(c_205, plain, (~v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), '#skF_1')), inference(splitLeft, [status(thm)], [c_197])).
% 3.48/1.63  tff(c_244, plain, (~v1_tops_2(k5_tmap_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_239, c_205])).
% 3.48/1.63  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.48/1.63  tff(c_113, plain, (![B_44, A_45]: (v1_tops_2(B_44, A_45) | ~r1_tarski(B_44, u1_pre_topc(A_45)) | ~m1_subset_1(B_44, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_45)))) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.48/1.63  tff(c_116, plain, (![A_8]: (v1_tops_2(u1_pre_topc(A_8), A_8) | ~r1_tarski(u1_pre_topc(A_8), u1_pre_topc(A_8)) | ~l1_pre_topc(A_8))), inference(resolution, [status(thm)], [c_16, c_113])).
% 3.48/1.63  tff(c_119, plain, (![A_8]: (v1_tops_2(u1_pre_topc(A_8), A_8) | ~l1_pre_topc(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_116])).
% 3.48/1.63  tff(c_255, plain, (v1_tops_2(k5_tmap_1('#skF_1', '#skF_2'), k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_239, c_119])).
% 3.48/1.63  tff(c_270, plain, (v1_tops_2(k5_tmap_1('#skF_1', '#skF_2'), k6_tmap_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_255])).
% 3.48/1.63  tff(c_246, plain, (m1_subset_1(k5_tmap_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_239, c_177])).
% 3.48/1.63  tff(c_642, plain, (![B_93, A_94]: (v1_tops_2(B_93, A_94) | ~m1_subset_1(B_93, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_94), u1_pre_topc(A_94)))))) | ~v1_tops_2(B_93, g1_pre_topc(u1_struct_0(A_94), u1_pre_topc(A_94))) | ~l1_pre_topc(A_94) | ~v2_pre_topc(A_94) | v2_struct_0(A_94))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.48/1.63  tff(c_658, plain, (![B_93]: (v1_tops_2(B_93, '#skF_1') | ~m1_subset_1(B_93, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))))) | ~v1_tops_2(B_93, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_79, c_642])).
% 3.48/1.63  tff(c_670, plain, (![B_93]: (v1_tops_2(B_93, '#skF_1') | ~m1_subset_1(B_93, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~v1_tops_2(B_93, k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_79, c_134, c_658])).
% 3.48/1.63  tff(c_673, plain, (![B_95]: (v1_tops_2(B_95, '#skF_1') | ~m1_subset_1(B_95, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~v1_tops_2(B_95, k6_tmap_1('#skF_1', '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_670])).
% 3.48/1.63  tff(c_676, plain, (v1_tops_2(k5_tmap_1('#skF_1', '#skF_2'), '#skF_1') | ~v1_tops_2(k5_tmap_1('#skF_1', '#skF_2'), k6_tmap_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_246, c_673])).
% 3.48/1.63  tff(c_687, plain, (v1_tops_2(k5_tmap_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_270, c_676])).
% 3.48/1.63  tff(c_689, plain, $false, inference(negUnitSimplification, [status(thm)], [c_244, c_687])).
% 3.48/1.63  tff(c_690, plain, (r1_tarski(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), u1_pre_topc('#skF_1'))), inference(splitRight, [status(thm)], [c_197])).
% 3.48/1.63  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.48/1.63  tff(c_694, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=u1_pre_topc('#skF_1') | ~r1_tarski(u1_pre_topc('#skF_1'), u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_690, c_2])).
% 3.48/1.63  tff(c_698, plain, (~r1_tarski(u1_pre_topc('#skF_1'), u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_694])).
% 3.48/1.63  tff(c_733, plain, (~r1_tarski(u1_pre_topc('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_730, c_698])).
% 3.48/1.63  tff(c_774, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_733])).
% 3.48/1.63  tff(c_777, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_774])).
% 3.48/1.63  tff(c_779, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_777])).
% 3.48/1.63  tff(c_780, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=u1_pre_topc('#skF_1')), inference(splitRight, [status(thm)], [c_694])).
% 3.48/1.63  tff(c_820, plain, (![A_101, B_102]: (u1_pre_topc(k6_tmap_1(A_101, B_102))=k5_tmap_1(A_101, B_102) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101) | ~v2_pre_topc(A_101) | v2_struct_0(A_101))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.48/1.63  tff(c_826, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_820])).
% 3.48/1.63  tff(c_831, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_780, c_826])).
% 3.48/1.63  tff(c_832, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_831])).
% 3.48/1.63  tff(c_994, plain, (![B_115, A_116]: (r2_hidden(B_115, u1_pre_topc(A_116)) | k5_tmap_1(A_116, B_115)!=u1_pre_topc(A_116) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116) | ~v2_pre_topc(A_116) | v2_struct_0(A_116))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.48/1.63  tff(c_1000, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | k5_tmap_1('#skF_1', '#skF_2')!=u1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_994])).
% 3.48/1.63  tff(c_1005, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_832, c_1000])).
% 3.48/1.63  tff(c_1007, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_112, c_1005])).
% 3.48/1.63  tff(c_1009, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=k6_tmap_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_58])).
% 3.48/1.63  tff(c_1008, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_58])).
% 3.48/1.63  tff(c_1014, plain, (![B_119, A_120]: (r2_hidden(B_119, u1_pre_topc(A_120)) | ~v3_pre_topc(B_119, A_120) | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0(A_120))) | ~l1_pre_topc(A_120))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.48/1.63  tff(c_1017, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~v3_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_1014])).
% 3.48/1.63  tff(c_1020, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1008, c_1017])).
% 3.48/1.63  tff(c_1449, plain, (![A_170, B_171]: (k5_tmap_1(A_170, B_171)=u1_pre_topc(A_170) | ~r2_hidden(B_171, u1_pre_topc(A_170)) | ~m1_subset_1(B_171, k1_zfmisc_1(u1_struct_0(A_170))) | ~l1_pre_topc(A_170) | ~v2_pre_topc(A_170) | v2_struct_0(A_170))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.48/1.63  tff(c_1455, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_1449])).
% 3.48/1.63  tff(c_1460, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1020, c_1455])).
% 3.48/1.63  tff(c_1461, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_1460])).
% 3.48/1.63  tff(c_1419, plain, (![A_168, B_169]: (g1_pre_topc(u1_struct_0(A_168), k5_tmap_1(A_168, B_169))=k6_tmap_1(A_168, B_169) | ~m1_subset_1(B_169, k1_zfmisc_1(u1_struct_0(A_168))) | ~l1_pre_topc(A_168) | ~v2_pre_topc(A_168) | v2_struct_0(A_168))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.48/1.63  tff(c_1423, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_1419])).
% 3.48/1.63  tff(c_1428, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1423])).
% 3.48/1.63  tff(c_1429, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_1428])).
% 3.48/1.63  tff(c_1463, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1461, c_1429])).
% 3.48/1.63  tff(c_1473, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1009, c_1463])).
% 3.48/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.63  
% 3.48/1.63  Inference rules
% 3.48/1.63  ----------------------
% 3.48/1.63  #Ref     : 0
% 3.48/1.63  #Sup     : 248
% 3.48/1.63  #Fact    : 0
% 3.48/1.63  #Define  : 0
% 3.48/1.63  #Split   : 9
% 3.48/1.63  #Chain   : 0
% 3.48/1.63  #Close   : 0
% 3.48/1.63  
% 3.48/1.63  Ordering : KBO
% 3.48/1.63  
% 3.48/1.63  Simplification rules
% 3.48/1.63  ----------------------
% 3.48/1.63  #Subsume      : 41
% 3.48/1.63  #Demod        : 436
% 3.48/1.63  #Tautology    : 93
% 3.48/1.63  #SimpNegUnit  : 52
% 3.48/1.63  #BackRed      : 51
% 3.48/1.63  
% 3.48/1.63  #Partial instantiations: 0
% 3.48/1.63  #Strategies tried      : 1
% 3.48/1.63  
% 3.48/1.63  Timing (in seconds)
% 3.48/1.63  ----------------------
% 3.91/1.63  Preprocessing        : 0.35
% 3.91/1.63  Parsing              : 0.18
% 3.91/1.63  CNF conversion       : 0.02
% 3.91/1.63  Main loop            : 0.50
% 3.91/1.63  Inferencing          : 0.18
% 3.91/1.63  Reduction            : 0.18
% 3.91/1.63  Demodulation         : 0.13
% 3.91/1.63  BG Simplification    : 0.02
% 3.91/1.63  Subsumption          : 0.09
% 3.91/1.63  Abstraction          : 0.03
% 3.91/1.63  MUC search           : 0.00
% 3.91/1.63  Cooper               : 0.00
% 3.91/1.63  Total                : 0.89
% 3.91/1.63  Index Insertion      : 0.00
% 3.91/1.63  Index Deletion       : 0.00
% 3.91/1.63  Index Matching       : 0.00
% 3.91/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
