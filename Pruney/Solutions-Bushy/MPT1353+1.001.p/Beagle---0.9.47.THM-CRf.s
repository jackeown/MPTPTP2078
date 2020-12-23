%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1353+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:51 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 133 expanded)
%              Number of leaves         :   21 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :  143 ( 322 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

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

tff(f_70,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ( v1_tops_2(B,A)
            <=> r1_tarski(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tops_2)).

tff(f_38,axiom,(
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

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(c_26,plain,
    ( ~ r1_tarski('#skF_4',u1_pre_topc('#skF_3'))
    | ~ v1_tops_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_33,plain,(
    ~ v1_tops_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_24,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_32,plain,
    ( v1_tops_2('#skF_4','#skF_3')
    | r1_tarski('#skF_4',u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_34,plain,(
    r1_tarski('#skF_4',u1_pre_topc('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_32])).

tff(c_203,plain,(
    ! [A_70,B_71] :
      ( r2_hidden('#skF_1'(A_70,B_71),B_71)
      | v1_tops_2(B_71,A_70)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_70))))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_205,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4')
    | v1_tops_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_203])).

tff(c_208,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4')
    | v1_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_205])).

tff(c_209,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_208])).

tff(c_10,plain,(
    ! [C_15,B_12,A_11] :
      ( r2_hidden(C_15,B_12)
      | ~ r2_hidden(C_15,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_219,plain,(
    ! [B_72] :
      ( r2_hidden('#skF_1'('#skF_3','#skF_4'),B_72)
      | ~ r1_tarski('#skF_4',B_72) ) ),
    inference(resolution,[status(thm)],[c_209,c_10])).

tff(c_47,plain,(
    ! [A_31,C_32,B_33] :
      ( m1_subset_1(A_31,C_32)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(C_32))
      | ~ r2_hidden(A_31,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_50,plain,(
    ! [A_31] :
      ( m1_subset_1(A_31,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(A_31,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22,c_47])).

tff(c_79,plain,(
    ! [B_44,A_45] :
      ( v3_pre_topc(B_44,A_45)
      | ~ r2_hidden(B_44,u1_pre_topc(A_45))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_82,plain,(
    ! [A_31] :
      ( v3_pre_topc(A_31,'#skF_3')
      | ~ r2_hidden(A_31,u1_pre_topc('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ r2_hidden(A_31,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_50,c_79])).

tff(c_85,plain,(
    ! [A_31] :
      ( v3_pre_topc(A_31,'#skF_3')
      | ~ r2_hidden(A_31,u1_pre_topc('#skF_3'))
      | ~ r2_hidden(A_31,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_82])).

tff(c_226,plain,
    ( v3_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | ~ r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4')
    | ~ r1_tarski('#skF_4',u1_pre_topc('#skF_3')) ),
    inference(resolution,[status(thm)],[c_219,c_85])).

tff(c_236,plain,(
    v3_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_209,c_226])).

tff(c_4,plain,(
    ! [A_1,B_7] :
      ( ~ v3_pre_topc('#skF_1'(A_1,B_7),A_1)
      | v1_tops_2(B_7,A_1)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_240,plain,
    ( v1_tops_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_236,c_4])).

tff(c_243,plain,(
    v1_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_240])).

tff(c_245,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_243])).

tff(c_246,plain,(
    ~ r1_tarski('#skF_4',u1_pre_topc('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_251,plain,(
    ! [A_75,B_76] :
      ( r2_hidden('#skF_2'(A_75,B_76),A_75)
      | r1_tarski(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( ~ r2_hidden('#skF_2'(A_11,B_12),B_12)
      | r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_256,plain,(
    ! [A_75] : r1_tarski(A_75,A_75) ),
    inference(resolution,[status(thm)],[c_251,c_12])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_2'(A_11,B_12),A_11)
      | r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_258,plain,(
    ! [C_78,B_79,A_80] :
      ( r2_hidden(C_78,B_79)
      | ~ r2_hidden(C_78,A_80)
      | ~ r1_tarski(A_80,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_261,plain,(
    ! [A_11,B_12,B_79] :
      ( r2_hidden('#skF_2'(A_11,B_12),B_79)
      | ~ r1_tarski(A_11,B_79)
      | r1_tarski(A_11,B_12) ) ),
    inference(resolution,[status(thm)],[c_14,c_258])).

tff(c_247,plain,(
    v1_tops_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_262,plain,(
    ! [A_81,C_82,B_83] :
      ( m1_subset_1(A_81,C_82)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(C_82))
      | ~ r2_hidden(A_81,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_265,plain,(
    ! [A_81] :
      ( m1_subset_1(A_81,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(A_81,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22,c_262])).

tff(c_395,plain,(
    ! [C_125,A_126,B_127] :
      ( v3_pre_topc(C_125,A_126)
      | ~ r2_hidden(C_125,B_127)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ v1_tops_2(B_127,A_126)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_126))))
      | ~ l1_pre_topc(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_434,plain,(
    ! [A_146,B_147,A_148] :
      ( v3_pre_topc('#skF_2'(A_146,B_147),A_148)
      | ~ m1_subset_1('#skF_2'(A_146,B_147),k1_zfmisc_1(u1_struct_0(A_148)))
      | ~ v1_tops_2(A_146,A_148)
      | ~ m1_subset_1(A_146,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_148))))
      | ~ l1_pre_topc(A_148)
      | r1_tarski(A_146,B_147) ) ),
    inference(resolution,[status(thm)],[c_14,c_395])).

tff(c_438,plain,(
    ! [A_146,B_147] :
      ( v3_pre_topc('#skF_2'(A_146,B_147),'#skF_3')
      | ~ v1_tops_2(A_146,'#skF_3')
      | ~ m1_subset_1(A_146,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
      | ~ l1_pre_topc('#skF_3')
      | r1_tarski(A_146,B_147)
      | ~ r2_hidden('#skF_2'(A_146,B_147),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_265,c_434])).

tff(c_442,plain,(
    ! [A_149,B_150] :
      ( v3_pre_topc('#skF_2'(A_149,B_150),'#skF_3')
      | ~ v1_tops_2(A_149,'#skF_3')
      | ~ m1_subset_1(A_149,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
      | r1_tarski(A_149,B_150)
      | ~ r2_hidden('#skF_2'(A_149,B_150),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_438])).

tff(c_444,plain,(
    ! [B_150] :
      ( v3_pre_topc('#skF_2'('#skF_4',B_150),'#skF_3')
      | ~ v1_tops_2('#skF_4','#skF_3')
      | r1_tarski('#skF_4',B_150)
      | ~ r2_hidden('#skF_2'('#skF_4',B_150),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22,c_442])).

tff(c_448,plain,(
    ! [B_151] :
      ( v3_pre_topc('#skF_2'('#skF_4',B_151),'#skF_3')
      | r1_tarski('#skF_4',B_151)
      | ~ r2_hidden('#skF_2'('#skF_4',B_151),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_444])).

tff(c_314,plain,(
    ! [B_98,A_99] :
      ( r2_hidden(B_98,u1_pre_topc(A_99))
      | ~ v3_pre_topc(B_98,A_99)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_317,plain,(
    ! [A_81] :
      ( r2_hidden(A_81,u1_pre_topc('#skF_3'))
      | ~ v3_pre_topc(A_81,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ r2_hidden(A_81,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_265,c_314])).

tff(c_321,plain,(
    ! [A_100] :
      ( r2_hidden(A_100,u1_pre_topc('#skF_3'))
      | ~ v3_pre_topc(A_100,'#skF_3')
      | ~ r2_hidden(A_100,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_317])).

tff(c_336,plain,(
    ! [A_11] :
      ( r1_tarski(A_11,u1_pre_topc('#skF_3'))
      | ~ v3_pre_topc('#skF_2'(A_11,u1_pre_topc('#skF_3')),'#skF_3')
      | ~ r2_hidden('#skF_2'(A_11,u1_pre_topc('#skF_3')),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_321,c_12])).

tff(c_452,plain,
    ( r1_tarski('#skF_4',u1_pre_topc('#skF_3'))
    | ~ r2_hidden('#skF_2'('#skF_4',u1_pre_topc('#skF_3')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_448,c_336])).

tff(c_455,plain,(
    ~ r2_hidden('#skF_2'('#skF_4',u1_pre_topc('#skF_3')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_246,c_246,c_452])).

tff(c_465,plain,
    ( ~ r1_tarski('#skF_4','#skF_4')
    | r1_tarski('#skF_4',u1_pre_topc('#skF_3')) ),
    inference(resolution,[status(thm)],[c_261,c_455])).

tff(c_471,plain,(
    r1_tarski('#skF_4',u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_465])).

tff(c_473,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_246,c_471])).

%------------------------------------------------------------------------------
