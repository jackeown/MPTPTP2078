%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:51 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 588 expanded)
%              Number of leaves         :   31 ( 221 expanded)
%              Depth                    :   15
%              Number of atoms          :  342 (1867 expanded)
%              Number of equality atoms :   52 ( 284 expanded)
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

tff(f_151,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k6_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tmap_1)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_136,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(u1_pre_topc(A),k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_tmap_1)).

tff(f_124,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
            & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> r1_tarski(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tops_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_69,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_tops_2(B,A)
            & m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) )
        <=> ( v1_tops_2(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
            & m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_compts_1)).

tff(f_110,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,u1_pre_topc(A))
          <=> u1_pre_topc(A) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tmap_1)).

tff(f_81,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k6_tmap_1(A,B) = g1_pre_topc(u1_struct_0(A),k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_tmap_1)).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_58,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_69,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_52,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != k6_tmap_1('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_75,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_52])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_44,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_76,plain,(
    ! [B_32,A_33] :
      ( v3_pre_topc(B_32,A_33)
      | ~ r2_hidden(B_32,u1_pre_topc(A_33))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_79,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_76])).

tff(c_82,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_79])).

tff(c_83,plain,(
    ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_82])).

tff(c_48,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_42,plain,(
    ! [A_24,B_26] :
      ( r1_tarski(u1_pre_topc(A_24),k5_tmap_1(A_24,B_26))
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24)
      | ~ v2_pre_topc(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_468,plain,(
    ! [A_75,B_76] :
      ( u1_pre_topc(k6_tmap_1(A_75,B_76)) = k5_tmap_1(A_75,B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_474,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_468])).

tff(c_479,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_474])).

tff(c_480,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_479])).

tff(c_214,plain,(
    ! [A_53,B_54] :
      ( u1_pre_topc(k6_tmap_1(A_53,B_54)) = k5_tmap_1(A_53,B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_220,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_214])).

tff(c_225,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_220])).

tff(c_226,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_225])).

tff(c_98,plain,(
    ! [A_38,B_39] :
      ( l1_pre_topc(k6_tmap_1(A_38,B_39))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_101,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_98])).

tff(c_104,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_101])).

tff(c_105,plain,(
    l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_104])).

tff(c_130,plain,(
    ! [A_47,B_48] :
      ( u1_struct_0(k6_tmap_1(A_47,B_48)) = u1_struct_0(A_47)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_133,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_130])).

tff(c_136,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_133])).

tff(c_137,plain,(
    u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_136])).

tff(c_12,plain,(
    ! [A_6] :
      ( m1_subset_1(u1_pre_topc(A_6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_6))))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_165,plain,
    ( m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_12])).

tff(c_185,plain,(
    m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_165])).

tff(c_14,plain,(
    ! [B_9,A_7] :
      ( v1_tops_2(B_9,A_7)
      | ~ r1_tarski(B_9,u1_pre_topc(A_7))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_7))))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_189,plain,
    ( v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),'#skF_1')
    | ~ r1_tarski(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_185,c_14])).

tff(c_195,plain,
    ( v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),'#skF_1')
    | ~ r1_tarski(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_189])).

tff(c_203,plain,(
    ~ r1_tarski(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),u1_pre_topc('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_195])).

tff(c_16,plain,(
    ! [B_9,A_7] :
      ( r1_tarski(B_9,u1_pre_topc(A_7))
      | ~ v1_tops_2(B_9,A_7)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_7))))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_192,plain,
    ( r1_tarski(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),u1_pre_topc('#skF_1'))
    | ~ v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_185,c_16])).

tff(c_198,plain,
    ( r1_tarski(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),u1_pre_topc('#skF_1'))
    | ~ v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_192])).

tff(c_204,plain,(
    ~ v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_203,c_198])).

tff(c_229,plain,(
    ~ v1_tops_2(k5_tmap_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_204])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_106,plain,(
    ! [B_40,A_41] :
      ( v1_tops_2(B_40,A_41)
      | ~ r1_tarski(B_40,u1_pre_topc(A_41))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_41))))
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_109,plain,(
    ! [A_6] :
      ( v1_tops_2(u1_pre_topc(A_6),A_6)
      | ~ r1_tarski(u1_pre_topc(A_6),u1_pre_topc(A_6))
      | ~ l1_pre_topc(A_6) ) ),
    inference(resolution,[status(thm)],[c_12,c_106])).

tff(c_112,plain,(
    ! [A_6] :
      ( v1_tops_2(u1_pre_topc(A_6),A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_109])).

tff(c_238,plain,
    ( v1_tops_2(k5_tmap_1('#skF_1','#skF_2'),k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_112])).

tff(c_247,plain,(
    v1_tops_2(k5_tmap_1('#skF_1','#skF_2'),k6_tmap_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_238])).

tff(c_241,plain,
    ( m1_subset_1(k5_tmap_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1','#skF_2')))))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_12])).

tff(c_249,plain,(
    m1_subset_1(k5_tmap_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_137,c_241])).

tff(c_427,plain,(
    ! [B_72,A_73] :
      ( v1_tops_2(B_72,A_73)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_73),u1_pre_topc(A_73))))))
      | ~ v1_tops_2(B_72,g1_pre_topc(u1_struct_0(A_73),u1_pre_topc(A_73)))
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_439,plain,(
    ! [B_72] :
      ( v1_tops_2(B_72,'#skF_1')
      | ~ m1_subset_1(B_72,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1','#skF_2')))))
      | ~ v1_tops_2(B_72,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_427])).

tff(c_450,plain,(
    ! [B_72] :
      ( v1_tops_2(B_72,'#skF_1')
      | ~ m1_subset_1(B_72,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ v1_tops_2(B_72,k6_tmap_1('#skF_1','#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_69,c_137,c_439])).

tff(c_453,plain,(
    ! [B_74] :
      ( v1_tops_2(B_74,'#skF_1')
      | ~ m1_subset_1(B_74,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ v1_tops_2(B_74,k6_tmap_1('#skF_1','#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_450])).

tff(c_456,plain,
    ( v1_tops_2(k5_tmap_1('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_tops_2(k5_tmap_1('#skF_1','#skF_2'),k6_tmap_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_249,c_453])).

tff(c_463,plain,(
    v1_tops_2(k5_tmap_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_456])).

tff(c_465,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_229,c_463])).

tff(c_467,plain,(
    r1_tarski(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),u1_pre_topc('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_195])).

tff(c_502,plain,(
    r1_tarski(k5_tmap_1('#skF_1','#skF_2'),u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_467])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_505,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | ~ r1_tarski(u1_pre_topc('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_502,c_2])).

tff(c_519,plain,(
    ~ r1_tarski(u1_pre_topc('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_505])).

tff(c_522,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_519])).

tff(c_525,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_522])).

tff(c_527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_525])).

tff(c_528,plain,(
    k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1') ),
    inference(splitRight,[status(thm)],[c_505])).

tff(c_595,plain,(
    ! [B_79,A_80] :
      ( r2_hidden(B_79,u1_pre_topc(A_80))
      | k5_tmap_1(A_80,B_79) != u1_pre_topc(A_80)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80)
      | ~ v2_pre_topc(A_80)
      | v2_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_601,plain,
    ( r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | k5_tmap_1('#skF_1','#skF_2') != u1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_595])).

tff(c_606,plain,
    ( r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_528,c_601])).

tff(c_608,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_83,c_606])).

tff(c_610,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != k6_tmap_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1036,plain,(
    ! [A_124,B_125] :
      ( u1_pre_topc(k6_tmap_1(A_124,B_125)) = k5_tmap_1(A_124,B_125)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ l1_pre_topc(A_124)
      | ~ v2_pre_topc(A_124)
      | v2_struct_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1042,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_1036])).

tff(c_1047,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1042])).

tff(c_1048,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1047])).

tff(c_609,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_613,plain,(
    ! [B_81,A_82] :
      ( r2_hidden(B_81,u1_pre_topc(A_82))
      | ~ v3_pre_topc(B_81,A_82)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_616,plain,
    ( r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_613])).

tff(c_619,plain,(
    r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_609,c_616])).

tff(c_984,plain,(
    ! [A_118,B_119] :
      ( k5_tmap_1(A_118,B_119) = u1_pre_topc(A_118)
      | ~ r2_hidden(B_119,u1_pre_topc(A_118))
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_pre_topc(A_118)
      | ~ v2_pre_topc(A_118)
      | v2_struct_0(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_990,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_984])).

tff(c_995,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_619,c_990])).

tff(c_996,plain,(
    k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_995])).

tff(c_750,plain,(
    ! [A_102,B_103] :
      ( u1_pre_topc(k6_tmap_1(A_102,B_103)) = k5_tmap_1(A_102,B_103)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102)
      | ~ v2_pre_topc(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_756,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_750])).

tff(c_761,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_756])).

tff(c_762,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_761])).

tff(c_633,plain,(
    ! [A_87,B_88] :
      ( l1_pre_topc(k6_tmap_1(A_87,B_88))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87)
      | ~ v2_pre_topc(A_87)
      | v2_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_636,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_633])).

tff(c_639,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_636])).

tff(c_640,plain,(
    l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_639])).

tff(c_665,plain,(
    ! [A_96,B_97] :
      ( u1_struct_0(k6_tmap_1(A_96,B_97)) = u1_struct_0(A_96)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96)
      | ~ v2_pre_topc(A_96)
      | v2_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_668,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_665])).

tff(c_671,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_668])).

tff(c_672,plain,(
    u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_671])).

tff(c_700,plain,
    ( m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_672,c_12])).

tff(c_720,plain,(
    m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_640,c_700])).

tff(c_724,plain,
    ( v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),'#skF_1')
    | ~ r1_tarski(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_720,c_14])).

tff(c_730,plain,
    ( v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),'#skF_1')
    | ~ r1_tarski(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_724])).

tff(c_734,plain,(
    ~ r1_tarski(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),u1_pre_topc('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_730])).

tff(c_766,plain,(
    ~ r1_tarski(k5_tmap_1('#skF_1','#skF_2'),u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_762,c_734])).

tff(c_1005,plain,(
    ~ r1_tarski(u1_pre_topc('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_996,c_766])).

tff(c_1013,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1005])).

tff(c_1015,plain,(
    r1_tarski(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),u1_pre_topc('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_730])).

tff(c_1018,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = u1_pre_topc('#skF_1')
    | ~ r1_tarski(u1_pre_topc('#skF_1'),u1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_1015,c_2])).

tff(c_1025,plain,(
    ~ r1_tarski(u1_pre_topc('#skF_1'),u1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1018])).

tff(c_1051,plain,(
    ~ r1_tarski(u1_pre_topc('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1048,c_1025])).

tff(c_1079,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1051])).

tff(c_1082,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_1079])).

tff(c_1084,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1082])).

tff(c_1085,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = u1_pre_topc('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1018])).

tff(c_1111,plain,(
    ! [A_126,B_127] :
      ( u1_pre_topc(k6_tmap_1(A_126,B_127)) = k5_tmap_1(A_126,B_127)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_pre_topc(A_126)
      | ~ v2_pre_topc(A_126)
      | v2_struct_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1117,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_1111])).

tff(c_1122,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1085,c_1117])).

tff(c_1123,plain,(
    k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1122])).

tff(c_1224,plain,(
    ! [A_136,B_137] :
      ( g1_pre_topc(u1_struct_0(A_136),k5_tmap_1(A_136,B_137)) = k6_tmap_1(A_136,B_137)
      | ~ m1_subset_1(B_137,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ l1_pre_topc(A_136)
      | ~ v2_pre_topc(A_136)
      | v2_struct_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1228,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_1224])).

tff(c_1233,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1123,c_1228])).

tff(c_1235,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_610,c_1233])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:27:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.45/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/1.57  
% 3.45/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/1.57  %$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1
% 3.45/1.57  
% 3.45/1.57  %Foreground sorts:
% 3.45/1.57  
% 3.45/1.57  
% 3.45/1.57  %Background operators:
% 3.45/1.57  
% 3.45/1.57  
% 3.45/1.57  %Foreground operators:
% 3.45/1.57  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.45/1.57  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.45/1.57  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.45/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.45/1.57  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.45/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.45/1.57  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 3.45/1.57  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.45/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.45/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.45/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.45/1.57  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.45/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.45/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.45/1.57  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 3.45/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.45/1.57  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.45/1.57  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 3.45/1.57  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.45/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.45/1.57  
% 3.45/1.60  tff(f_151, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k6_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_tmap_1)).
% 3.45/1.60  tff(f_40, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 3.45/1.60  tff(f_136, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(u1_pre_topc(A), k5_tmap_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_tmap_1)).
% 3.45/1.60  tff(f_124, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tmap_1)).
% 3.45/1.60  tff(f_96, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 3.45/1.60  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 3.45/1.60  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> r1_tarski(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_tops_2)).
% 3.45/1.60  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.45/1.60  tff(f_69, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_tops_2(B, A) & m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))) <=> (v1_tops_2(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_compts_1)).
% 3.45/1.60  tff(f_110, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) <=> (u1_pre_topc(A) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_tmap_1)).
% 3.45/1.60  tff(f_81, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k6_tmap_1(A, B) = g1_pre_topc(u1_struct_0(A), k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_tmap_1)).
% 3.45/1.60  tff(c_50, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.45/1.60  tff(c_58, plain, (v3_pre_topc('#skF_2', '#skF_1') | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.45/1.60  tff(c_69, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_58])).
% 3.45/1.60  tff(c_52, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=k6_tmap_1('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.45/1.60  tff(c_75, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_52])).
% 3.45/1.60  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.45/1.60  tff(c_44, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.45/1.60  tff(c_76, plain, (![B_32, A_33]: (v3_pre_topc(B_32, A_33) | ~r2_hidden(B_32, u1_pre_topc(A_33)) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.45/1.60  tff(c_79, plain, (v3_pre_topc('#skF_2', '#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_76])).
% 3.45/1.60  tff(c_82, plain, (v3_pre_topc('#skF_2', '#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_79])).
% 3.45/1.60  tff(c_83, plain, (~r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_75, c_82])).
% 3.45/1.60  tff(c_48, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.45/1.60  tff(c_42, plain, (![A_24, B_26]: (r1_tarski(u1_pre_topc(A_24), k5_tmap_1(A_24, B_26)) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24) | ~v2_pre_topc(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.45/1.60  tff(c_468, plain, (![A_75, B_76]: (u1_pre_topc(k6_tmap_1(A_75, B_76))=k5_tmap_1(A_75, B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75) | v2_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.45/1.60  tff(c_474, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_468])).
% 3.45/1.60  tff(c_479, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_474])).
% 3.45/1.60  tff(c_480, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_479])).
% 3.45/1.60  tff(c_214, plain, (![A_53, B_54]: (u1_pre_topc(k6_tmap_1(A_53, B_54))=k5_tmap_1(A_53, B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53) | ~v2_pre_topc(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.45/1.60  tff(c_220, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_214])).
% 3.45/1.60  tff(c_225, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_220])).
% 3.45/1.60  tff(c_226, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_225])).
% 3.45/1.60  tff(c_98, plain, (![A_38, B_39]: (l1_pre_topc(k6_tmap_1(A_38, B_39)) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.45/1.60  tff(c_101, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_98])).
% 3.45/1.60  tff(c_104, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_101])).
% 3.45/1.60  tff(c_105, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_104])).
% 3.45/1.60  tff(c_130, plain, (![A_47, B_48]: (u1_struct_0(k6_tmap_1(A_47, B_48))=u1_struct_0(A_47) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47) | ~v2_pre_topc(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.45/1.60  tff(c_133, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_130])).
% 3.45/1.60  tff(c_136, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_133])).
% 3.45/1.60  tff(c_137, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_136])).
% 3.45/1.60  tff(c_12, plain, (![A_6]: (m1_subset_1(u1_pre_topc(A_6), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_6)))) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.45/1.60  tff(c_165, plain, (m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_137, c_12])).
% 3.45/1.60  tff(c_185, plain, (m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_165])).
% 3.45/1.60  tff(c_14, plain, (![B_9, A_7]: (v1_tops_2(B_9, A_7) | ~r1_tarski(B_9, u1_pre_topc(A_7)) | ~m1_subset_1(B_9, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_7)))) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.45/1.60  tff(c_189, plain, (v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), '#skF_1') | ~r1_tarski(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_185, c_14])).
% 3.45/1.60  tff(c_195, plain, (v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), '#skF_1') | ~r1_tarski(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_189])).
% 3.45/1.60  tff(c_203, plain, (~r1_tarski(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), u1_pre_topc('#skF_1'))), inference(splitLeft, [status(thm)], [c_195])).
% 3.45/1.60  tff(c_16, plain, (![B_9, A_7]: (r1_tarski(B_9, u1_pre_topc(A_7)) | ~v1_tops_2(B_9, A_7) | ~m1_subset_1(B_9, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_7)))) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.45/1.60  tff(c_192, plain, (r1_tarski(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), u1_pre_topc('#skF_1')) | ~v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_185, c_16])).
% 3.45/1.60  tff(c_198, plain, (r1_tarski(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), u1_pre_topc('#skF_1')) | ~v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_192])).
% 3.45/1.60  tff(c_204, plain, (~v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_203, c_198])).
% 3.45/1.60  tff(c_229, plain, (~v1_tops_2(k5_tmap_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_226, c_204])).
% 3.45/1.60  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.45/1.60  tff(c_106, plain, (![B_40, A_41]: (v1_tops_2(B_40, A_41) | ~r1_tarski(B_40, u1_pre_topc(A_41)) | ~m1_subset_1(B_40, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_41)))) | ~l1_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.45/1.60  tff(c_109, plain, (![A_6]: (v1_tops_2(u1_pre_topc(A_6), A_6) | ~r1_tarski(u1_pre_topc(A_6), u1_pre_topc(A_6)) | ~l1_pre_topc(A_6))), inference(resolution, [status(thm)], [c_12, c_106])).
% 3.45/1.60  tff(c_112, plain, (![A_6]: (v1_tops_2(u1_pre_topc(A_6), A_6) | ~l1_pre_topc(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_109])).
% 3.45/1.60  tff(c_238, plain, (v1_tops_2(k5_tmap_1('#skF_1', '#skF_2'), k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_226, c_112])).
% 3.45/1.60  tff(c_247, plain, (v1_tops_2(k5_tmap_1('#skF_1', '#skF_2'), k6_tmap_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_238])).
% 3.45/1.60  tff(c_241, plain, (m1_subset_1(k5_tmap_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))))) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_226, c_12])).
% 3.45/1.60  tff(c_249, plain, (m1_subset_1(k5_tmap_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_137, c_241])).
% 3.45/1.60  tff(c_427, plain, (![B_72, A_73]: (v1_tops_2(B_72, A_73) | ~m1_subset_1(B_72, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_73), u1_pre_topc(A_73)))))) | ~v1_tops_2(B_72, g1_pre_topc(u1_struct_0(A_73), u1_pre_topc(A_73))) | ~l1_pre_topc(A_73) | ~v2_pre_topc(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.45/1.60  tff(c_439, plain, (![B_72]: (v1_tops_2(B_72, '#skF_1') | ~m1_subset_1(B_72, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))))) | ~v1_tops_2(B_72, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_69, c_427])).
% 3.45/1.60  tff(c_450, plain, (![B_72]: (v1_tops_2(B_72, '#skF_1') | ~m1_subset_1(B_72, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~v1_tops_2(B_72, k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_69, c_137, c_439])).
% 3.45/1.60  tff(c_453, plain, (![B_74]: (v1_tops_2(B_74, '#skF_1') | ~m1_subset_1(B_74, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~v1_tops_2(B_74, k6_tmap_1('#skF_1', '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_50, c_450])).
% 3.45/1.60  tff(c_456, plain, (v1_tops_2(k5_tmap_1('#skF_1', '#skF_2'), '#skF_1') | ~v1_tops_2(k5_tmap_1('#skF_1', '#skF_2'), k6_tmap_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_249, c_453])).
% 3.45/1.60  tff(c_463, plain, (v1_tops_2(k5_tmap_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_247, c_456])).
% 3.45/1.60  tff(c_465, plain, $false, inference(negUnitSimplification, [status(thm)], [c_229, c_463])).
% 3.45/1.60  tff(c_467, plain, (r1_tarski(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), u1_pre_topc('#skF_1'))), inference(splitRight, [status(thm)], [c_195])).
% 3.45/1.60  tff(c_502, plain, (r1_tarski(k5_tmap_1('#skF_1', '#skF_2'), u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_480, c_467])).
% 3.45/1.60  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.45/1.60  tff(c_505, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | ~r1_tarski(u1_pre_topc('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_502, c_2])).
% 3.45/1.60  tff(c_519, plain, (~r1_tarski(u1_pre_topc('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_505])).
% 3.45/1.60  tff(c_522, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_519])).
% 3.45/1.60  tff(c_525, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_522])).
% 3.45/1.60  tff(c_527, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_525])).
% 3.45/1.60  tff(c_528, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1')), inference(splitRight, [status(thm)], [c_505])).
% 3.45/1.60  tff(c_595, plain, (![B_79, A_80]: (r2_hidden(B_79, u1_pre_topc(A_80)) | k5_tmap_1(A_80, B_79)!=u1_pre_topc(A_80) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80) | ~v2_pre_topc(A_80) | v2_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.45/1.60  tff(c_601, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | k5_tmap_1('#skF_1', '#skF_2')!=u1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_595])).
% 3.45/1.60  tff(c_606, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_528, c_601])).
% 3.45/1.60  tff(c_608, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_83, c_606])).
% 3.45/1.60  tff(c_610, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=k6_tmap_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_58])).
% 3.45/1.60  tff(c_1036, plain, (![A_124, B_125]: (u1_pre_topc(k6_tmap_1(A_124, B_125))=k5_tmap_1(A_124, B_125) | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_124))) | ~l1_pre_topc(A_124) | ~v2_pre_topc(A_124) | v2_struct_0(A_124))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.45/1.60  tff(c_1042, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_1036])).
% 3.45/1.60  tff(c_1047, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1042])).
% 3.45/1.60  tff(c_1048, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_1047])).
% 3.45/1.60  tff(c_609, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_58])).
% 3.45/1.60  tff(c_613, plain, (![B_81, A_82]: (r2_hidden(B_81, u1_pre_topc(A_82)) | ~v3_pre_topc(B_81, A_82) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.45/1.60  tff(c_616, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~v3_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_613])).
% 3.45/1.60  tff(c_619, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_609, c_616])).
% 3.45/1.60  tff(c_984, plain, (![A_118, B_119]: (k5_tmap_1(A_118, B_119)=u1_pre_topc(A_118) | ~r2_hidden(B_119, u1_pre_topc(A_118)) | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_pre_topc(A_118) | ~v2_pre_topc(A_118) | v2_struct_0(A_118))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.45/1.60  tff(c_990, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_984])).
% 3.45/1.60  tff(c_995, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_619, c_990])).
% 3.45/1.60  tff(c_996, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_995])).
% 3.45/1.60  tff(c_750, plain, (![A_102, B_103]: (u1_pre_topc(k6_tmap_1(A_102, B_103))=k5_tmap_1(A_102, B_103) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102) | ~v2_pre_topc(A_102) | v2_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.45/1.60  tff(c_756, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_750])).
% 3.45/1.60  tff(c_761, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_756])).
% 3.45/1.60  tff(c_762, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_761])).
% 3.45/1.60  tff(c_633, plain, (![A_87, B_88]: (l1_pre_topc(k6_tmap_1(A_87, B_88)) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87) | ~v2_pre_topc(A_87) | v2_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.45/1.60  tff(c_636, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_633])).
% 3.45/1.60  tff(c_639, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_636])).
% 3.45/1.60  tff(c_640, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_639])).
% 3.45/1.60  tff(c_665, plain, (![A_96, B_97]: (u1_struct_0(k6_tmap_1(A_96, B_97))=u1_struct_0(A_96) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96) | ~v2_pre_topc(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.45/1.60  tff(c_668, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_665])).
% 3.45/1.60  tff(c_671, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_668])).
% 3.45/1.60  tff(c_672, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_671])).
% 3.45/1.60  tff(c_700, plain, (m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_672, c_12])).
% 3.45/1.60  tff(c_720, plain, (m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_640, c_700])).
% 3.45/1.60  tff(c_724, plain, (v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), '#skF_1') | ~r1_tarski(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_720, c_14])).
% 3.45/1.60  tff(c_730, plain, (v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), '#skF_1') | ~r1_tarski(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_724])).
% 3.45/1.60  tff(c_734, plain, (~r1_tarski(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), u1_pre_topc('#skF_1'))), inference(splitLeft, [status(thm)], [c_730])).
% 3.45/1.60  tff(c_766, plain, (~r1_tarski(k5_tmap_1('#skF_1', '#skF_2'), u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_762, c_734])).
% 3.45/1.60  tff(c_1005, plain, (~r1_tarski(u1_pre_topc('#skF_1'), u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_996, c_766])).
% 3.45/1.60  tff(c_1013, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1005])).
% 3.45/1.60  tff(c_1015, plain, (r1_tarski(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), u1_pre_topc('#skF_1'))), inference(splitRight, [status(thm)], [c_730])).
% 3.45/1.60  tff(c_1018, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=u1_pre_topc('#skF_1') | ~r1_tarski(u1_pre_topc('#skF_1'), u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_1015, c_2])).
% 3.45/1.60  tff(c_1025, plain, (~r1_tarski(u1_pre_topc('#skF_1'), u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1018])).
% 3.45/1.60  tff(c_1051, plain, (~r1_tarski(u1_pre_topc('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1048, c_1025])).
% 3.45/1.60  tff(c_1079, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1051])).
% 3.45/1.60  tff(c_1082, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_1079])).
% 3.45/1.60  tff(c_1084, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_1082])).
% 3.45/1.60  tff(c_1085, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=u1_pre_topc('#skF_1')), inference(splitRight, [status(thm)], [c_1018])).
% 3.45/1.60  tff(c_1111, plain, (![A_126, B_127]: (u1_pre_topc(k6_tmap_1(A_126, B_127))=k5_tmap_1(A_126, B_127) | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_pre_topc(A_126) | ~v2_pre_topc(A_126) | v2_struct_0(A_126))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.45/1.60  tff(c_1117, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_1111])).
% 3.45/1.60  tff(c_1122, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1085, c_1117])).
% 3.45/1.60  tff(c_1123, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_1122])).
% 3.45/1.60  tff(c_1224, plain, (![A_136, B_137]: (g1_pre_topc(u1_struct_0(A_136), k5_tmap_1(A_136, B_137))=k6_tmap_1(A_136, B_137) | ~m1_subset_1(B_137, k1_zfmisc_1(u1_struct_0(A_136))) | ~l1_pre_topc(A_136) | ~v2_pre_topc(A_136) | v2_struct_0(A_136))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.45/1.60  tff(c_1228, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_1224])).
% 3.45/1.60  tff(c_1233, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1123, c_1228])).
% 3.45/1.60  tff(c_1235, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_610, c_1233])).
% 3.45/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/1.60  
% 3.45/1.60  Inference rules
% 3.45/1.60  ----------------------
% 3.45/1.60  #Ref     : 0
% 3.45/1.60  #Sup     : 187
% 3.45/1.60  #Fact    : 0
% 3.45/1.60  #Define  : 0
% 3.45/1.60  #Split   : 16
% 3.45/1.60  #Chain   : 0
% 3.45/1.60  #Close   : 0
% 3.45/1.60  
% 3.45/1.60  Ordering : KBO
% 3.45/1.60  
% 3.45/1.60  Simplification rules
% 3.45/1.60  ----------------------
% 3.45/1.60  #Subsume      : 13
% 3.45/1.60  #Demod        : 462
% 3.45/1.60  #Tautology    : 117
% 3.45/1.60  #SimpNegUnit  : 48
% 3.45/1.60  #BackRed      : 48
% 3.45/1.60  
% 3.45/1.60  #Partial instantiations: 0
% 3.45/1.60  #Strategies tried      : 1
% 3.45/1.60  
% 3.45/1.60  Timing (in seconds)
% 3.45/1.60  ----------------------
% 3.45/1.60  Preprocessing        : 0.33
% 3.45/1.60  Parsing              : 0.17
% 3.45/1.60  CNF conversion       : 0.02
% 3.45/1.60  Main loop            : 0.43
% 3.45/1.60  Inferencing          : 0.15
% 3.45/1.60  Reduction            : 0.16
% 3.45/1.60  Demodulation         : 0.11
% 3.45/1.60  BG Simplification    : 0.02
% 3.45/1.60  Subsumption          : 0.07
% 3.45/1.60  Abstraction          : 0.02
% 3.45/1.60  MUC search           : 0.00
% 3.45/1.60  Cooper               : 0.00
% 3.45/1.60  Total                : 0.82
% 3.45/1.60  Index Insertion      : 0.00
% 3.45/1.60  Index Deletion       : 0.00
% 3.45/1.60  Index Matching       : 0.00
% 3.45/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
