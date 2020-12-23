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
% DateTime   : Thu Dec  3 10:27:49 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 515 expanded)
%              Number of leaves         :   32 ( 197 expanded)
%              Depth                    :   16
%              Number of atoms          :  293 (1651 expanded)
%              Number of equality atoms :   44 ( 258 expanded)
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

tff(f_149,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k6_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tmap_1)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_134,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(u1_pre_topc(A),k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_tmap_1)).

tff(f_122,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
            & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> r1_tarski(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tops_2)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => v1_tops_2(u1_pre_topc(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_compts_1)).

tff(f_79,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_108,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,u1_pre_topc(A))
          <=> u1_pre_topc(A) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tmap_1)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_54,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != k6_tmap_1('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_81,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_46,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_105,plain,(
    ! [B_35,A_36] :
      ( v3_pre_topc(B_35,A_36)
      | ~ r2_hidden(B_35,u1_pre_topc(A_36))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_108,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_105])).

tff(c_111,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_108])).

tff(c_112,plain,(
    ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_111])).

tff(c_50,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_44,plain,(
    ! [A_23,B_25] :
      ( r1_tarski(u1_pre_topc(A_23),k5_tmap_1(A_23,B_25))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_526,plain,(
    ! [A_74,B_75] :
      ( u1_pre_topc(k6_tmap_1(A_74,B_75)) = k5_tmap_1(A_74,B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_532,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_526])).

tff(c_537,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_532])).

tff(c_538,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_537])).

tff(c_235,plain,(
    ! [A_51,B_52] :
      ( u1_pre_topc(k6_tmap_1(A_51,B_52)) = k5_tmap_1(A_51,B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_241,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_235])).

tff(c_246,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_241])).

tff(c_247,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_246])).

tff(c_134,plain,(
    ! [A_43,B_44] :
      ( l1_pre_topc(k6_tmap_1(A_43,B_44))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43)
      | ~ v2_pre_topc(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_137,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_134])).

tff(c_140,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_137])).

tff(c_141,plain,(
    l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_140])).

tff(c_154,plain,(
    ! [A_49,B_50] :
      ( u1_struct_0(k6_tmap_1(A_49,B_50)) = u1_struct_0(A_49)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49)
      | ~ v2_pre_topc(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_157,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_154])).

tff(c_160,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_157])).

tff(c_161,plain,(
    u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_160])).

tff(c_14,plain,(
    ! [A_7] :
      ( m1_subset_1(u1_pre_topc(A_7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_7))))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_192,plain,
    ( m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_14])).

tff(c_214,plain,(
    m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_192])).

tff(c_18,plain,(
    ! [B_10,A_8] :
      ( r1_tarski(B_10,u1_pre_topc(A_8))
      | ~ v1_tops_2(B_10,A_8)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_8))))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_218,plain,
    ( r1_tarski(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),u1_pre_topc('#skF_1'))
    | ~ v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_214,c_18])).

tff(c_224,plain,
    ( r1_tarski(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),u1_pre_topc('#skF_1'))
    | ~ v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_218])).

tff(c_232,plain,(
    ~ v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_224])).

tff(c_249,plain,(
    ~ v1_tops_2(k5_tmap_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_232])).

tff(c_20,plain,(
    ! [A_11] :
      ( v1_tops_2(u1_pre_topc(A_11),A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_264,plain,
    ( v1_tops_2(k5_tmap_1('#skF_1','#skF_2'),k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_20])).

tff(c_274,plain,(
    v1_tops_2(k5_tmap_1('#skF_1','#skF_2'),k6_tmap_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_264])).

tff(c_261,plain,
    ( m1_subset_1(k5_tmap_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1','#skF_2')))))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_14])).

tff(c_272,plain,(
    m1_subset_1(k5_tmap_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_161,c_261])).

tff(c_60,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_82,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_60])).

tff(c_482,plain,(
    ! [B_71,A_72] :
      ( v1_tops_2(B_71,A_72)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_72),u1_pre_topc(A_72))))))
      | ~ v1_tops_2(B_71,g1_pre_topc(u1_struct_0(A_72),u1_pre_topc(A_72)))
      | ~ l1_pre_topc(A_72)
      | ~ v2_pre_topc(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_494,plain,(
    ! [B_71] :
      ( v1_tops_2(B_71,'#skF_1')
      | ~ m1_subset_1(B_71,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1','#skF_2')))))
      | ~ v1_tops_2(B_71,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_482])).

tff(c_508,plain,(
    ! [B_71] :
      ( v1_tops_2(B_71,'#skF_1')
      | ~ m1_subset_1(B_71,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ v1_tops_2(B_71,k6_tmap_1('#skF_1','#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_82,c_161,c_494])).

tff(c_511,plain,(
    ! [B_73] :
      ( v1_tops_2(B_73,'#skF_1')
      | ~ m1_subset_1(B_73,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ v1_tops_2(B_73,k6_tmap_1('#skF_1','#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_508])).

tff(c_514,plain,
    ( v1_tops_2(k5_tmap_1('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_tops_2(k5_tmap_1('#skF_1','#skF_2'),k6_tmap_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_272,c_511])).

tff(c_521,plain,(
    v1_tops_2(k5_tmap_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_514])).

tff(c_523,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_249,c_521])).

tff(c_525,plain,(
    v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_224])).

tff(c_539,plain,(
    v1_tops_2(k5_tmap_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_538,c_525])).

tff(c_551,plain,
    ( m1_subset_1(k5_tmap_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1','#skF_2')))))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_538,c_14])).

tff(c_562,plain,(
    m1_subset_1(k5_tmap_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_161,c_551])).

tff(c_568,plain,
    ( r1_tarski(k5_tmap_1('#skF_1','#skF_2'),u1_pre_topc('#skF_1'))
    | ~ v1_tops_2(k5_tmap_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_562,c_18])).

tff(c_574,plain,(
    r1_tarski(k5_tmap_1('#skF_1','#skF_2'),u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_539,c_568])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_580,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | ~ r1_tarski(u1_pre_topc('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_574,c_2])).

tff(c_601,plain,(
    ~ r1_tarski(u1_pre_topc('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_580])).

tff(c_604,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_601])).

tff(c_607,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_604])).

tff(c_609,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_607])).

tff(c_610,plain,(
    k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1') ),
    inference(splitRight,[status(thm)],[c_580])).

tff(c_668,plain,(
    ! [B_78,A_79] :
      ( r2_hidden(B_78,u1_pre_topc(A_79))
      | k5_tmap_1(A_79,B_78) != u1_pre_topc(A_79)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79)
      | ~ v2_pre_topc(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_674,plain,
    ( r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | k5_tmap_1('#skF_1','#skF_2') != u1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_668])).

tff(c_679,plain,
    ( r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_610,c_674])).

tff(c_681,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_112,c_679])).

tff(c_682,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != k6_tmap_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_683,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_692,plain,(
    ! [B_80,A_81] :
      ( r2_hidden(B_80,u1_pre_topc(A_81))
      | ~ v3_pre_topc(B_80,A_81)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_695,plain,
    ( r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_692])).

tff(c_698,plain,(
    r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_683,c_695])).

tff(c_898,plain,(
    ! [A_102,B_103] :
      ( k5_tmap_1(A_102,B_103) = u1_pre_topc(A_102)
      | ~ r2_hidden(B_103,u1_pre_topc(A_102))
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102)
      | ~ v2_pre_topc(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_904,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_898])).

tff(c_909,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_698,c_904])).

tff(c_910,plain,(
    k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_909])).

tff(c_831,plain,(
    ! [A_99,B_100] :
      ( u1_pre_topc(k6_tmap_1(A_99,B_100)) = k5_tmap_1(A_99,B_100)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99)
      | ~ v2_pre_topc(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_837,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_831])).

tff(c_842,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_837])).

tff(c_843,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_842])).

tff(c_727,plain,(
    ! [A_90,B_91] :
      ( l1_pre_topc(k6_tmap_1(A_90,B_91))
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_pre_topc(A_90)
      | ~ v2_pre_topc(A_90)
      | v2_struct_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_730,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_727])).

tff(c_733,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_730])).

tff(c_734,plain,(
    l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_733])).

tff(c_735,plain,(
    ! [A_92,B_93] :
      ( v1_pre_topc(k6_tmap_1(A_92,B_93))
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92)
      | ~ v2_pre_topc(A_92)
      | v2_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_738,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_735])).

tff(c_741,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_738])).

tff(c_742,plain,(
    v1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_741])).

tff(c_743,plain,(
    ! [A_94,B_95] :
      ( u1_struct_0(k6_tmap_1(A_94,B_95)) = u1_struct_0(A_94)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94)
      | v2_struct_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_746,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_743])).

tff(c_749,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_746])).

tff(c_750,plain,(
    u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_749])).

tff(c_8,plain,(
    ! [A_3] :
      ( g1_pre_topc(u1_struct_0(A_3),u1_pre_topc(A_3)) = A_3
      | ~ v1_pre_topc(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_778,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))) = k6_tmap_1('#skF_1','#skF_2')
    | ~ v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_750,c_8])).

tff(c_801,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_734,c_742,c_778])).

tff(c_847,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_843,c_801])).

tff(c_912,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_910,c_847])).

tff(c_919,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_682,c_912])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:25:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.47  
% 3.14/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.48  %$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1
% 3.14/1.48  
% 3.14/1.48  %Foreground sorts:
% 3.14/1.48  
% 3.14/1.48  
% 3.14/1.48  %Background operators:
% 3.14/1.48  
% 3.14/1.48  
% 3.14/1.48  %Foreground operators:
% 3.14/1.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.14/1.48  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.14/1.48  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.14/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.48  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.14/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.14/1.48  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 3.14/1.48  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.14/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.14/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.14/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.14/1.48  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.14/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.14/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.48  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 3.14/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.48  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.14/1.48  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 3.14/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.14/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.14/1.48  
% 3.30/1.50  tff(f_149, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k6_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_tmap_1)).
% 3.30/1.50  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 3.30/1.50  tff(f_134, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(u1_pre_topc(A), k5_tmap_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_tmap_1)).
% 3.30/1.50  tff(f_122, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tmap_1)).
% 3.30/1.50  tff(f_94, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 3.30/1.50  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 3.30/1.50  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> r1_tarski(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_tops_2)).
% 3.30/1.50  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => v1_tops_2(u1_pre_topc(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_compts_1)).
% 3.30/1.50  tff(f_79, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_tops_2(B, A) & m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))) <=> (v1_tops_2(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_compts_1)).
% 3.30/1.50  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.30/1.50  tff(f_108, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) <=> (u1_pre_topc(A) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_tmap_1)).
% 3.30/1.50  tff(f_37, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 3.30/1.50  tff(c_52, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.30/1.50  tff(c_54, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=k6_tmap_1('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.30/1.50  tff(c_81, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_54])).
% 3.30/1.50  tff(c_48, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.30/1.50  tff(c_46, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.30/1.50  tff(c_105, plain, (![B_35, A_36]: (v3_pre_topc(B_35, A_36) | ~r2_hidden(B_35, u1_pre_topc(A_36)) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.30/1.50  tff(c_108, plain, (v3_pre_topc('#skF_2', '#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_105])).
% 3.30/1.50  tff(c_111, plain, (v3_pre_topc('#skF_2', '#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_108])).
% 3.30/1.50  tff(c_112, plain, (~r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_81, c_111])).
% 3.30/1.50  tff(c_50, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.30/1.50  tff(c_44, plain, (![A_23, B_25]: (r1_tarski(u1_pre_topc(A_23), k5_tmap_1(A_23, B_25)) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.30/1.50  tff(c_526, plain, (![A_74, B_75]: (u1_pre_topc(k6_tmap_1(A_74, B_75))=k5_tmap_1(A_74, B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.30/1.50  tff(c_532, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_526])).
% 3.30/1.50  tff(c_537, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_532])).
% 3.30/1.50  tff(c_538, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_52, c_537])).
% 3.30/1.50  tff(c_235, plain, (![A_51, B_52]: (u1_pre_topc(k6_tmap_1(A_51, B_52))=k5_tmap_1(A_51, B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.30/1.50  tff(c_241, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_235])).
% 3.30/1.50  tff(c_246, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_241])).
% 3.30/1.50  tff(c_247, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_52, c_246])).
% 3.30/1.50  tff(c_134, plain, (![A_43, B_44]: (l1_pre_topc(k6_tmap_1(A_43, B_44)) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43) | ~v2_pre_topc(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.30/1.50  tff(c_137, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_134])).
% 3.30/1.50  tff(c_140, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_137])).
% 3.30/1.50  tff(c_141, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_140])).
% 3.30/1.50  tff(c_154, plain, (![A_49, B_50]: (u1_struct_0(k6_tmap_1(A_49, B_50))=u1_struct_0(A_49) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_pre_topc(A_49) | ~v2_pre_topc(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.30/1.50  tff(c_157, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_154])).
% 3.30/1.50  tff(c_160, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_157])).
% 3.30/1.50  tff(c_161, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_52, c_160])).
% 3.30/1.50  tff(c_14, plain, (![A_7]: (m1_subset_1(u1_pre_topc(A_7), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_7)))) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.30/1.50  tff(c_192, plain, (m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_161, c_14])).
% 3.30/1.50  tff(c_214, plain, (m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_192])).
% 3.30/1.50  tff(c_18, plain, (![B_10, A_8]: (r1_tarski(B_10, u1_pre_topc(A_8)) | ~v1_tops_2(B_10, A_8) | ~m1_subset_1(B_10, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_8)))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.30/1.50  tff(c_218, plain, (r1_tarski(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), u1_pre_topc('#skF_1')) | ~v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_214, c_18])).
% 3.30/1.50  tff(c_224, plain, (r1_tarski(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), u1_pre_topc('#skF_1')) | ~v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_218])).
% 3.30/1.50  tff(c_232, plain, (~v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), '#skF_1')), inference(splitLeft, [status(thm)], [c_224])).
% 3.30/1.50  tff(c_249, plain, (~v1_tops_2(k5_tmap_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_247, c_232])).
% 3.30/1.50  tff(c_20, plain, (![A_11]: (v1_tops_2(u1_pre_topc(A_11), A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.30/1.50  tff(c_264, plain, (v1_tops_2(k5_tmap_1('#skF_1', '#skF_2'), k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_247, c_20])).
% 3.30/1.50  tff(c_274, plain, (v1_tops_2(k5_tmap_1('#skF_1', '#skF_2'), k6_tmap_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_264])).
% 3.30/1.50  tff(c_261, plain, (m1_subset_1(k5_tmap_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))))) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_247, c_14])).
% 3.30/1.50  tff(c_272, plain, (m1_subset_1(k5_tmap_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_161, c_261])).
% 3.30/1.50  tff(c_60, plain, (v3_pre_topc('#skF_2', '#skF_1') | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.30/1.50  tff(c_82, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_81, c_60])).
% 3.30/1.50  tff(c_482, plain, (![B_71, A_72]: (v1_tops_2(B_71, A_72) | ~m1_subset_1(B_71, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_72), u1_pre_topc(A_72)))))) | ~v1_tops_2(B_71, g1_pre_topc(u1_struct_0(A_72), u1_pre_topc(A_72))) | ~l1_pre_topc(A_72) | ~v2_pre_topc(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.30/1.50  tff(c_494, plain, (![B_71]: (v1_tops_2(B_71, '#skF_1') | ~m1_subset_1(B_71, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))))) | ~v1_tops_2(B_71, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_482])).
% 3.30/1.50  tff(c_508, plain, (![B_71]: (v1_tops_2(B_71, '#skF_1') | ~m1_subset_1(B_71, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~v1_tops_2(B_71, k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_82, c_161, c_494])).
% 3.30/1.50  tff(c_511, plain, (![B_73]: (v1_tops_2(B_73, '#skF_1') | ~m1_subset_1(B_73, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~v1_tops_2(B_73, k6_tmap_1('#skF_1', '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_52, c_508])).
% 3.30/1.50  tff(c_514, plain, (v1_tops_2(k5_tmap_1('#skF_1', '#skF_2'), '#skF_1') | ~v1_tops_2(k5_tmap_1('#skF_1', '#skF_2'), k6_tmap_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_272, c_511])).
% 3.30/1.50  tff(c_521, plain, (v1_tops_2(k5_tmap_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_274, c_514])).
% 3.30/1.50  tff(c_523, plain, $false, inference(negUnitSimplification, [status(thm)], [c_249, c_521])).
% 3.30/1.50  tff(c_525, plain, (v1_tops_2(u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')), '#skF_1')), inference(splitRight, [status(thm)], [c_224])).
% 3.30/1.50  tff(c_539, plain, (v1_tops_2(k5_tmap_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_538, c_525])).
% 3.30/1.50  tff(c_551, plain, (m1_subset_1(k5_tmap_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))))) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_538, c_14])).
% 3.30/1.50  tff(c_562, plain, (m1_subset_1(k5_tmap_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_161, c_551])).
% 3.30/1.50  tff(c_568, plain, (r1_tarski(k5_tmap_1('#skF_1', '#skF_2'), u1_pre_topc('#skF_1')) | ~v1_tops_2(k5_tmap_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_562, c_18])).
% 3.30/1.50  tff(c_574, plain, (r1_tarski(k5_tmap_1('#skF_1', '#skF_2'), u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_539, c_568])).
% 3.30/1.50  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.30/1.50  tff(c_580, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | ~r1_tarski(u1_pre_topc('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_574, c_2])).
% 3.30/1.50  tff(c_601, plain, (~r1_tarski(u1_pre_topc('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_580])).
% 3.30/1.50  tff(c_604, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_601])).
% 3.30/1.50  tff(c_607, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_604])).
% 3.30/1.50  tff(c_609, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_607])).
% 3.30/1.50  tff(c_610, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1')), inference(splitRight, [status(thm)], [c_580])).
% 3.30/1.50  tff(c_668, plain, (![B_78, A_79]: (r2_hidden(B_78, u1_pre_topc(A_79)) | k5_tmap_1(A_79, B_78)!=u1_pre_topc(A_79) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79) | ~v2_pre_topc(A_79) | v2_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.30/1.50  tff(c_674, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | k5_tmap_1('#skF_1', '#skF_2')!=u1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_668])).
% 3.30/1.50  tff(c_679, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_610, c_674])).
% 3.30/1.50  tff(c_681, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_112, c_679])).
% 3.30/1.50  tff(c_682, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=k6_tmap_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_54])).
% 3.30/1.50  tff(c_683, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_54])).
% 3.30/1.50  tff(c_692, plain, (![B_80, A_81]: (r2_hidden(B_80, u1_pre_topc(A_81)) | ~v3_pre_topc(B_80, A_81) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.30/1.50  tff(c_695, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~v3_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_692])).
% 3.30/1.50  tff(c_698, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_683, c_695])).
% 3.30/1.50  tff(c_898, plain, (![A_102, B_103]: (k5_tmap_1(A_102, B_103)=u1_pre_topc(A_102) | ~r2_hidden(B_103, u1_pre_topc(A_102)) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102) | ~v2_pre_topc(A_102) | v2_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.30/1.50  tff(c_904, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_898])).
% 3.30/1.50  tff(c_909, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_698, c_904])).
% 3.30/1.50  tff(c_910, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_52, c_909])).
% 3.30/1.50  tff(c_831, plain, (![A_99, B_100]: (u1_pre_topc(k6_tmap_1(A_99, B_100))=k5_tmap_1(A_99, B_100) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99) | ~v2_pre_topc(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.30/1.50  tff(c_837, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_831])).
% 3.30/1.50  tff(c_842, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_837])).
% 3.30/1.50  tff(c_843, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_52, c_842])).
% 3.30/1.50  tff(c_727, plain, (![A_90, B_91]: (l1_pre_topc(k6_tmap_1(A_90, B_91)) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_pre_topc(A_90) | ~v2_pre_topc(A_90) | v2_struct_0(A_90))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.30/1.50  tff(c_730, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_727])).
% 3.30/1.50  tff(c_733, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_730])).
% 3.30/1.50  tff(c_734, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_733])).
% 3.30/1.50  tff(c_735, plain, (![A_92, B_93]: (v1_pre_topc(k6_tmap_1(A_92, B_93)) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92) | ~v2_pre_topc(A_92) | v2_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.30/1.50  tff(c_738, plain, (v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_735])).
% 3.30/1.50  tff(c_741, plain, (v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_738])).
% 3.30/1.50  tff(c_742, plain, (v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_741])).
% 3.30/1.50  tff(c_743, plain, (![A_94, B_95]: (u1_struct_0(k6_tmap_1(A_94, B_95))=u1_struct_0(A_94) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94) | ~v2_pre_topc(A_94) | v2_struct_0(A_94))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.30/1.50  tff(c_746, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_743])).
% 3.30/1.50  tff(c_749, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_746])).
% 3.30/1.50  tff(c_750, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_52, c_749])).
% 3.30/1.50  tff(c_8, plain, (![A_3]: (g1_pre_topc(u1_struct_0(A_3), u1_pre_topc(A_3))=A_3 | ~v1_pre_topc(A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.30/1.50  tff(c_778, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')))=k6_tmap_1('#skF_1', '#skF_2') | ~v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_750, c_8])).
% 3.30/1.50  tff(c_801, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')))=k6_tmap_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_734, c_742, c_778])).
% 3.30/1.50  tff(c_847, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_843, c_801])).
% 3.30/1.50  tff(c_912, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_910, c_847])).
% 3.30/1.50  tff(c_919, plain, $false, inference(negUnitSimplification, [status(thm)], [c_682, c_912])).
% 3.30/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.50  
% 3.30/1.50  Inference rules
% 3.30/1.50  ----------------------
% 3.30/1.50  #Ref     : 0
% 3.30/1.50  #Sup     : 151
% 3.30/1.50  #Fact    : 0
% 3.30/1.50  #Define  : 0
% 3.30/1.50  #Split   : 10
% 3.30/1.50  #Chain   : 0
% 3.30/1.50  #Close   : 0
% 3.30/1.50  
% 3.30/1.50  Ordering : KBO
% 3.30/1.50  
% 3.30/1.50  Simplification rules
% 3.30/1.50  ----------------------
% 3.30/1.50  #Subsume      : 13
% 3.30/1.50  #Demod        : 310
% 3.30/1.50  #Tautology    : 82
% 3.30/1.50  #SimpNegUnit  : 36
% 3.30/1.50  #BackRed      : 25
% 3.30/1.50  
% 3.30/1.50  #Partial instantiations: 0
% 3.30/1.50  #Strategies tried      : 1
% 3.30/1.50  
% 3.30/1.50  Timing (in seconds)
% 3.30/1.50  ----------------------
% 3.30/1.50  Preprocessing        : 0.34
% 3.30/1.50  Parsing              : 0.18
% 3.30/1.50  CNF conversion       : 0.02
% 3.30/1.50  Main loop            : 0.38
% 3.30/1.50  Inferencing          : 0.13
% 3.30/1.50  Reduction            : 0.14
% 3.30/1.50  Demodulation         : 0.10
% 3.30/1.50  BG Simplification    : 0.02
% 3.30/1.50  Subsumption          : 0.06
% 3.30/1.50  Abstraction          : 0.02
% 3.30/1.50  MUC search           : 0.00
% 3.30/1.50  Cooper               : 0.00
% 3.30/1.50  Total                : 0.77
% 3.30/1.50  Index Insertion      : 0.00
% 3.30/1.50  Index Deletion       : 0.00
% 3.30/1.50  Index Matching       : 0.00
% 3.30/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
