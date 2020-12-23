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
% DateTime   : Thu Dec  3 10:29:09 EST 2020

% Result     : Theorem 17.84s
% Output     : CNFRefutation 17.94s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 153 expanded)
%              Number of leaves         :   29 (  65 expanded)
%              Depth                    :   12
%              Number of atoms          :  170 ( 313 expanded)
%              Number of equality atoms :   18 (  38 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_36,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_46,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v2_tex_2(B,A)
                    | v2_tex_2(C,A) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tex_2)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_tarski(C,B)
                  & v2_tex_2(B,A) )
               => v2_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tex_2)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_19608,plain,(
    ! [A_407,B_408] : k4_xboole_0(A_407,k4_xboole_0(A_407,B_408)) = k3_xboole_0(A_407,B_408) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_19617,plain,(
    ! [A_407,B_408] : r1_tarski(k3_xboole_0(A_407,B_408),A_407) ),
    inference(superposition,[status(thm),theory(equality)],[c_19608,c_8])).

tff(c_12,plain,(
    ! [B_11,A_10] : k2_tarski(B_11,A_10) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_93,plain,(
    ! [A_42,B_43] : k1_setfam_1(k2_tarski(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_108,plain,(
    ! [B_44,A_45] : k1_setfam_1(k2_tarski(B_44,A_45)) = k3_xboole_0(A_45,B_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_93])).

tff(c_18,plain,(
    ! [A_17,B_18] : k1_setfam_1(k2_tarski(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_114,plain,(
    ! [B_44,A_45] : k3_xboole_0(B_44,A_45) = k3_xboole_0(A_45,B_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_18])).

tff(c_10,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_28,plain,
    ( v2_tex_2('#skF_4','#skF_2')
    | v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_36,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_34,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_70,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | ~ m1_subset_1(A_36,k1_zfmisc_1(B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_78,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_70])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_208,plain,(
    ! [C_59,B_60,A_61] :
      ( r2_hidden(C_59,B_60)
      | ~ r2_hidden(C_59,A_61)
      | ~ r1_tarski(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_349,plain,(
    ! [A_79,B_80,B_81] :
      ( r2_hidden('#skF_1'(A_79,B_80),B_81)
      | ~ r1_tarski(A_79,B_81)
      | r1_tarski(A_79,B_80) ) ),
    inference(resolution,[status(thm)],[c_6,c_208])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1332,plain,(
    ! [A_117,B_118,B_119,B_120] :
      ( r2_hidden('#skF_1'(A_117,B_118),B_119)
      | ~ r1_tarski(B_120,B_119)
      | ~ r1_tarski(A_117,B_120)
      | r1_tarski(A_117,B_118) ) ),
    inference(resolution,[status(thm)],[c_349,c_2])).

tff(c_1357,plain,(
    ! [A_121,B_122] :
      ( r2_hidden('#skF_1'(A_121,B_122),u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_121,'#skF_3')
      | r1_tarski(A_121,B_122) ) ),
    inference(resolution,[status(thm)],[c_78,c_1332])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1365,plain,(
    ! [A_121] :
      ( ~ r1_tarski(A_121,'#skF_3')
      | r1_tarski(A_121,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_1357,c_4])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_329,plain,(
    ! [C_76,A_77,B_78] :
      ( v2_tex_2(C_76,A_77)
      | ~ v2_tex_2(B_78,A_77)
      | ~ r1_tarski(C_76,B_78)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_603,plain,(
    ! [A_98,B_99,A_100] :
      ( v2_tex_2(k4_xboole_0(A_98,B_99),A_100)
      | ~ v2_tex_2(A_98,A_100)
      | ~ m1_subset_1(k4_xboole_0(A_98,B_99),k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ m1_subset_1(A_98,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(resolution,[status(thm)],[c_8,c_329])).

tff(c_1537,plain,(
    ! [A_131,B_132,A_133] :
      ( v2_tex_2(k4_xboole_0(A_131,B_132),A_133)
      | ~ v2_tex_2(A_131,A_133)
      | ~ m1_subset_1(A_131,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_pre_topc(A_133)
      | ~ r1_tarski(k4_xboole_0(A_131,B_132),u1_struct_0(A_133)) ) ),
    inference(resolution,[status(thm)],[c_22,c_603])).

tff(c_1541,plain,(
    ! [A_131,B_132] :
      ( v2_tex_2(k4_xboole_0(A_131,B_132),'#skF_2')
      | ~ v2_tex_2(A_131,'#skF_2')
      | ~ m1_subset_1(A_131,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(k4_xboole_0(A_131,B_132),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1365,c_1537])).

tff(c_19369,plain,(
    ! [A_389,B_390] :
      ( v2_tex_2(k4_xboole_0(A_389,B_390),'#skF_2')
      | ~ v2_tex_2(A_389,'#skF_2')
      | ~ m1_subset_1(A_389,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski(k4_xboole_0(A_389,B_390),'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1541])).

tff(c_19376,plain,(
    ! [B_390] :
      ( v2_tex_2(k4_xboole_0('#skF_3',B_390),'#skF_2')
      | ~ v2_tex_2('#skF_3','#skF_2')
      | ~ r1_tarski(k4_xboole_0('#skF_3',B_390),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_19369])).

tff(c_19382,plain,(
    ! [B_391] : v2_tex_2(k4_xboole_0('#skF_3',B_391),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_36,c_19376])).

tff(c_19427,plain,(
    ! [B_392] : v2_tex_2(k3_xboole_0('#skF_3',B_392),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_19382])).

tff(c_19463,plain,(
    ! [B_44] : v2_tex_2(k3_xboole_0(B_44,'#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_19427])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_269,plain,(
    ! [A_66,B_67,C_68] :
      ( k9_subset_1(A_66,B_67,C_68) = k3_xboole_0(B_67,C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(A_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_277,plain,(
    ! [B_67] : k9_subset_1(u1_struct_0('#skF_2'),B_67,'#skF_4') = k3_xboole_0(B_67,'#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_269])).

tff(c_26,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0('#skF_2'),'#skF_3','#skF_4'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_279,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_26])).

tff(c_280,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_279])).

tff(c_19478,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19463,c_280])).

tff(c_19479,plain,(
    v2_tex_2('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_19515,plain,(
    ! [A_397,B_398] :
      ( r1_tarski(A_397,B_398)
      | ~ m1_subset_1(A_397,k1_zfmisc_1(B_398)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_19526,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_19515])).

tff(c_19652,plain,(
    ! [C_418,B_419,A_420] :
      ( r2_hidden(C_418,B_419)
      | ~ r2_hidden(C_418,A_420)
      | ~ r1_tarski(A_420,B_419) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_19792,plain,(
    ! [A_438,B_439,B_440] :
      ( r2_hidden('#skF_1'(A_438,B_439),B_440)
      | ~ r1_tarski(A_438,B_440)
      | r1_tarski(A_438,B_439) ) ),
    inference(resolution,[status(thm)],[c_6,c_19652])).

tff(c_20777,plain,(
    ! [A_476,B_477,B_478,B_479] :
      ( r2_hidden('#skF_1'(A_476,B_477),B_478)
      | ~ r1_tarski(B_479,B_478)
      | ~ r1_tarski(A_476,B_479)
      | r1_tarski(A_476,B_477) ) ),
    inference(resolution,[status(thm)],[c_19792,c_2])).

tff(c_20974,plain,(
    ! [A_488,B_489] :
      ( r2_hidden('#skF_1'(A_488,B_489),u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_488,'#skF_4')
      | r1_tarski(A_488,B_489) ) ),
    inference(resolution,[status(thm)],[c_19526,c_20777])).

tff(c_20982,plain,(
    ! [A_488] :
      ( ~ r1_tarski(A_488,'#skF_4')
      | r1_tarski(A_488,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_20974,c_4])).

tff(c_19686,plain,(
    ! [C_426,A_427,B_428] :
      ( v2_tex_2(C_426,A_427)
      | ~ v2_tex_2(B_428,A_427)
      | ~ r1_tarski(C_426,B_428)
      | ~ m1_subset_1(C_426,k1_zfmisc_1(u1_struct_0(A_427)))
      | ~ m1_subset_1(B_428,k1_zfmisc_1(u1_struct_0(A_427)))
      | ~ l1_pre_topc(A_427) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20048,plain,(
    ! [A_457,B_458,A_459] :
      ( v2_tex_2(k4_xboole_0(A_457,B_458),A_459)
      | ~ v2_tex_2(A_457,A_459)
      | ~ m1_subset_1(k4_xboole_0(A_457,B_458),k1_zfmisc_1(u1_struct_0(A_459)))
      | ~ m1_subset_1(A_457,k1_zfmisc_1(u1_struct_0(A_459)))
      | ~ l1_pre_topc(A_459) ) ),
    inference(resolution,[status(thm)],[c_8,c_19686])).

tff(c_21001,plain,(
    ! [A_491,B_492,A_493] :
      ( v2_tex_2(k4_xboole_0(A_491,B_492),A_493)
      | ~ v2_tex_2(A_491,A_493)
      | ~ m1_subset_1(A_491,k1_zfmisc_1(u1_struct_0(A_493)))
      | ~ l1_pre_topc(A_493)
      | ~ r1_tarski(k4_xboole_0(A_491,B_492),u1_struct_0(A_493)) ) ),
    inference(resolution,[status(thm)],[c_22,c_20048])).

tff(c_21021,plain,(
    ! [A_8,B_9,A_493] :
      ( v2_tex_2(k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)),A_493)
      | ~ v2_tex_2(A_8,A_493)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(u1_struct_0(A_493)))
      | ~ l1_pre_topc(A_493)
      | ~ r1_tarski(k3_xboole_0(A_8,B_9),u1_struct_0(A_493)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_21001])).

tff(c_23934,plain,(
    ! [A_619,B_620,A_621] :
      ( v2_tex_2(k3_xboole_0(A_619,B_620),A_621)
      | ~ v2_tex_2(A_619,A_621)
      | ~ m1_subset_1(A_619,k1_zfmisc_1(u1_struct_0(A_621)))
      | ~ l1_pre_topc(A_621)
      | ~ r1_tarski(k3_xboole_0(A_619,B_620),u1_struct_0(A_621)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_21021])).

tff(c_23950,plain,(
    ! [A_619,B_620] :
      ( v2_tex_2(k3_xboole_0(A_619,B_620),'#skF_2')
      | ~ v2_tex_2(A_619,'#skF_2')
      | ~ m1_subset_1(A_619,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(k3_xboole_0(A_619,B_620),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_20982,c_23934])).

tff(c_35622,plain,(
    ! [A_747,B_748] :
      ( v2_tex_2(k3_xboole_0(A_747,B_748),'#skF_2')
      | ~ v2_tex_2(A_747,'#skF_2')
      | ~ m1_subset_1(A_747,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski(k3_xboole_0(A_747,B_748),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_23950])).

tff(c_35627,plain,(
    ! [B_748] :
      ( v2_tex_2(k3_xboole_0('#skF_4',B_748),'#skF_2')
      | ~ v2_tex_2('#skF_4','#skF_2')
      | ~ r1_tarski(k3_xboole_0('#skF_4',B_748),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_35622])).

tff(c_35633,plain,(
    ! [B_748] : v2_tex_2(k3_xboole_0('#skF_4',B_748),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19617,c_19479,c_35627])).

tff(c_19528,plain,(
    ! [A_399,B_400] : k1_setfam_1(k2_tarski(A_399,B_400)) = k3_xboole_0(A_399,B_400) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_19552,plain,(
    ! [B_403,A_404] : k1_setfam_1(k2_tarski(B_403,A_404)) = k3_xboole_0(A_404,B_403) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_19528])).

tff(c_19558,plain,(
    ! [B_403,A_404] : k3_xboole_0(B_403,A_404) = k3_xboole_0(A_404,B_403) ),
    inference(superposition,[status(thm),theory(equality)],[c_19552,c_18])).

tff(c_19656,plain,(
    ! [A_421,B_422,C_423] :
      ( k9_subset_1(A_421,B_422,C_423) = k3_xboole_0(B_422,C_423)
      | ~ m1_subset_1(C_423,k1_zfmisc_1(A_421)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_19664,plain,(
    ! [B_422] : k9_subset_1(u1_struct_0('#skF_2'),B_422,'#skF_4') = k3_xboole_0(B_422,'#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_19656])).

tff(c_19666,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19664,c_26])).

tff(c_19667,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19558,c_19666])).

tff(c_35637,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_35633,c_19667])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:19:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.84/9.02  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.84/9.02  
% 17.84/9.02  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.84/9.03  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 17.84/9.03  
% 17.84/9.03  %Foreground sorts:
% 17.84/9.03  
% 17.84/9.03  
% 17.84/9.03  %Background operators:
% 17.84/9.03  
% 17.84/9.03  
% 17.84/9.03  %Foreground operators:
% 17.84/9.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.84/9.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.84/9.03  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 17.84/9.03  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 17.84/9.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.84/9.03  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 17.84/9.03  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 17.84/9.03  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 17.84/9.03  tff('#skF_2', type, '#skF_2': $i).
% 17.84/9.03  tff('#skF_3', type, '#skF_3': $i).
% 17.84/9.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 17.84/9.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.84/9.03  tff('#skF_4', type, '#skF_4': $i).
% 17.84/9.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.84/9.03  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 17.84/9.03  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 17.84/9.03  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 17.84/9.03  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 17.84/9.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 17.84/9.03  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 17.84/9.03  
% 17.94/9.04  tff(f_36, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 17.94/9.04  tff(f_34, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 17.94/9.04  tff(f_38, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 17.94/9.04  tff(f_46, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 17.94/9.04  tff(f_79, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(B, A) | v2_tex_2(C, A)) => v2_tex_2(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tex_2)).
% 17.94/9.04  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 17.94/9.04  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 17.94/9.04  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_tex_2)).
% 17.94/9.04  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 17.94/9.04  tff(c_19608, plain, (![A_407, B_408]: (k4_xboole_0(A_407, k4_xboole_0(A_407, B_408))=k3_xboole_0(A_407, B_408))), inference(cnfTransformation, [status(thm)], [f_36])).
% 17.94/9.04  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 17.94/9.04  tff(c_19617, plain, (![A_407, B_408]: (r1_tarski(k3_xboole_0(A_407, B_408), A_407))), inference(superposition, [status(thm), theory('equality')], [c_19608, c_8])).
% 17.94/9.04  tff(c_12, plain, (![B_11, A_10]: (k2_tarski(B_11, A_10)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_38])).
% 17.94/9.04  tff(c_93, plain, (![A_42, B_43]: (k1_setfam_1(k2_tarski(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_46])).
% 17.94/9.04  tff(c_108, plain, (![B_44, A_45]: (k1_setfam_1(k2_tarski(B_44, A_45))=k3_xboole_0(A_45, B_44))), inference(superposition, [status(thm), theory('equality')], [c_12, c_93])).
% 17.94/9.04  tff(c_18, plain, (![A_17, B_18]: (k1_setfam_1(k2_tarski(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_46])).
% 17.94/9.04  tff(c_114, plain, (![B_44, A_45]: (k3_xboole_0(B_44, A_45)=k3_xboole_0(A_45, B_44))), inference(superposition, [status(thm), theory('equality')], [c_108, c_18])).
% 17.94/9.04  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_36])).
% 17.94/9.04  tff(c_28, plain, (v2_tex_2('#skF_4', '#skF_2') | v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 17.94/9.04  tff(c_36, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_28])).
% 17.94/9.04  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 17.94/9.04  tff(c_34, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 17.94/9.04  tff(c_70, plain, (![A_36, B_37]: (r1_tarski(A_36, B_37) | ~m1_subset_1(A_36, k1_zfmisc_1(B_37)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 17.94/9.04  tff(c_78, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_70])).
% 17.94/9.04  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.94/9.04  tff(c_208, plain, (![C_59, B_60, A_61]: (r2_hidden(C_59, B_60) | ~r2_hidden(C_59, A_61) | ~r1_tarski(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.94/9.04  tff(c_349, plain, (![A_79, B_80, B_81]: (r2_hidden('#skF_1'(A_79, B_80), B_81) | ~r1_tarski(A_79, B_81) | r1_tarski(A_79, B_80))), inference(resolution, [status(thm)], [c_6, c_208])).
% 17.94/9.04  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.94/9.04  tff(c_1332, plain, (![A_117, B_118, B_119, B_120]: (r2_hidden('#skF_1'(A_117, B_118), B_119) | ~r1_tarski(B_120, B_119) | ~r1_tarski(A_117, B_120) | r1_tarski(A_117, B_118))), inference(resolution, [status(thm)], [c_349, c_2])).
% 17.94/9.04  tff(c_1357, plain, (![A_121, B_122]: (r2_hidden('#skF_1'(A_121, B_122), u1_struct_0('#skF_2')) | ~r1_tarski(A_121, '#skF_3') | r1_tarski(A_121, B_122))), inference(resolution, [status(thm)], [c_78, c_1332])).
% 17.94/9.04  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.94/9.04  tff(c_1365, plain, (![A_121]: (~r1_tarski(A_121, '#skF_3') | r1_tarski(A_121, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_1357, c_4])).
% 17.94/9.04  tff(c_22, plain, (![A_19, B_20]: (m1_subset_1(A_19, k1_zfmisc_1(B_20)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_50])).
% 17.94/9.04  tff(c_329, plain, (![C_76, A_77, B_78]: (v2_tex_2(C_76, A_77) | ~v2_tex_2(B_78, A_77) | ~r1_tarski(C_76, B_78) | ~m1_subset_1(C_76, k1_zfmisc_1(u1_struct_0(A_77))) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_64])).
% 17.94/9.04  tff(c_603, plain, (![A_98, B_99, A_100]: (v2_tex_2(k4_xboole_0(A_98, B_99), A_100) | ~v2_tex_2(A_98, A_100) | ~m1_subset_1(k4_xboole_0(A_98, B_99), k1_zfmisc_1(u1_struct_0(A_100))) | ~m1_subset_1(A_98, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100))), inference(resolution, [status(thm)], [c_8, c_329])).
% 17.94/9.04  tff(c_1537, plain, (![A_131, B_132, A_133]: (v2_tex_2(k4_xboole_0(A_131, B_132), A_133) | ~v2_tex_2(A_131, A_133) | ~m1_subset_1(A_131, k1_zfmisc_1(u1_struct_0(A_133))) | ~l1_pre_topc(A_133) | ~r1_tarski(k4_xboole_0(A_131, B_132), u1_struct_0(A_133)))), inference(resolution, [status(thm)], [c_22, c_603])).
% 17.94/9.04  tff(c_1541, plain, (![A_131, B_132]: (v2_tex_2(k4_xboole_0(A_131, B_132), '#skF_2') | ~v2_tex_2(A_131, '#skF_2') | ~m1_subset_1(A_131, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~r1_tarski(k4_xboole_0(A_131, B_132), '#skF_3'))), inference(resolution, [status(thm)], [c_1365, c_1537])).
% 17.94/9.04  tff(c_19369, plain, (![A_389, B_390]: (v2_tex_2(k4_xboole_0(A_389, B_390), '#skF_2') | ~v2_tex_2(A_389, '#skF_2') | ~m1_subset_1(A_389, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski(k4_xboole_0(A_389, B_390), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1541])).
% 17.94/9.04  tff(c_19376, plain, (![B_390]: (v2_tex_2(k4_xboole_0('#skF_3', B_390), '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~r1_tarski(k4_xboole_0('#skF_3', B_390), '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_19369])).
% 17.94/9.04  tff(c_19382, plain, (![B_391]: (v2_tex_2(k4_xboole_0('#skF_3', B_391), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_36, c_19376])).
% 17.94/9.04  tff(c_19427, plain, (![B_392]: (v2_tex_2(k3_xboole_0('#skF_3', B_392), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_10, c_19382])).
% 17.94/9.04  tff(c_19463, plain, (![B_44]: (v2_tex_2(k3_xboole_0(B_44, '#skF_3'), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_114, c_19427])).
% 17.94/9.04  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 17.94/9.04  tff(c_269, plain, (![A_66, B_67, C_68]: (k9_subset_1(A_66, B_67, C_68)=k3_xboole_0(B_67, C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 17.94/9.04  tff(c_277, plain, (![B_67]: (k9_subset_1(u1_struct_0('#skF_2'), B_67, '#skF_4')=k3_xboole_0(B_67, '#skF_4'))), inference(resolution, [status(thm)], [c_30, c_269])).
% 17.94/9.04  tff(c_26, plain, (~v2_tex_2(k9_subset_1(u1_struct_0('#skF_2'), '#skF_3', '#skF_4'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 17.94/9.04  tff(c_279, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_277, c_26])).
% 17.94/9.04  tff(c_280, plain, (~v2_tex_2(k3_xboole_0('#skF_4', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_279])).
% 17.94/9.04  tff(c_19478, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19463, c_280])).
% 17.94/9.04  tff(c_19479, plain, (v2_tex_2('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_28])).
% 17.94/9.04  tff(c_19515, plain, (![A_397, B_398]: (r1_tarski(A_397, B_398) | ~m1_subset_1(A_397, k1_zfmisc_1(B_398)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 17.94/9.04  tff(c_19526, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_19515])).
% 17.94/9.04  tff(c_19652, plain, (![C_418, B_419, A_420]: (r2_hidden(C_418, B_419) | ~r2_hidden(C_418, A_420) | ~r1_tarski(A_420, B_419))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.94/9.04  tff(c_19792, plain, (![A_438, B_439, B_440]: (r2_hidden('#skF_1'(A_438, B_439), B_440) | ~r1_tarski(A_438, B_440) | r1_tarski(A_438, B_439))), inference(resolution, [status(thm)], [c_6, c_19652])).
% 17.94/9.04  tff(c_20777, plain, (![A_476, B_477, B_478, B_479]: (r2_hidden('#skF_1'(A_476, B_477), B_478) | ~r1_tarski(B_479, B_478) | ~r1_tarski(A_476, B_479) | r1_tarski(A_476, B_477))), inference(resolution, [status(thm)], [c_19792, c_2])).
% 17.94/9.04  tff(c_20974, plain, (![A_488, B_489]: (r2_hidden('#skF_1'(A_488, B_489), u1_struct_0('#skF_2')) | ~r1_tarski(A_488, '#skF_4') | r1_tarski(A_488, B_489))), inference(resolution, [status(thm)], [c_19526, c_20777])).
% 17.94/9.04  tff(c_20982, plain, (![A_488]: (~r1_tarski(A_488, '#skF_4') | r1_tarski(A_488, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_20974, c_4])).
% 17.94/9.04  tff(c_19686, plain, (![C_426, A_427, B_428]: (v2_tex_2(C_426, A_427) | ~v2_tex_2(B_428, A_427) | ~r1_tarski(C_426, B_428) | ~m1_subset_1(C_426, k1_zfmisc_1(u1_struct_0(A_427))) | ~m1_subset_1(B_428, k1_zfmisc_1(u1_struct_0(A_427))) | ~l1_pre_topc(A_427))), inference(cnfTransformation, [status(thm)], [f_64])).
% 17.94/9.04  tff(c_20048, plain, (![A_457, B_458, A_459]: (v2_tex_2(k4_xboole_0(A_457, B_458), A_459) | ~v2_tex_2(A_457, A_459) | ~m1_subset_1(k4_xboole_0(A_457, B_458), k1_zfmisc_1(u1_struct_0(A_459))) | ~m1_subset_1(A_457, k1_zfmisc_1(u1_struct_0(A_459))) | ~l1_pre_topc(A_459))), inference(resolution, [status(thm)], [c_8, c_19686])).
% 17.94/9.04  tff(c_21001, plain, (![A_491, B_492, A_493]: (v2_tex_2(k4_xboole_0(A_491, B_492), A_493) | ~v2_tex_2(A_491, A_493) | ~m1_subset_1(A_491, k1_zfmisc_1(u1_struct_0(A_493))) | ~l1_pre_topc(A_493) | ~r1_tarski(k4_xboole_0(A_491, B_492), u1_struct_0(A_493)))), inference(resolution, [status(thm)], [c_22, c_20048])).
% 17.94/9.04  tff(c_21021, plain, (![A_8, B_9, A_493]: (v2_tex_2(k4_xboole_0(A_8, k4_xboole_0(A_8, B_9)), A_493) | ~v2_tex_2(A_8, A_493) | ~m1_subset_1(A_8, k1_zfmisc_1(u1_struct_0(A_493))) | ~l1_pre_topc(A_493) | ~r1_tarski(k3_xboole_0(A_8, B_9), u1_struct_0(A_493)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_21001])).
% 17.94/9.04  tff(c_23934, plain, (![A_619, B_620, A_621]: (v2_tex_2(k3_xboole_0(A_619, B_620), A_621) | ~v2_tex_2(A_619, A_621) | ~m1_subset_1(A_619, k1_zfmisc_1(u1_struct_0(A_621))) | ~l1_pre_topc(A_621) | ~r1_tarski(k3_xboole_0(A_619, B_620), u1_struct_0(A_621)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_21021])).
% 17.94/9.04  tff(c_23950, plain, (![A_619, B_620]: (v2_tex_2(k3_xboole_0(A_619, B_620), '#skF_2') | ~v2_tex_2(A_619, '#skF_2') | ~m1_subset_1(A_619, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~r1_tarski(k3_xboole_0(A_619, B_620), '#skF_4'))), inference(resolution, [status(thm)], [c_20982, c_23934])).
% 17.94/9.04  tff(c_35622, plain, (![A_747, B_748]: (v2_tex_2(k3_xboole_0(A_747, B_748), '#skF_2') | ~v2_tex_2(A_747, '#skF_2') | ~m1_subset_1(A_747, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski(k3_xboole_0(A_747, B_748), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_23950])).
% 17.94/9.04  tff(c_35627, plain, (![B_748]: (v2_tex_2(k3_xboole_0('#skF_4', B_748), '#skF_2') | ~v2_tex_2('#skF_4', '#skF_2') | ~r1_tarski(k3_xboole_0('#skF_4', B_748), '#skF_4'))), inference(resolution, [status(thm)], [c_30, c_35622])).
% 17.94/9.04  tff(c_35633, plain, (![B_748]: (v2_tex_2(k3_xboole_0('#skF_4', B_748), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_19617, c_19479, c_35627])).
% 17.94/9.04  tff(c_19528, plain, (![A_399, B_400]: (k1_setfam_1(k2_tarski(A_399, B_400))=k3_xboole_0(A_399, B_400))), inference(cnfTransformation, [status(thm)], [f_46])).
% 17.94/9.04  tff(c_19552, plain, (![B_403, A_404]: (k1_setfam_1(k2_tarski(B_403, A_404))=k3_xboole_0(A_404, B_403))), inference(superposition, [status(thm), theory('equality')], [c_12, c_19528])).
% 17.94/9.04  tff(c_19558, plain, (![B_403, A_404]: (k3_xboole_0(B_403, A_404)=k3_xboole_0(A_404, B_403))), inference(superposition, [status(thm), theory('equality')], [c_19552, c_18])).
% 17.94/9.04  tff(c_19656, plain, (![A_421, B_422, C_423]: (k9_subset_1(A_421, B_422, C_423)=k3_xboole_0(B_422, C_423) | ~m1_subset_1(C_423, k1_zfmisc_1(A_421)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 17.94/9.04  tff(c_19664, plain, (![B_422]: (k9_subset_1(u1_struct_0('#skF_2'), B_422, '#skF_4')=k3_xboole_0(B_422, '#skF_4'))), inference(resolution, [status(thm)], [c_30, c_19656])).
% 17.94/9.04  tff(c_19666, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_19664, c_26])).
% 17.94/9.04  tff(c_19667, plain, (~v2_tex_2(k3_xboole_0('#skF_4', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_19558, c_19666])).
% 17.94/9.04  tff(c_35637, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_35633, c_19667])).
% 17.94/9.04  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.94/9.04  
% 17.94/9.04  Inference rules
% 17.94/9.04  ----------------------
% 17.94/9.04  #Ref     : 0
% 17.94/9.04  #Sup     : 10091
% 17.94/9.04  #Fact    : 0
% 17.94/9.04  #Define  : 0
% 17.94/9.04  #Split   : 6
% 17.94/9.04  #Chain   : 0
% 17.94/9.04  #Close   : 0
% 17.94/9.04  
% 17.94/9.04  Ordering : KBO
% 17.94/9.04  
% 17.94/9.04  Simplification rules
% 17.94/9.04  ----------------------
% 17.94/9.04  #Subsume      : 1283
% 17.94/9.04  #Demod        : 2092
% 17.94/9.04  #Tautology    : 1630
% 17.94/9.04  #SimpNegUnit  : 5
% 17.94/9.04  #BackRed      : 4
% 17.94/9.04  
% 17.94/9.04  #Partial instantiations: 0
% 17.94/9.04  #Strategies tried      : 1
% 17.94/9.04  
% 17.94/9.04  Timing (in seconds)
% 17.94/9.04  ----------------------
% 17.94/9.05  Preprocessing        : 0.30
% 17.94/9.05  Parsing              : 0.16
% 17.94/9.05  CNF conversion       : 0.02
% 17.94/9.05  Main loop            : 7.97
% 17.94/9.05  Inferencing          : 1.34
% 17.94/9.05  Reduction            : 5.15
% 17.94/9.05  Demodulation         : 4.86
% 17.94/9.05  BG Simplification    : 0.25
% 17.94/9.05  Subsumption          : 0.98
% 17.94/9.05  Abstraction          : 0.28
% 17.94/9.05  MUC search           : 0.00
% 17.94/9.05  Cooper               : 0.00
% 17.94/9.05  Total                : 8.30
% 17.94/9.05  Index Insertion      : 0.00
% 17.94/9.05  Index Deletion       : 0.00
% 17.94/9.05  Index Matching       : 0.00
% 17.94/9.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
