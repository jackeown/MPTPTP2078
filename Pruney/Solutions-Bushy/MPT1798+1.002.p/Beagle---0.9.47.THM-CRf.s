%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1798+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:25 EST 2020

% Result     : Theorem 34.69s
% Output     : CNFRefutation 34.69s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 645 expanded)
%              Number of leaves         :   28 ( 229 expanded)
%              Depth                    :   16
%              Number of atoms          :  553 (2814 expanded)
%              Number of equality atoms :  117 ( 735 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k8_tmap_1 > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k8_tmap_1,type,(
    k8_tmap_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_tmap_1,type,(
    k6_tmap_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_tmap_1,type,(
    k5_tmap_1: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_133,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ( u1_struct_0(k8_tmap_1(A,B)) = u1_struct_0(A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( C = u1_struct_0(B)
                   => u1_pre_topc(k8_tmap_1(A,B)) = k5_tmap_1(A,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_tmap_1)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( ( v1_pre_topc(C)
                & v2_pre_topc(C)
                & l1_pre_topc(C) )
             => ( C = k8_tmap_1(A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( D = u1_struct_0(B)
                     => C = k6_tmap_1(A,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_tmap_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k5_tmap_1(A,B),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_tmap_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k6_tmap_1(A,B) = g1_pre_topc(u1_struct_0(A),k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_tmap_1)).

tff(f_30,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_103,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_32,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_28,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_34,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_26,plain,(
    ! [B_39,A_37] :
      ( m1_subset_1(u1_struct_0(B_39),k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ m1_pre_topc(B_39,A_37)
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_84,plain,(
    ! [A_63,B_64] :
      ( l1_pre_topc(k6_tmap_1(A_63,B_64))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63)
      | ~ v2_pre_topc(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_88,plain,(
    ! [A_37,B_39] :
      ( l1_pre_topc(k6_tmap_1(A_37,u1_struct_0(B_39)))
      | ~ v2_pre_topc(A_37)
      | v2_struct_0(A_37)
      | ~ m1_pre_topc(B_39,A_37)
      | ~ l1_pre_topc(A_37) ) ),
    inference(resolution,[status(thm)],[c_26,c_84])).

tff(c_78,plain,(
    ! [A_59,B_60] :
      ( v1_pre_topc(k6_tmap_1(A_59,B_60))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59)
      | ~ v2_pre_topc(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_82,plain,(
    ! [A_37,B_39] :
      ( v1_pre_topc(k6_tmap_1(A_37,u1_struct_0(B_39)))
      | ~ v2_pre_topc(A_37)
      | v2_struct_0(A_37)
      | ~ m1_pre_topc(B_39,A_37)
      | ~ l1_pre_topc(A_37) ) ),
    inference(resolution,[status(thm)],[c_26,c_78])).

tff(c_72,plain,(
    ! [A_55,B_56] :
      ( v2_pre_topc(k6_tmap_1(A_55,B_56))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_pre_topc(A_55)
      | ~ v2_pre_topc(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_76,plain,(
    ! [A_37,B_39] :
      ( v2_pre_topc(k6_tmap_1(A_37,u1_struct_0(B_39)))
      | ~ v2_pre_topc(A_37)
      | v2_struct_0(A_37)
      | ~ m1_pre_topc(B_39,A_37)
      | ~ l1_pre_topc(A_37) ) ),
    inference(resolution,[status(thm)],[c_26,c_72])).

tff(c_179,plain,(
    ! [B_91,A_92,C_93] :
      ( u1_struct_0(B_91) = '#skF_1'(A_92,B_91,C_93)
      | k8_tmap_1(A_92,B_91) = C_93
      | ~ l1_pre_topc(C_93)
      | ~ v2_pre_topc(C_93)
      | ~ v1_pre_topc(C_93)
      | ~ m1_pre_topc(B_91,A_92)
      | ~ l1_pre_topc(A_92)
      | ~ v2_pre_topc(A_92)
      | v2_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1001,plain,(
    ! [A_259,B_260,A_261,B_262] :
      ( '#skF_1'(A_259,B_260,k6_tmap_1(A_261,u1_struct_0(B_262))) = u1_struct_0(B_260)
      | k8_tmap_1(A_259,B_260) = k6_tmap_1(A_261,u1_struct_0(B_262))
      | ~ l1_pre_topc(k6_tmap_1(A_261,u1_struct_0(B_262)))
      | ~ v1_pre_topc(k6_tmap_1(A_261,u1_struct_0(B_262)))
      | ~ m1_pre_topc(B_260,A_259)
      | ~ l1_pre_topc(A_259)
      | ~ v2_pre_topc(A_259)
      | v2_struct_0(A_259)
      | ~ v2_pre_topc(A_261)
      | v2_struct_0(A_261)
      | ~ m1_pre_topc(B_262,A_261)
      | ~ l1_pre_topc(A_261) ) ),
    inference(resolution,[status(thm)],[c_76,c_179])).

tff(c_1013,plain,(
    ! [A_263,B_264,A_265,B_266] :
      ( '#skF_1'(A_263,B_264,k6_tmap_1(A_265,u1_struct_0(B_266))) = u1_struct_0(B_264)
      | k8_tmap_1(A_263,B_264) = k6_tmap_1(A_265,u1_struct_0(B_266))
      | ~ l1_pre_topc(k6_tmap_1(A_265,u1_struct_0(B_266)))
      | ~ m1_pre_topc(B_264,A_263)
      | ~ l1_pre_topc(A_263)
      | ~ v2_pre_topc(A_263)
      | v2_struct_0(A_263)
      | ~ v2_pre_topc(A_265)
      | v2_struct_0(A_265)
      | ~ m1_pre_topc(B_266,A_265)
      | ~ l1_pre_topc(A_265) ) ),
    inference(resolution,[status(thm)],[c_82,c_1001])).

tff(c_1025,plain,(
    ! [A_267,B_268,A_269,B_270] :
      ( '#skF_1'(A_267,B_268,k6_tmap_1(A_269,u1_struct_0(B_270))) = u1_struct_0(B_268)
      | k8_tmap_1(A_267,B_268) = k6_tmap_1(A_269,u1_struct_0(B_270))
      | ~ m1_pre_topc(B_268,A_267)
      | ~ l1_pre_topc(A_267)
      | ~ v2_pre_topc(A_267)
      | v2_struct_0(A_267)
      | ~ v2_pre_topc(A_269)
      | v2_struct_0(A_269)
      | ~ m1_pre_topc(B_270,A_269)
      | ~ l1_pre_topc(A_269) ) ),
    inference(resolution,[status(thm)],[c_88,c_1013])).

tff(c_6,plain,(
    ! [A_2,B_14,C_20] :
      ( k6_tmap_1(A_2,'#skF_1'(A_2,B_14,C_20)) != C_20
      | k8_tmap_1(A_2,B_14) = C_20
      | ~ l1_pre_topc(C_20)
      | ~ v2_pre_topc(C_20)
      | ~ v1_pre_topc(C_20)
      | ~ m1_pre_topc(B_14,A_2)
      | ~ l1_pre_topc(A_2)
      | ~ v2_pre_topc(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1054,plain,(
    ! [A_269,B_270,A_267,B_268] :
      ( k6_tmap_1(A_269,u1_struct_0(B_270)) != k6_tmap_1(A_267,u1_struct_0(B_268))
      | k8_tmap_1(A_267,B_268) = k6_tmap_1(A_269,u1_struct_0(B_270))
      | ~ l1_pre_topc(k6_tmap_1(A_269,u1_struct_0(B_270)))
      | ~ v2_pre_topc(k6_tmap_1(A_269,u1_struct_0(B_270)))
      | ~ v1_pre_topc(k6_tmap_1(A_269,u1_struct_0(B_270)))
      | ~ m1_pre_topc(B_268,A_267)
      | ~ l1_pre_topc(A_267)
      | ~ v2_pre_topc(A_267)
      | v2_struct_0(A_267)
      | k8_tmap_1(A_267,B_268) = k6_tmap_1(A_269,u1_struct_0(B_270))
      | ~ m1_pre_topc(B_268,A_267)
      | ~ l1_pre_topc(A_267)
      | ~ v2_pre_topc(A_267)
      | v2_struct_0(A_267)
      | ~ v2_pre_topc(A_269)
      | v2_struct_0(A_269)
      | ~ m1_pre_topc(B_270,A_269)
      | ~ l1_pre_topc(A_269) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1025,c_6])).

tff(c_21631,plain,(
    ! [A_1420,B_1421] :
      ( k6_tmap_1(A_1420,u1_struct_0(B_1421)) = k8_tmap_1(A_1420,B_1421)
      | ~ l1_pre_topc(k6_tmap_1(A_1420,u1_struct_0(B_1421)))
      | ~ v2_pre_topc(k6_tmap_1(A_1420,u1_struct_0(B_1421)))
      | ~ v1_pre_topc(k6_tmap_1(A_1420,u1_struct_0(B_1421)))
      | ~ m1_pre_topc(B_1421,A_1420)
      | ~ l1_pre_topc(A_1420)
      | ~ v2_pre_topc(A_1420)
      | v2_struct_0(A_1420)
      | k6_tmap_1(A_1420,u1_struct_0(B_1421)) = k8_tmap_1(A_1420,B_1421)
      | ~ m1_pre_topc(B_1421,A_1420)
      | ~ l1_pre_topc(A_1420)
      | ~ v2_pre_topc(A_1420)
      | v2_struct_0(A_1420)
      | ~ v2_pre_topc(A_1420)
      | v2_struct_0(A_1420)
      | ~ m1_pre_topc(B_1421,A_1420)
      | ~ l1_pre_topc(A_1420) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1054])).

tff(c_21956,plain,(
    ! [A_1426,B_1427] :
      ( ~ l1_pre_topc(k6_tmap_1(A_1426,u1_struct_0(B_1427)))
      | ~ v1_pre_topc(k6_tmap_1(A_1426,u1_struct_0(B_1427)))
      | k6_tmap_1(A_1426,u1_struct_0(B_1427)) = k8_tmap_1(A_1426,B_1427)
      | ~ v2_pre_topc(A_1426)
      | v2_struct_0(A_1426)
      | ~ m1_pre_topc(B_1427,A_1426)
      | ~ l1_pre_topc(A_1426) ) ),
    inference(resolution,[status(thm)],[c_76,c_21631])).

tff(c_22024,plain,(
    ! [A_1428,B_1429] :
      ( ~ l1_pre_topc(k6_tmap_1(A_1428,u1_struct_0(B_1429)))
      | k6_tmap_1(A_1428,u1_struct_0(B_1429)) = k8_tmap_1(A_1428,B_1429)
      | ~ v2_pre_topc(A_1428)
      | v2_struct_0(A_1428)
      | ~ m1_pre_topc(B_1429,A_1428)
      | ~ l1_pre_topc(A_1428) ) ),
    inference(resolution,[status(thm)],[c_82,c_21956])).

tff(c_22092,plain,(
    ! [A_1430,B_1431] :
      ( k6_tmap_1(A_1430,u1_struct_0(B_1431)) = k8_tmap_1(A_1430,B_1431)
      | ~ v2_pre_topc(A_1430)
      | v2_struct_0(A_1430)
      | ~ m1_pre_topc(B_1431,A_1430)
      | ~ l1_pre_topc(A_1430) ) ),
    inference(resolution,[status(thm)],[c_88,c_22024])).

tff(c_14,plain,(
    ! [A_27,B_28] :
      ( m1_subset_1(k5_tmap_1(A_27,B_28),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_27))))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_132,plain,(
    ! [A_83,B_84] :
      ( g1_pre_topc(u1_struct_0(A_83),k5_tmap_1(A_83,B_84)) = k6_tmap_1(A_83,B_84)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83)
      | ~ v2_pre_topc(A_83)
      | v2_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_141,plain,(
    ! [A_87,B_88] :
      ( g1_pre_topc(u1_struct_0(A_87),k5_tmap_1(A_87,u1_struct_0(B_88))) = k6_tmap_1(A_87,u1_struct_0(B_88))
      | ~ v2_pre_topc(A_87)
      | v2_struct_0(A_87)
      | ~ m1_pre_topc(B_88,A_87)
      | ~ l1_pre_topc(A_87) ) ),
    inference(resolution,[status(thm)],[c_26,c_132])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_58,plain,(
    ! [C_47,A_48,D_49,B_50] :
      ( C_47 = A_48
      | g1_pre_topc(C_47,D_49) != g1_pre_topc(A_48,B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(k1_zfmisc_1(A_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_60,plain,(
    ! [A_1,A_48,B_50] :
      ( u1_struct_0(A_1) = A_48
      | g1_pre_topc(A_48,B_50) != A_1
      | ~ m1_subset_1(B_50,k1_zfmisc_1(k1_zfmisc_1(A_48)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_58])).

tff(c_150,plain,(
    ! [A_87,A_1,B_88] :
      ( u1_struct_0(A_87) = u1_struct_0(A_1)
      | k6_tmap_1(A_87,u1_struct_0(B_88)) != A_1
      | ~ m1_subset_1(k5_tmap_1(A_87,u1_struct_0(B_88)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_87))))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_87)
      | v2_struct_0(A_87)
      | ~ m1_pre_topc(B_88,A_87)
      | ~ l1_pre_topc(A_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_60])).

tff(c_334,plain,(
    ! [A_154,B_155] :
      ( u1_struct_0(k6_tmap_1(A_154,u1_struct_0(B_155))) = u1_struct_0(A_154)
      | ~ m1_subset_1(k5_tmap_1(A_154,u1_struct_0(B_155)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_154))))
      | ~ v1_pre_topc(k6_tmap_1(A_154,u1_struct_0(B_155)))
      | ~ l1_pre_topc(k6_tmap_1(A_154,u1_struct_0(B_155)))
      | ~ v2_pre_topc(A_154)
      | v2_struct_0(A_154)
      | ~ m1_pre_topc(B_155,A_154)
      | ~ l1_pre_topc(A_154) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_150])).

tff(c_340,plain,(
    ! [A_156,B_157] :
      ( u1_struct_0(k6_tmap_1(A_156,u1_struct_0(B_157))) = u1_struct_0(A_156)
      | ~ v1_pre_topc(k6_tmap_1(A_156,u1_struct_0(B_157)))
      | ~ l1_pre_topc(k6_tmap_1(A_156,u1_struct_0(B_157)))
      | ~ m1_pre_topc(B_157,A_156)
      | ~ m1_subset_1(u1_struct_0(B_157),k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ l1_pre_topc(A_156)
      | ~ v2_pre_topc(A_156)
      | v2_struct_0(A_156) ) ),
    inference(resolution,[status(thm)],[c_14,c_334])).

tff(c_345,plain,(
    ! [A_158,B_159] :
      ( u1_struct_0(k6_tmap_1(A_158,u1_struct_0(B_159))) = u1_struct_0(A_158)
      | ~ v1_pre_topc(k6_tmap_1(A_158,u1_struct_0(B_159)))
      | ~ l1_pre_topc(k6_tmap_1(A_158,u1_struct_0(B_159)))
      | ~ v2_pre_topc(A_158)
      | v2_struct_0(A_158)
      | ~ m1_pre_topc(B_159,A_158)
      | ~ l1_pre_topc(A_158) ) ),
    inference(resolution,[status(thm)],[c_26,c_340])).

tff(c_357,plain,(
    ! [A_162,B_163] :
      ( u1_struct_0(k6_tmap_1(A_162,u1_struct_0(B_163))) = u1_struct_0(A_162)
      | ~ l1_pre_topc(k6_tmap_1(A_162,u1_struct_0(B_163)))
      | ~ v2_pre_topc(A_162)
      | v2_struct_0(A_162)
      | ~ m1_pre_topc(B_163,A_162)
      | ~ l1_pre_topc(A_162) ) ),
    inference(resolution,[status(thm)],[c_82,c_345])).

tff(c_361,plain,(
    ! [A_37,B_39] :
      ( u1_struct_0(k6_tmap_1(A_37,u1_struct_0(B_39))) = u1_struct_0(A_37)
      | ~ v2_pre_topc(A_37)
      | v2_struct_0(A_37)
      | ~ m1_pre_topc(B_39,A_37)
      | ~ l1_pre_topc(A_37) ) ),
    inference(resolution,[status(thm)],[c_88,c_357])).

tff(c_23085,plain,(
    ! [A_1442,B_1443] :
      ( u1_struct_0(k8_tmap_1(A_1442,B_1443)) = u1_struct_0(A_1442)
      | ~ v2_pre_topc(A_1442)
      | v2_struct_0(A_1442)
      | ~ m1_pre_topc(B_1443,A_1442)
      | ~ l1_pre_topc(A_1442)
      | ~ v2_pre_topc(A_1442)
      | v2_struct_0(A_1442)
      | ~ m1_pre_topc(B_1443,A_1442)
      | ~ l1_pre_topc(A_1442) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22092,c_361])).

tff(c_40,plain,
    ( u1_struct_0('#skF_3') = '#skF_4'
    | u1_struct_0(k8_tmap_1('#skF_2','#skF_3')) != u1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_43,plain,(
    u1_struct_0(k8_tmap_1('#skF_2','#skF_3')) != u1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_23966,plain,
    ( ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_23085,c_43])).

tff(c_23976,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_34,c_23966])).

tff(c_23978,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_23976])).

tff(c_23980,plain,(
    u1_struct_0(k8_tmap_1('#skF_2','#skF_3')) = u1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_38,plain,
    ( u1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) != k5_tmap_1('#skF_2','#skF_4')
    | u1_struct_0(k8_tmap_1('#skF_2','#skF_3')) != u1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_24029,plain,(
    u1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) != k5_tmap_1('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23980,c_38])).

tff(c_42,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | u1_struct_0(k8_tmap_1('#skF_2','#skF_3')) != u1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_24006,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23980,c_42])).

tff(c_25289,plain,(
    ! [A_1579,B_1580] :
      ( g1_pre_topc(u1_struct_0(A_1579),k5_tmap_1(A_1579,B_1580)) = k6_tmap_1(A_1579,B_1580)
      | ~ m1_subset_1(B_1580,k1_zfmisc_1(u1_struct_0(A_1579)))
      | ~ l1_pre_topc(A_1579)
      | ~ v2_pre_topc(A_1579)
      | v2_struct_0(A_1579) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_25299,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2','#skF_4')) = k6_tmap_1('#skF_2','#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24006,c_25289])).

tff(c_25313,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2','#skF_4')) = k6_tmap_1('#skF_2','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_25299])).

tff(c_25314,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2','#skF_4')) = k6_tmap_1('#skF_2','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_25313])).

tff(c_24,plain,(
    ! [C_35,A_31,D_36,B_32] :
      ( C_35 = A_31
      | g1_pre_topc(C_35,D_36) != g1_pre_topc(A_31,B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(k1_zfmisc_1(A_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_25331,plain,(
    ! [C_35,D_36] :
      ( u1_struct_0('#skF_2') = C_35
      | k6_tmap_1('#skF_2','#skF_4') != g1_pre_topc(C_35,D_36)
      | ~ m1_subset_1(k5_tmap_1('#skF_2','#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25314,c_24])).

tff(c_25376,plain,(
    ~ m1_subset_1(k5_tmap_1('#skF_2','#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_25331])).

tff(c_25379,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_25376])).

tff(c_25382,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_24006,c_25379])).

tff(c_25384,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_25382])).

tff(c_25386,plain,(
    m1_subset_1(k5_tmap_1('#skF_2','#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_25331])).

tff(c_24048,plain,(
    ! [A_1456,B_1457] :
      ( v1_pre_topc(k6_tmap_1(A_1456,B_1457))
      | ~ m1_subset_1(B_1457,k1_zfmisc_1(u1_struct_0(A_1456)))
      | ~ l1_pre_topc(A_1456)
      | ~ v2_pre_topc(A_1456)
      | v2_struct_0(A_1456) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_24057,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24006,c_24048])).

tff(c_24068,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_2','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_24057])).

tff(c_24069,plain,(
    v1_pre_topc(k6_tmap_1('#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_24068])).

tff(c_23979,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_25207,plain,(
    ! [A_1562,B_1563] :
      ( v2_pre_topc(k6_tmap_1(A_1562,B_1563))
      | ~ m1_subset_1(B_1563,k1_zfmisc_1(u1_struct_0(A_1562)))
      | ~ l1_pre_topc(A_1562)
      | ~ v2_pre_topc(A_1562)
      | v2_struct_0(A_1562) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_25222,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24006,c_25207])).

tff(c_25238,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_2','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_25222])).

tff(c_25239,plain,(
    v2_pre_topc(k6_tmap_1('#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_25238])).

tff(c_25148,plain,(
    ! [A_1554,B_1555] :
      ( l1_pre_topc(k6_tmap_1(A_1554,B_1555))
      | ~ m1_subset_1(B_1555,k1_zfmisc_1(u1_struct_0(A_1554)))
      | ~ l1_pre_topc(A_1554)
      | ~ v2_pre_topc(A_1554)
      | v2_struct_0(A_1554) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_25163,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24006,c_25148])).

tff(c_25179,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_25163])).

tff(c_25180,plain,(
    l1_pre_topc(k6_tmap_1('#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_25179])).

tff(c_25387,plain,(
    ! [B_1586,A_1587,C_1588] :
      ( u1_struct_0(B_1586) = '#skF_1'(A_1587,B_1586,C_1588)
      | k8_tmap_1(A_1587,B_1586) = C_1588
      | ~ l1_pre_topc(C_1588)
      | ~ v2_pre_topc(C_1588)
      | ~ v1_pre_topc(C_1588)
      | ~ m1_pre_topc(B_1586,A_1587)
      | ~ l1_pre_topc(A_1587)
      | ~ v2_pre_topc(A_1587)
      | v2_struct_0(A_1587) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_25397,plain,(
    ! [A_1587,B_1586] :
      ( '#skF_1'(A_1587,B_1586,k6_tmap_1('#skF_2','#skF_4')) = u1_struct_0(B_1586)
      | k8_tmap_1(A_1587,B_1586) = k6_tmap_1('#skF_2','#skF_4')
      | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_4'))
      | ~ v1_pre_topc(k6_tmap_1('#skF_2','#skF_4'))
      | ~ m1_pre_topc(B_1586,A_1587)
      | ~ l1_pre_topc(A_1587)
      | ~ v2_pre_topc(A_1587)
      | v2_struct_0(A_1587) ) ),
    inference(resolution,[status(thm)],[c_25239,c_25387])).

tff(c_27055,plain,(
    ! [A_1692,B_1693] :
      ( '#skF_1'(A_1692,B_1693,k6_tmap_1('#skF_2','#skF_4')) = u1_struct_0(B_1693)
      | k8_tmap_1(A_1692,B_1693) = k6_tmap_1('#skF_2','#skF_4')
      | ~ m1_pre_topc(B_1693,A_1692)
      | ~ l1_pre_topc(A_1692)
      | ~ v2_pre_topc(A_1692)
      | v2_struct_0(A_1692) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24069,c_25180,c_25397])).

tff(c_27067,plain,(
    ! [A_1692,B_1693] :
      ( k6_tmap_1(A_1692,u1_struct_0(B_1693)) != k6_tmap_1('#skF_2','#skF_4')
      | k8_tmap_1(A_1692,B_1693) = k6_tmap_1('#skF_2','#skF_4')
      | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_4'))
      | ~ v2_pre_topc(k6_tmap_1('#skF_2','#skF_4'))
      | ~ v1_pre_topc(k6_tmap_1('#skF_2','#skF_4'))
      | ~ m1_pre_topc(B_1693,A_1692)
      | ~ l1_pre_topc(A_1692)
      | ~ v2_pre_topc(A_1692)
      | v2_struct_0(A_1692)
      | k8_tmap_1(A_1692,B_1693) = k6_tmap_1('#skF_2','#skF_4')
      | ~ m1_pre_topc(B_1693,A_1692)
      | ~ l1_pre_topc(A_1692)
      | ~ v2_pre_topc(A_1692)
      | v2_struct_0(A_1692) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27055,c_6])).

tff(c_27079,plain,(
    ! [A_1694,B_1695] :
      ( k6_tmap_1(A_1694,u1_struct_0(B_1695)) != k6_tmap_1('#skF_2','#skF_4')
      | k8_tmap_1(A_1694,B_1695) = k6_tmap_1('#skF_2','#skF_4')
      | ~ m1_pre_topc(B_1695,A_1694)
      | ~ l1_pre_topc(A_1694)
      | ~ v2_pre_topc(A_1694)
      | v2_struct_0(A_1694) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24069,c_25239,c_25180,c_27067])).

tff(c_27089,plain,(
    ! [A_1696] :
      ( k6_tmap_1(A_1696,'#skF_4') != k6_tmap_1('#skF_2','#skF_4')
      | k8_tmap_1(A_1696,'#skF_3') = k6_tmap_1('#skF_2','#skF_4')
      | ~ m1_pre_topc('#skF_3',A_1696)
      | ~ l1_pre_topc(A_1696)
      | ~ v2_pre_topc(A_1696)
      | v2_struct_0(A_1696) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23979,c_27079])).

tff(c_27092,plain,
    ( k8_tmap_1('#skF_2','#skF_3') = k6_tmap_1('#skF_2','#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_27089])).

tff(c_27095,plain,
    ( k8_tmap_1('#skF_2','#skF_3') = k6_tmap_1('#skF_2','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_27092])).

tff(c_27096,plain,(
    k8_tmap_1('#skF_2','#skF_3') = k6_tmap_1('#skF_2','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_27095])).

tff(c_24091,plain,(
    ! [A_1462,B_1463] :
      ( l1_pre_topc(k6_tmap_1(A_1462,B_1463))
      | ~ m1_subset_1(B_1463,k1_zfmisc_1(u1_struct_0(A_1462)))
      | ~ l1_pre_topc(A_1462)
      | ~ v2_pre_topc(A_1462)
      | v2_struct_0(A_1462) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_24103,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24006,c_24091])).

tff(c_24115,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_24103])).

tff(c_24116,plain,(
    l1_pre_topc(k6_tmap_1('#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_24115])).

tff(c_24119,plain,(
    ! [A_1465,B_1466] :
      ( v2_pre_topc(k6_tmap_1(A_1465,B_1466))
      | ~ m1_subset_1(B_1466,k1_zfmisc_1(u1_struct_0(A_1465)))
      | ~ l1_pre_topc(A_1465)
      | ~ v2_pre_topc(A_1465)
      | v2_struct_0(A_1465) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_24131,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24006,c_24119])).

tff(c_24143,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_2','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_24131])).

tff(c_24144,plain,(
    v2_pre_topc(k6_tmap_1('#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_24143])).

tff(c_24388,plain,(
    ! [B_1501,A_1502,C_1503] :
      ( u1_struct_0(B_1501) = '#skF_1'(A_1502,B_1501,C_1503)
      | k8_tmap_1(A_1502,B_1501) = C_1503
      | ~ l1_pre_topc(C_1503)
      | ~ v2_pre_topc(C_1503)
      | ~ v1_pre_topc(C_1503)
      | ~ m1_pre_topc(B_1501,A_1502)
      | ~ l1_pre_topc(A_1502)
      | ~ v2_pre_topc(A_1502)
      | v2_struct_0(A_1502) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_24396,plain,(
    ! [A_1502,B_1501] :
      ( '#skF_1'(A_1502,B_1501,k6_tmap_1('#skF_2','#skF_4')) = u1_struct_0(B_1501)
      | k8_tmap_1(A_1502,B_1501) = k6_tmap_1('#skF_2','#skF_4')
      | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_4'))
      | ~ v1_pre_topc(k6_tmap_1('#skF_2','#skF_4'))
      | ~ m1_pre_topc(B_1501,A_1502)
      | ~ l1_pre_topc(A_1502)
      | ~ v2_pre_topc(A_1502)
      | v2_struct_0(A_1502) ) ),
    inference(resolution,[status(thm)],[c_24144,c_24388])).

tff(c_25067,plain,(
    ! [A_1547,B_1548] :
      ( '#skF_1'(A_1547,B_1548,k6_tmap_1('#skF_2','#skF_4')) = u1_struct_0(B_1548)
      | k8_tmap_1(A_1547,B_1548) = k6_tmap_1('#skF_2','#skF_4')
      | ~ m1_pre_topc(B_1548,A_1547)
      | ~ l1_pre_topc(A_1547)
      | ~ v2_pre_topc(A_1547)
      | v2_struct_0(A_1547) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24069,c_24116,c_24396])).

tff(c_25079,plain,(
    ! [A_1547,B_1548] :
      ( k6_tmap_1(A_1547,u1_struct_0(B_1548)) != k6_tmap_1('#skF_2','#skF_4')
      | k8_tmap_1(A_1547,B_1548) = k6_tmap_1('#skF_2','#skF_4')
      | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_4'))
      | ~ v2_pre_topc(k6_tmap_1('#skF_2','#skF_4'))
      | ~ v1_pre_topc(k6_tmap_1('#skF_2','#skF_4'))
      | ~ m1_pre_topc(B_1548,A_1547)
      | ~ l1_pre_topc(A_1547)
      | ~ v2_pre_topc(A_1547)
      | v2_struct_0(A_1547)
      | k8_tmap_1(A_1547,B_1548) = k6_tmap_1('#skF_2','#skF_4')
      | ~ m1_pre_topc(B_1548,A_1547)
      | ~ l1_pre_topc(A_1547)
      | ~ v2_pre_topc(A_1547)
      | v2_struct_0(A_1547) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25067,c_6])).

tff(c_25091,plain,(
    ! [A_1549,B_1550] :
      ( k6_tmap_1(A_1549,u1_struct_0(B_1550)) != k6_tmap_1('#skF_2','#skF_4')
      | k8_tmap_1(A_1549,B_1550) = k6_tmap_1('#skF_2','#skF_4')
      | ~ m1_pre_topc(B_1550,A_1549)
      | ~ l1_pre_topc(A_1549)
      | ~ v2_pre_topc(A_1549)
      | v2_struct_0(A_1549) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24069,c_24144,c_24116,c_25079])).

tff(c_25101,plain,(
    ! [A_1551] :
      ( k6_tmap_1(A_1551,'#skF_4') != k6_tmap_1('#skF_2','#skF_4')
      | k8_tmap_1(A_1551,'#skF_3') = k6_tmap_1('#skF_2','#skF_4')
      | ~ m1_pre_topc('#skF_3',A_1551)
      | ~ l1_pre_topc(A_1551)
      | ~ v2_pre_topc(A_1551)
      | v2_struct_0(A_1551) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23979,c_25091])).

tff(c_25104,plain,
    ( k8_tmap_1('#skF_2','#skF_3') = k6_tmap_1('#skF_2','#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_25101])).

tff(c_25107,plain,
    ( k8_tmap_1('#skF_2','#skF_3') = k6_tmap_1('#skF_2','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_25104])).

tff(c_25108,plain,(
    k8_tmap_1('#skF_2','#skF_3') = k6_tmap_1('#skF_2','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_25107])).

tff(c_24007,plain,(
    ! [B_1445,A_1446] :
      ( m1_subset_1(u1_struct_0(B_1445),k1_zfmisc_1(u1_struct_0(A_1446)))
      | ~ m1_pre_topc(B_1445,A_1446)
      | ~ l1_pre_topc(A_1446) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_24013,plain,(
    ! [B_1445] :
      ( m1_subset_1(u1_struct_0(B_1445),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_1445,k8_tmap_1('#skF_2','#skF_3'))
      | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23980,c_24007])).

tff(c_24083,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_24013])).

tff(c_25115,plain,(
    ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25108,c_24083])).

tff(c_25121,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24116,c_25115])).

tff(c_25123,plain,(
    l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_24013])).

tff(c_23989,plain,(
    ! [A_1444] :
      ( g1_pre_topc(u1_struct_0(A_1444),u1_pre_topc(A_1444)) = A_1444
      | ~ v1_pre_topc(A_1444)
      | ~ l1_pre_topc(A_1444) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_23998,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))) = k8_tmap_1('#skF_2','#skF_3')
    | ~ v1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_23980,c_23989])).

tff(c_25462,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))) = k8_tmap_1('#skF_2','#skF_3')
    | ~ v1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25123,c_23998])).

tff(c_25463,plain,(
    ~ v1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_25462])).

tff(c_27107,plain,(
    ~ v1_pre_topc(k6_tmap_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27096,c_25463])).

tff(c_27125,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24069,c_27107])).

tff(c_27126,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))) = k8_tmap_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_25462])).

tff(c_22,plain,(
    ! [D_36,B_32,C_35,A_31] :
      ( D_36 = B_32
      | g1_pre_topc(C_35,D_36) != g1_pre_topc(A_31,B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(k1_zfmisc_1(A_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_27524,plain,(
    ! [B_1717,A_1718] :
      ( u1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) = B_1717
      | k8_tmap_1('#skF_2','#skF_3') != g1_pre_topc(A_1718,B_1717)
      | ~ m1_subset_1(B_1717,k1_zfmisc_1(k1_zfmisc_1(A_1718))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27126,c_22])).

tff(c_27527,plain,
    ( u1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) = k5_tmap_1('#skF_2','#skF_4')
    | g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2','#skF_4')) != k8_tmap_1('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_25386,c_27524])).

tff(c_27532,plain,
    ( u1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) = k5_tmap_1('#skF_2','#skF_4')
    | k8_tmap_1('#skF_2','#skF_3') != k6_tmap_1('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25314,c_27527])).

tff(c_27533,plain,(
    k8_tmap_1('#skF_2','#skF_3') != k6_tmap_1('#skF_2','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_24029,c_27532])).

tff(c_28206,plain,(
    ! [A_1762,B_1763] :
      ( '#skF_1'(A_1762,B_1763,k6_tmap_1('#skF_2','#skF_4')) = u1_struct_0(B_1763)
      | k8_tmap_1(A_1762,B_1763) = k6_tmap_1('#skF_2','#skF_4')
      | ~ m1_pre_topc(B_1763,A_1762)
      | ~ l1_pre_topc(A_1762)
      | ~ v2_pre_topc(A_1762)
      | v2_struct_0(A_1762) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24069,c_25180,c_25397])).

tff(c_28215,plain,(
    ! [A_1762,B_1763] :
      ( k6_tmap_1(A_1762,u1_struct_0(B_1763)) != k6_tmap_1('#skF_2','#skF_4')
      | k8_tmap_1(A_1762,B_1763) = k6_tmap_1('#skF_2','#skF_4')
      | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_4'))
      | ~ v2_pre_topc(k6_tmap_1('#skF_2','#skF_4'))
      | ~ v1_pre_topc(k6_tmap_1('#skF_2','#skF_4'))
      | ~ m1_pre_topc(B_1763,A_1762)
      | ~ l1_pre_topc(A_1762)
      | ~ v2_pre_topc(A_1762)
      | v2_struct_0(A_1762)
      | k8_tmap_1(A_1762,B_1763) = k6_tmap_1('#skF_2','#skF_4')
      | ~ m1_pre_topc(B_1763,A_1762)
      | ~ l1_pre_topc(A_1762)
      | ~ v2_pre_topc(A_1762)
      | v2_struct_0(A_1762) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28206,c_6])).

tff(c_28231,plain,(
    ! [A_1767,B_1768] :
      ( k6_tmap_1(A_1767,u1_struct_0(B_1768)) != k6_tmap_1('#skF_2','#skF_4')
      | k8_tmap_1(A_1767,B_1768) = k6_tmap_1('#skF_2','#skF_4')
      | ~ m1_pre_topc(B_1768,A_1767)
      | ~ l1_pre_topc(A_1767)
      | ~ v2_pre_topc(A_1767)
      | v2_struct_0(A_1767) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24069,c_25239,c_25180,c_28215])).

tff(c_28241,plain,(
    ! [A_1769] :
      ( k6_tmap_1(A_1769,'#skF_4') != k6_tmap_1('#skF_2','#skF_4')
      | k8_tmap_1(A_1769,'#skF_3') = k6_tmap_1('#skF_2','#skF_4')
      | ~ m1_pre_topc('#skF_3',A_1769)
      | ~ l1_pre_topc(A_1769)
      | ~ v2_pre_topc(A_1769)
      | v2_struct_0(A_1769) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23979,c_28231])).

tff(c_28244,plain,
    ( k8_tmap_1('#skF_2','#skF_3') = k6_tmap_1('#skF_2','#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_28241])).

tff(c_28247,plain,
    ( k8_tmap_1('#skF_2','#skF_3') = k6_tmap_1('#skF_2','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_28244])).

tff(c_28249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_27533,c_28247])).

%------------------------------------------------------------------------------
