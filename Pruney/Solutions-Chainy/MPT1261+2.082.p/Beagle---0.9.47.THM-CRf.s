%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:23 EST 2020

% Result     : Theorem 5.62s
% Output     : CNFRefutation 5.62s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 136 expanded)
%              Number of leaves         :   36 (  62 expanded)
%              Depth                    :    8
%              Number of atoms          :  118 ( 254 expanded)
%              Number of equality atoms :   57 (  93 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_37,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_4845,plain,(
    ! [A_185,B_186,C_187] :
      ( k7_subset_1(A_185,B_186,C_187) = k4_xboole_0(B_186,C_187)
      | ~ m1_subset_1(B_186,k1_zfmisc_1(A_185)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4848,plain,(
    ! [C_187] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_187) = k4_xboole_0('#skF_2',C_187) ),
    inference(resolution,[status(thm)],[c_30,c_4845])).

tff(c_36,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_177,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1051,plain,(
    ! [B_96,A_97] :
      ( v4_pre_topc(B_96,A_97)
      | k2_pre_topc(A_97,B_96) != B_96
      | ~ v2_pre_topc(A_97)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1057,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1051])).

tff(c_1061,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_1057])).

tff(c_1062,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_177,c_1061])).

tff(c_1776,plain,(
    ! [A_104,B_105] :
      ( k4_subset_1(u1_struct_0(A_104),B_105,k2_tops_1(A_104,B_105)) = k2_pre_topc(A_104,B_105)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1780,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1776])).

tff(c_1784,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1780])).

tff(c_456,plain,(
    ! [A_62,B_63,C_64] :
      ( k7_subset_1(A_62,B_63,C_64) = k4_xboole_0(B_63,C_64)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_460,plain,(
    ! [C_65] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_65) = k4_xboole_0('#skF_2',C_65) ),
    inference(resolution,[status(thm)],[c_30,c_456])).

tff(c_42,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_278,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_177,c_42])).

tff(c_466,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_460,c_278])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_356,plain,(
    ! [A_58,B_59] : k2_xboole_0(k5_xboole_0(A_58,B_59),k3_xboole_0(A_58,B_59)) = k2_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_383,plain,(
    ! [A_1,B_2] : k2_xboole_0(k4_xboole_0(A_1,B_2),k3_xboole_0(A_1,k3_xboole_0(A_1,B_2))) = k2_xboole_0(A_1,k3_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_356])).

tff(c_394,plain,(
    ! [A_1,B_2] : k2_xboole_0(k4_xboole_0(A_1,B_2),k3_xboole_0(A_1,k3_xboole_0(A_1,B_2))) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_383])).

tff(c_10,plain,(
    ! [B_10,A_9] : k2_tarski(B_10,A_9) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_100,plain,(
    ! [A_39,B_40] : k3_tarski(k2_tarski(A_39,B_40)) = k2_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_206,plain,(
    ! [A_47,B_48] : k3_tarski(k2_tarski(A_47,B_48)) = k2_xboole_0(B_48,A_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_100])).

tff(c_12,plain,(
    ! [A_11,B_12] : k3_tarski(k2_tarski(A_11,B_12)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_212,plain,(
    ! [B_48,A_47] : k2_xboole_0(B_48,A_47) = k2_xboole_0(A_47,B_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_12])).

tff(c_480,plain,(
    ! [A_66,B_67] : k2_xboole_0(k4_xboole_0(A_66,B_67),k3_xboole_0(A_66,k3_xboole_0(A_66,B_67))) = A_66 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_383])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_489,plain,(
    ! [A_66,B_67] : k2_xboole_0(k4_xboole_0(A_66,B_67),k3_xboole_0(A_66,k3_xboole_0(A_66,B_67))) = k2_xboole_0(k4_xboole_0(A_66,B_67),A_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_480,c_6])).

tff(c_506,plain,(
    ! [A_68,B_69] : k2_xboole_0(A_68,k4_xboole_0(A_68,B_69)) = A_68 ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_212,c_489])).

tff(c_521,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_466,c_506])).

tff(c_24,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(k2_tops_1(A_24,B_25),k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_942,plain,(
    ! [A_89,B_90,C_91] :
      ( k4_subset_1(A_89,B_90,C_91) = k2_xboole_0(B_90,C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(A_89))
      | ~ m1_subset_1(B_90,k1_zfmisc_1(A_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4297,plain,(
    ! [A_156,B_157,B_158] :
      ( k4_subset_1(u1_struct_0(A_156),B_157,k2_tops_1(A_156,B_158)) = k2_xboole_0(B_157,k2_tops_1(A_156,B_158))
      | ~ m1_subset_1(B_157,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ m1_subset_1(B_158,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ l1_pre_topc(A_156) ) ),
    inference(resolution,[status(thm)],[c_24,c_942])).

tff(c_4301,plain,(
    ! [B_158] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_158)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_158))
      | ~ m1_subset_1(B_158,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_4297])).

tff(c_4427,plain,(
    ! [B_159] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_159)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_159))
      | ~ m1_subset_1(B_159,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_4301])).

tff(c_4434,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_4427])).

tff(c_4439,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1784,c_521,c_4434])).

tff(c_4441,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1062,c_4439])).

tff(c_4442,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_4849,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4848,c_4442])).

tff(c_4443,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_4860,plain,(
    ! [A_189,B_190] :
      ( k2_pre_topc(A_189,B_190) = B_190
      | ~ v4_pre_topc(B_190,A_189)
      | ~ m1_subset_1(B_190,k1_zfmisc_1(u1_struct_0(A_189)))
      | ~ l1_pre_topc(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4863,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_4860])).

tff(c_4866,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_4443,c_4863])).

tff(c_6033,plain,(
    ! [A_224,B_225] :
      ( k7_subset_1(u1_struct_0(A_224),k2_pre_topc(A_224,B_225),k1_tops_1(A_224,B_225)) = k2_tops_1(A_224,B_225)
      | ~ m1_subset_1(B_225,k1_zfmisc_1(u1_struct_0(A_224)))
      | ~ l1_pre_topc(A_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6042,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4866,c_6033])).

tff(c_6046,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_4848,c_6042])).

tff(c_6048,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4849,c_6046])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:37:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.62/2.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.62/2.18  
% 5.62/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.62/2.18  %$ v4_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 5.62/2.18  
% 5.62/2.18  %Foreground sorts:
% 5.62/2.18  
% 5.62/2.18  
% 5.62/2.18  %Background operators:
% 5.62/2.18  
% 5.62/2.18  
% 5.62/2.18  %Foreground operators:
% 5.62/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.62/2.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.62/2.18  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 5.62/2.18  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.62/2.18  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.62/2.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.62/2.18  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.62/2.18  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.62/2.18  tff('#skF_2', type, '#skF_2': $i).
% 5.62/2.18  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.62/2.18  tff('#skF_1', type, '#skF_1': $i).
% 5.62/2.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.62/2.18  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.62/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.62/2.18  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.62/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.62/2.18  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.62/2.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.62/2.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.62/2.18  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.62/2.18  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.62/2.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.62/2.18  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.62/2.18  
% 5.62/2.20  tff(f_96, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 5.62/2.20  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.62/2.20  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.62/2.20  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 5.62/2.20  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 5.62/2.20  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.62/2.20  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_xboole_1)).
% 5.62/2.20  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.62/2.20  tff(f_37, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.62/2.20  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_1)).
% 5.62/2.20  tff(f_70, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 5.62/2.20  tff(f_43, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.62/2.20  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 5.62/2.20  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.62/2.20  tff(c_4845, plain, (![A_185, B_186, C_187]: (k7_subset_1(A_185, B_186, C_187)=k4_xboole_0(B_186, C_187) | ~m1_subset_1(B_186, k1_zfmisc_1(A_185)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.62/2.20  tff(c_4848, plain, (![C_187]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_187)=k4_xboole_0('#skF_2', C_187))), inference(resolution, [status(thm)], [c_30, c_4845])).
% 5.62/2.20  tff(c_36, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.62/2.20  tff(c_177, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_36])).
% 5.62/2.20  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.62/2.20  tff(c_34, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.62/2.20  tff(c_1051, plain, (![B_96, A_97]: (v4_pre_topc(B_96, A_97) | k2_pre_topc(A_97, B_96)!=B_96 | ~v2_pre_topc(A_97) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.62/2.20  tff(c_1057, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1051])).
% 5.62/2.20  tff(c_1061, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_1057])).
% 5.62/2.20  tff(c_1062, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_177, c_1061])).
% 5.62/2.20  tff(c_1776, plain, (![A_104, B_105]: (k4_subset_1(u1_struct_0(A_104), B_105, k2_tops_1(A_104, B_105))=k2_pre_topc(A_104, B_105) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.62/2.20  tff(c_1780, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1776])).
% 5.62/2.20  tff(c_1784, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1780])).
% 5.62/2.20  tff(c_456, plain, (![A_62, B_63, C_64]: (k7_subset_1(A_62, B_63, C_64)=k4_xboole_0(B_63, C_64) | ~m1_subset_1(B_63, k1_zfmisc_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.62/2.20  tff(c_460, plain, (![C_65]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_65)=k4_xboole_0('#skF_2', C_65))), inference(resolution, [status(thm)], [c_30, c_456])).
% 5.62/2.20  tff(c_42, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.62/2.20  tff(c_278, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_177, c_42])).
% 5.62/2.20  tff(c_466, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_460, c_278])).
% 5.62/2.20  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k3_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.62/2.20  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.62/2.20  tff(c_356, plain, (![A_58, B_59]: (k2_xboole_0(k5_xboole_0(A_58, B_59), k3_xboole_0(A_58, B_59))=k2_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.62/2.20  tff(c_383, plain, (![A_1, B_2]: (k2_xboole_0(k4_xboole_0(A_1, B_2), k3_xboole_0(A_1, k3_xboole_0(A_1, B_2)))=k2_xboole_0(A_1, k3_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_356])).
% 5.62/2.20  tff(c_394, plain, (![A_1, B_2]: (k2_xboole_0(k4_xboole_0(A_1, B_2), k3_xboole_0(A_1, k3_xboole_0(A_1, B_2)))=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_383])).
% 5.62/2.20  tff(c_10, plain, (![B_10, A_9]: (k2_tarski(B_10, A_9)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.62/2.20  tff(c_100, plain, (![A_39, B_40]: (k3_tarski(k2_tarski(A_39, B_40))=k2_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.62/2.20  tff(c_206, plain, (![A_47, B_48]: (k3_tarski(k2_tarski(A_47, B_48))=k2_xboole_0(B_48, A_47))), inference(superposition, [status(thm), theory('equality')], [c_10, c_100])).
% 5.62/2.20  tff(c_12, plain, (![A_11, B_12]: (k3_tarski(k2_tarski(A_11, B_12))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.62/2.20  tff(c_212, plain, (![B_48, A_47]: (k2_xboole_0(B_48, A_47)=k2_xboole_0(A_47, B_48))), inference(superposition, [status(thm), theory('equality')], [c_206, c_12])).
% 5.62/2.20  tff(c_480, plain, (![A_66, B_67]: (k2_xboole_0(k4_xboole_0(A_66, B_67), k3_xboole_0(A_66, k3_xboole_0(A_66, B_67)))=A_66)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_383])).
% 5.62/2.20  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.62/2.20  tff(c_489, plain, (![A_66, B_67]: (k2_xboole_0(k4_xboole_0(A_66, B_67), k3_xboole_0(A_66, k3_xboole_0(A_66, B_67)))=k2_xboole_0(k4_xboole_0(A_66, B_67), A_66))), inference(superposition, [status(thm), theory('equality')], [c_480, c_6])).
% 5.62/2.20  tff(c_506, plain, (![A_68, B_69]: (k2_xboole_0(A_68, k4_xboole_0(A_68, B_69))=A_68)), inference(demodulation, [status(thm), theory('equality')], [c_394, c_212, c_489])).
% 5.62/2.20  tff(c_521, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_466, c_506])).
% 5.62/2.20  tff(c_24, plain, (![A_24, B_25]: (m1_subset_1(k2_tops_1(A_24, B_25), k1_zfmisc_1(u1_struct_0(A_24))) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.62/2.20  tff(c_942, plain, (![A_89, B_90, C_91]: (k4_subset_1(A_89, B_90, C_91)=k2_xboole_0(B_90, C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(A_89)) | ~m1_subset_1(B_90, k1_zfmisc_1(A_89)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.62/2.20  tff(c_4297, plain, (![A_156, B_157, B_158]: (k4_subset_1(u1_struct_0(A_156), B_157, k2_tops_1(A_156, B_158))=k2_xboole_0(B_157, k2_tops_1(A_156, B_158)) | ~m1_subset_1(B_157, k1_zfmisc_1(u1_struct_0(A_156))) | ~m1_subset_1(B_158, k1_zfmisc_1(u1_struct_0(A_156))) | ~l1_pre_topc(A_156))), inference(resolution, [status(thm)], [c_24, c_942])).
% 5.62/2.20  tff(c_4301, plain, (![B_158]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_158))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_158)) | ~m1_subset_1(B_158, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_4297])).
% 5.62/2.20  tff(c_4427, plain, (![B_159]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_159))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_159)) | ~m1_subset_1(B_159, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_4301])).
% 5.62/2.20  tff(c_4434, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_4427])).
% 5.62/2.20  tff(c_4439, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1784, c_521, c_4434])).
% 5.62/2.20  tff(c_4441, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1062, c_4439])).
% 5.62/2.20  tff(c_4442, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_36])).
% 5.62/2.20  tff(c_4849, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4848, c_4442])).
% 5.62/2.20  tff(c_4443, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_36])).
% 5.62/2.20  tff(c_4860, plain, (![A_189, B_190]: (k2_pre_topc(A_189, B_190)=B_190 | ~v4_pre_topc(B_190, A_189) | ~m1_subset_1(B_190, k1_zfmisc_1(u1_struct_0(A_189))) | ~l1_pre_topc(A_189))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.62/2.20  tff(c_4863, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_4860])).
% 5.62/2.20  tff(c_4866, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_4443, c_4863])).
% 5.62/2.20  tff(c_6033, plain, (![A_224, B_225]: (k7_subset_1(u1_struct_0(A_224), k2_pre_topc(A_224, B_225), k1_tops_1(A_224, B_225))=k2_tops_1(A_224, B_225) | ~m1_subset_1(B_225, k1_zfmisc_1(u1_struct_0(A_224))) | ~l1_pre_topc(A_224))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.62/2.20  tff(c_6042, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4866, c_6033])).
% 5.62/2.20  tff(c_6046, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_4848, c_6042])).
% 5.62/2.20  tff(c_6048, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4849, c_6046])).
% 5.62/2.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.62/2.20  
% 5.62/2.20  Inference rules
% 5.62/2.20  ----------------------
% 5.62/2.20  #Ref     : 0
% 5.62/2.20  #Sup     : 1481
% 5.62/2.20  #Fact    : 0
% 5.62/2.20  #Define  : 0
% 5.62/2.20  #Split   : 2
% 5.62/2.20  #Chain   : 0
% 5.62/2.20  #Close   : 0
% 5.62/2.20  
% 5.62/2.20  Ordering : KBO
% 5.62/2.20  
% 5.62/2.20  Simplification rules
% 5.62/2.20  ----------------------
% 5.62/2.20  #Subsume      : 45
% 5.62/2.20  #Demod        : 2858
% 5.62/2.20  #Tautology    : 1132
% 5.62/2.20  #SimpNegUnit  : 4
% 5.62/2.20  #BackRed      : 1
% 5.62/2.20  
% 5.62/2.20  #Partial instantiations: 0
% 5.62/2.20  #Strategies tried      : 1
% 5.62/2.20  
% 5.62/2.20  Timing (in seconds)
% 5.62/2.20  ----------------------
% 5.62/2.20  Preprocessing        : 0.33
% 5.62/2.20  Parsing              : 0.18
% 5.62/2.20  CNF conversion       : 0.02
% 5.62/2.20  Main loop            : 1.09
% 5.62/2.20  Inferencing          : 0.31
% 5.62/2.20  Reduction            : 0.58
% 5.62/2.20  Demodulation         : 0.52
% 5.62/2.20  BG Simplification    : 0.03
% 5.62/2.20  Subsumption          : 0.12
% 5.62/2.20  Abstraction          : 0.06
% 5.62/2.20  MUC search           : 0.00
% 5.62/2.20  Cooper               : 0.00
% 5.62/2.20  Total                : 1.46
% 5.62/2.20  Index Insertion      : 0.00
% 5.62/2.20  Index Deletion       : 0.00
% 5.62/2.20  Index Matching       : 0.00
% 5.62/2.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
