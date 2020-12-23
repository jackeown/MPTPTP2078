%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:19 EST 2020

% Result     : Theorem 8.69s
% Output     : CNFRefutation 8.86s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 152 expanded)
%              Number of leaves         :   43 (  68 expanded)
%              Depth                    :    9
%              Number of atoms          :  141 ( 268 expanded)
%              Number of equality atoms :   69 ( 100 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff(f_125,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_84,axiom,(
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

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_65,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_113,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_15594,plain,(
    ! [A_371,B_372,C_373] :
      ( k7_subset_1(A_371,B_372,C_373) = k4_xboole_0(B_372,C_373)
      | ~ m1_subset_1(B_372,k1_zfmisc_1(A_371)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_15600,plain,(
    ! [C_373] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_373) = k4_xboole_0('#skF_2',C_373) ),
    inference(resolution,[status(thm)],[c_46,c_15594])).

tff(c_52,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_103,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_50,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_3278,plain,(
    ! [B_153,A_154] :
      ( v4_pre_topc(B_153,A_154)
      | k2_pre_topc(A_154,B_153) != B_153
      | ~ v2_pre_topc(A_154)
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ l1_pre_topc(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3288,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_3278])).

tff(c_3293,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50,c_3288])).

tff(c_3294,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_3293])).

tff(c_3306,plain,(
    ! [A_155,B_156] :
      ( k4_subset_1(u1_struct_0(A_155),B_156,k2_tops_1(A_155,B_156)) = k2_pre_topc(A_155,B_156)
      | ~ m1_subset_1(B_156,k1_zfmisc_1(u1_struct_0(A_155)))
      | ~ l1_pre_topc(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_3313,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_3306])).

tff(c_3318,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3313])).

tff(c_1476,plain,(
    ! [A_116,B_117,C_118] :
      ( k7_subset_1(A_116,B_117,C_118) = k4_xboole_0(B_117,C_118)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(A_116)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1483,plain,(
    ! [C_119] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_119) = k4_xboole_0('#skF_2',C_119) ),
    inference(resolution,[status(thm)],[c_46,c_1476])).

tff(c_58,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_196,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_58])).

tff(c_1489,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1483,c_196])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_78,plain,(
    ! [A_51,B_52] : k4_xboole_0(A_51,k2_xboole_0(A_51,B_52)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_88,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_78])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_361,plain,(
    ! [A_74,B_75] : k5_xboole_0(A_74,k3_xboole_0(A_74,B_75)) = k4_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_385,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_361])).

tff(c_388,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_385])).

tff(c_10,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_162,plain,(
    ! [A_63,B_64] :
      ( k3_xboole_0(A_63,B_64) = A_63
      | ~ r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_693,plain,(
    ! [A_92,B_93] : k3_xboole_0(k4_xboole_0(A_92,B_93),A_92) = k4_xboole_0(A_92,B_93) ),
    inference(resolution,[status(thm)],[c_10,c_162])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_705,plain,(
    ! [A_92,B_93] : k5_xboole_0(k4_xboole_0(A_92,B_93),k4_xboole_0(A_92,B_93)) = k4_xboole_0(k4_xboole_0(A_92,B_93),A_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_693,c_4])).

tff(c_762,plain,(
    ! [A_94,B_95] : k4_xboole_0(k4_xboole_0(A_94,B_95),A_94) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_705])).

tff(c_12,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_780,plain,(
    ! [A_94,B_95] : k2_xboole_0(A_94,k4_xboole_0(A_94,B_95)) = k2_xboole_0(A_94,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_762,c_12])).

tff(c_816,plain,(
    ! [A_94,B_95] : k2_xboole_0(A_94,k4_xboole_0(A_94,B_95)) = A_94 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_780])).

tff(c_1528,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1489,c_816])).

tff(c_38,plain,(
    ! [A_35,B_36] :
      ( m1_subset_1(k2_tops_1(A_35,B_36),k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2431,plain,(
    ! [A_136,B_137,C_138] :
      ( k4_subset_1(A_136,B_137,C_138) = k2_xboole_0(B_137,C_138)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(A_136))
      | ~ m1_subset_1(B_137,k1_zfmisc_1(A_136)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_14082,plain,(
    ! [A_308,B_309,B_310] :
      ( k4_subset_1(u1_struct_0(A_308),B_309,k2_tops_1(A_308,B_310)) = k2_xboole_0(B_309,k2_tops_1(A_308,B_310))
      | ~ m1_subset_1(B_309,k1_zfmisc_1(u1_struct_0(A_308)))
      | ~ m1_subset_1(B_310,k1_zfmisc_1(u1_struct_0(A_308)))
      | ~ l1_pre_topc(A_308) ) ),
    inference(resolution,[status(thm)],[c_38,c_2431])).

tff(c_14089,plain,(
    ! [B_310] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_310)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_310))
      | ~ m1_subset_1(B_310,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_46,c_14082])).

tff(c_14369,plain,(
    ! [B_313] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_313)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_313))
      | ~ m1_subset_1(B_313,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_14089])).

tff(c_14380,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_46,c_14369])).

tff(c_14386,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3318,c_1528,c_14380])).

tff(c_14388,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3294,c_14386])).

tff(c_14389,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_15601,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15600,c_14389])).

tff(c_14390,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_17320,plain,(
    ! [A_409,B_410] :
      ( r1_tarski(k2_tops_1(A_409,B_410),B_410)
      | ~ v4_pre_topc(B_410,A_409)
      | ~ m1_subset_1(B_410,k1_zfmisc_1(u1_struct_0(A_409)))
      | ~ l1_pre_topc(A_409) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_17327,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_17320])).

tff(c_17332,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_14390,c_17327])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_17336,plain,(
    k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_17332,c_8])).

tff(c_18,plain,(
    ! [B_17,A_16] : k2_tarski(B_17,A_16) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14425,plain,(
    ! [A_318,B_319] : k1_setfam_1(k2_tarski(A_318,B_319)) = k3_xboole_0(A_318,B_319) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_14484,plain,(
    ! [B_325,A_326] : k1_setfam_1(k2_tarski(B_325,A_326)) = k3_xboole_0(A_326,B_325) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_14425])).

tff(c_28,plain,(
    ! [A_28,B_29] : k1_setfam_1(k2_tarski(A_28,B_29)) = k3_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_14490,plain,(
    ! [B_325,A_326] : k3_xboole_0(B_325,A_326) = k3_xboole_0(A_326,B_325) ),
    inference(superposition,[status(thm),theory(equality)],[c_14484,c_28])).

tff(c_17406,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_17336,c_14490])).

tff(c_17766,plain,(
    ! [A_416,B_417] :
      ( k7_subset_1(u1_struct_0(A_416),B_417,k2_tops_1(A_416,B_417)) = k1_tops_1(A_416,B_417)
      | ~ m1_subset_1(B_417,k1_zfmisc_1(u1_struct_0(A_416)))
      | ~ l1_pre_topc(A_416) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_17773,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_17766])).

tff(c_17778,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_15600,c_17773])).

tff(c_16,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_17800,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_17778,c_16])).

tff(c_17809,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17406,c_17800])).

tff(c_17811,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15601,c_17809])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:21:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.69/3.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.86/3.30  
% 8.86/3.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.86/3.30  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 8.86/3.30  
% 8.86/3.30  %Foreground sorts:
% 8.86/3.30  
% 8.86/3.30  
% 8.86/3.30  %Background operators:
% 8.86/3.30  
% 8.86/3.30  
% 8.86/3.30  %Foreground operators:
% 8.86/3.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.86/3.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.86/3.30  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 8.86/3.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.86/3.30  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.86/3.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.86/3.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.86/3.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.86/3.30  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 8.86/3.30  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 8.86/3.30  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 8.86/3.30  tff('#skF_2', type, '#skF_2': $i).
% 8.86/3.30  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 8.86/3.30  tff('#skF_1', type, '#skF_1': $i).
% 8.86/3.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.86/3.30  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 8.86/3.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.86/3.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.86/3.30  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.86/3.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.86/3.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.86/3.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.86/3.30  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 8.86/3.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.86/3.30  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.86/3.30  
% 8.86/3.32  tff(f_125, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 8.86/3.32  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 8.86/3.32  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 8.86/3.32  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 8.86/3.32  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 8.86/3.32  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 8.86/3.32  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 8.86/3.32  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.86/3.32  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 8.86/3.32  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.86/3.32  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 8.86/3.32  tff(f_90, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 8.86/3.32  tff(f_59, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 8.86/3.32  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 8.86/3.32  tff(f_45, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 8.86/3.32  tff(f_65, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 8.86/3.32  tff(f_113, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 8.86/3.32  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.86/3.32  tff(c_46, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.86/3.32  tff(c_15594, plain, (![A_371, B_372, C_373]: (k7_subset_1(A_371, B_372, C_373)=k4_xboole_0(B_372, C_373) | ~m1_subset_1(B_372, k1_zfmisc_1(A_371)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.86/3.32  tff(c_15600, plain, (![C_373]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_373)=k4_xboole_0('#skF_2', C_373))), inference(resolution, [status(thm)], [c_46, c_15594])).
% 8.86/3.32  tff(c_52, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.86/3.32  tff(c_103, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_52])).
% 8.86/3.32  tff(c_48, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.86/3.32  tff(c_50, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.86/3.32  tff(c_3278, plain, (![B_153, A_154]: (v4_pre_topc(B_153, A_154) | k2_pre_topc(A_154, B_153)!=B_153 | ~v2_pre_topc(A_154) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0(A_154))) | ~l1_pre_topc(A_154))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.86/3.32  tff(c_3288, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_3278])).
% 8.86/3.32  tff(c_3293, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50, c_3288])).
% 8.86/3.32  tff(c_3294, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_103, c_3293])).
% 8.86/3.32  tff(c_3306, plain, (![A_155, B_156]: (k4_subset_1(u1_struct_0(A_155), B_156, k2_tops_1(A_155, B_156))=k2_pre_topc(A_155, B_156) | ~m1_subset_1(B_156, k1_zfmisc_1(u1_struct_0(A_155))) | ~l1_pre_topc(A_155))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.86/3.32  tff(c_3313, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_3306])).
% 8.86/3.32  tff(c_3318, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_3313])).
% 8.86/3.32  tff(c_1476, plain, (![A_116, B_117, C_118]: (k7_subset_1(A_116, B_117, C_118)=k4_xboole_0(B_117, C_118) | ~m1_subset_1(B_117, k1_zfmisc_1(A_116)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.86/3.32  tff(c_1483, plain, (![C_119]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_119)=k4_xboole_0('#skF_2', C_119))), inference(resolution, [status(thm)], [c_46, c_1476])).
% 8.86/3.32  tff(c_58, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.86/3.32  tff(c_196, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_103, c_58])).
% 8.86/3.32  tff(c_1489, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1483, c_196])).
% 8.86/3.32  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.86/3.32  tff(c_78, plain, (![A_51, B_52]: (k4_xboole_0(A_51, k2_xboole_0(A_51, B_52))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.86/3.32  tff(c_88, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_78])).
% 8.86/3.32  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.86/3.32  tff(c_361, plain, (![A_74, B_75]: (k5_xboole_0(A_74, k3_xboole_0(A_74, B_75))=k4_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.86/3.32  tff(c_385, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_361])).
% 8.86/3.32  tff(c_388, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_88, c_385])).
% 8.86/3.32  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.86/3.32  tff(c_162, plain, (![A_63, B_64]: (k3_xboole_0(A_63, B_64)=A_63 | ~r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.86/3.32  tff(c_693, plain, (![A_92, B_93]: (k3_xboole_0(k4_xboole_0(A_92, B_93), A_92)=k4_xboole_0(A_92, B_93))), inference(resolution, [status(thm)], [c_10, c_162])).
% 8.86/3.32  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.86/3.32  tff(c_705, plain, (![A_92, B_93]: (k5_xboole_0(k4_xboole_0(A_92, B_93), k4_xboole_0(A_92, B_93))=k4_xboole_0(k4_xboole_0(A_92, B_93), A_92))), inference(superposition, [status(thm), theory('equality')], [c_693, c_4])).
% 8.86/3.32  tff(c_762, plain, (![A_94, B_95]: (k4_xboole_0(k4_xboole_0(A_94, B_95), A_94)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_388, c_705])).
% 8.86/3.32  tff(c_12, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.86/3.32  tff(c_780, plain, (![A_94, B_95]: (k2_xboole_0(A_94, k4_xboole_0(A_94, B_95))=k2_xboole_0(A_94, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_762, c_12])).
% 8.86/3.32  tff(c_816, plain, (![A_94, B_95]: (k2_xboole_0(A_94, k4_xboole_0(A_94, B_95))=A_94)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_780])).
% 8.86/3.32  tff(c_1528, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1489, c_816])).
% 8.86/3.32  tff(c_38, plain, (![A_35, B_36]: (m1_subset_1(k2_tops_1(A_35, B_36), k1_zfmisc_1(u1_struct_0(A_35))) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.86/3.32  tff(c_2431, plain, (![A_136, B_137, C_138]: (k4_subset_1(A_136, B_137, C_138)=k2_xboole_0(B_137, C_138) | ~m1_subset_1(C_138, k1_zfmisc_1(A_136)) | ~m1_subset_1(B_137, k1_zfmisc_1(A_136)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.86/3.32  tff(c_14082, plain, (![A_308, B_309, B_310]: (k4_subset_1(u1_struct_0(A_308), B_309, k2_tops_1(A_308, B_310))=k2_xboole_0(B_309, k2_tops_1(A_308, B_310)) | ~m1_subset_1(B_309, k1_zfmisc_1(u1_struct_0(A_308))) | ~m1_subset_1(B_310, k1_zfmisc_1(u1_struct_0(A_308))) | ~l1_pre_topc(A_308))), inference(resolution, [status(thm)], [c_38, c_2431])).
% 8.86/3.32  tff(c_14089, plain, (![B_310]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_310))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_310)) | ~m1_subset_1(B_310, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_14082])).
% 8.86/3.32  tff(c_14369, plain, (![B_313]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_313))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_313)) | ~m1_subset_1(B_313, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_14089])).
% 8.86/3.32  tff(c_14380, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_46, c_14369])).
% 8.86/3.32  tff(c_14386, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3318, c_1528, c_14380])).
% 8.86/3.32  tff(c_14388, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3294, c_14386])).
% 8.86/3.32  tff(c_14389, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 8.86/3.32  tff(c_15601, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_15600, c_14389])).
% 8.86/3.32  tff(c_14390, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_52])).
% 8.86/3.32  tff(c_17320, plain, (![A_409, B_410]: (r1_tarski(k2_tops_1(A_409, B_410), B_410) | ~v4_pre_topc(B_410, A_409) | ~m1_subset_1(B_410, k1_zfmisc_1(u1_struct_0(A_409))) | ~l1_pre_topc(A_409))), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.86/3.32  tff(c_17327, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_17320])).
% 8.86/3.32  tff(c_17332, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_14390, c_17327])).
% 8.86/3.32  tff(c_8, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.86/3.32  tff(c_17336, plain, (k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_17332, c_8])).
% 8.86/3.32  tff(c_18, plain, (![B_17, A_16]: (k2_tarski(B_17, A_16)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.86/3.32  tff(c_14425, plain, (![A_318, B_319]: (k1_setfam_1(k2_tarski(A_318, B_319))=k3_xboole_0(A_318, B_319))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.86/3.32  tff(c_14484, plain, (![B_325, A_326]: (k1_setfam_1(k2_tarski(B_325, A_326))=k3_xboole_0(A_326, B_325))), inference(superposition, [status(thm), theory('equality')], [c_18, c_14425])).
% 8.86/3.32  tff(c_28, plain, (![A_28, B_29]: (k1_setfam_1(k2_tarski(A_28, B_29))=k3_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.86/3.32  tff(c_14490, plain, (![B_325, A_326]: (k3_xboole_0(B_325, A_326)=k3_xboole_0(A_326, B_325))), inference(superposition, [status(thm), theory('equality')], [c_14484, c_28])).
% 8.86/3.32  tff(c_17406, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_17336, c_14490])).
% 8.86/3.32  tff(c_17766, plain, (![A_416, B_417]: (k7_subset_1(u1_struct_0(A_416), B_417, k2_tops_1(A_416, B_417))=k1_tops_1(A_416, B_417) | ~m1_subset_1(B_417, k1_zfmisc_1(u1_struct_0(A_416))) | ~l1_pre_topc(A_416))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.86/3.32  tff(c_17773, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_17766])).
% 8.86/3.32  tff(c_17778, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_15600, c_17773])).
% 8.86/3.32  tff(c_16, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.86/3.32  tff(c_17800, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_17778, c_16])).
% 8.86/3.32  tff(c_17809, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_17406, c_17800])).
% 8.86/3.32  tff(c_17811, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15601, c_17809])).
% 8.86/3.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.86/3.32  
% 8.86/3.32  Inference rules
% 8.86/3.32  ----------------------
% 8.86/3.32  #Ref     : 0
% 8.86/3.32  #Sup     : 4377
% 8.86/3.32  #Fact    : 0
% 8.86/3.32  #Define  : 0
% 8.86/3.32  #Split   : 2
% 8.86/3.32  #Chain   : 0
% 8.86/3.32  #Close   : 0
% 8.86/3.32  
% 8.86/3.32  Ordering : KBO
% 8.86/3.32  
% 8.86/3.32  Simplification rules
% 8.86/3.32  ----------------------
% 8.86/3.32  #Subsume      : 136
% 8.86/3.32  #Demod        : 6816
% 8.86/3.32  #Tautology    : 3683
% 8.86/3.32  #SimpNegUnit  : 6
% 8.86/3.32  #BackRed      : 4
% 8.86/3.32  
% 8.86/3.32  #Partial instantiations: 0
% 8.86/3.32  #Strategies tried      : 1
% 8.86/3.32  
% 8.86/3.32  Timing (in seconds)
% 8.86/3.32  ----------------------
% 8.86/3.32  Preprocessing        : 0.34
% 8.86/3.32  Parsing              : 0.18
% 8.86/3.32  CNF conversion       : 0.02
% 8.86/3.32  Main loop            : 2.21
% 8.86/3.32  Inferencing          : 0.52
% 8.86/3.32  Reduction            : 1.25
% 8.86/3.32  Demodulation         : 1.09
% 8.86/3.32  BG Simplification    : 0.05
% 8.86/3.32  Subsumption          : 0.29
% 8.86/3.32  Abstraction          : 0.10
% 8.86/3.32  MUC search           : 0.00
% 8.86/3.32  Cooper               : 0.00
% 8.86/3.32  Total                : 2.59
% 8.86/3.32  Index Insertion      : 0.00
% 8.86/3.32  Index Deletion       : 0.00
% 8.86/3.32  Index Matching       : 0.00
% 8.86/3.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
