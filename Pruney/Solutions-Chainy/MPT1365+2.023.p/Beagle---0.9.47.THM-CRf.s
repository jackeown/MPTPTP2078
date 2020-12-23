%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:57 EST 2020

% Result     : Theorem 10.80s
% Output     : CNFRefutation 10.80s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 151 expanded)
%              Number of leaves         :   34 (  71 expanded)
%              Depth                    :   12
%              Number of atoms          :  162 ( 407 expanded)
%              Number of equality atoms :   11 (  30 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v8_pre_topc,type,(
    v8_pre_topc: $i > $o )).

tff(v2_compts_1,type,(
    v2_compts_1: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_117,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v8_pre_topc(A)
                    & v2_compts_1(B,A)
                    & v2_compts_1(C,A) )
                 => v2_compts_1(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_compts_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v8_pre_topc(A)
              & v2_compts_1(B,A) )
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_compts_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v4_pre_topc(B,A)
                  & v4_pre_topc(C,A) )
               => v4_pre_topc(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tops_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_31,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_98,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v2_compts_1(B,A)
                  & r1_tarski(C,B)
                  & v4_pre_topc(C,A) )
               => v2_compts_1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_compts_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_118,plain,(
    ! [A_56,B_57,C_58] :
      ( k9_subset_1(A_56,B_57,C_58) = k3_xboole_0(B_57,C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_128,plain,(
    ! [B_57] : k9_subset_1(u1_struct_0('#skF_1'),B_57,'#skF_3') = k3_xboole_0(B_57,'#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_118])).

tff(c_28,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_140,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_28])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_64,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(A_47,B_48)
      | ~ m1_subset_1(A_47,k1_zfmisc_1(B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_79,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_38,c_64])).

tff(c_42,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_34,plain,(
    v8_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_32,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_269,plain,(
    ! [B_84,A_85] :
      ( v4_pre_topc(B_84,A_85)
      | ~ v2_compts_1(B_84,A_85)
      | ~ v8_pre_topc(A_85)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85)
      | ~ v2_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_283,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_269])).

tff(c_295,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_34,c_32,c_283])).

tff(c_20,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,k1_zfmisc_1(B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_30,plain,(
    v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_280,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_269])).

tff(c_292,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_34,c_30,c_280])).

tff(c_509,plain,(
    ! [A_101,B_102,C_103] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(A_101),B_102,C_103),A_101)
      | ~ v4_pre_topc(C_103,A_101)
      | ~ v4_pre_topc(B_102,A_101)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101)
      | ~ v2_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_515,plain,(
    ! [B_57] :
      ( v4_pre_topc(k3_xboole_0(B_57,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc('#skF_3','#skF_1')
      | ~ v4_pre_topc(B_57,'#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_509])).

tff(c_682,plain,(
    ! [B_125] :
      ( v4_pre_topc(k3_xboole_0(B_125,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc(B_125,'#skF_1')
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_292,c_515])).

tff(c_728,plain,(
    ! [A_18] :
      ( v4_pre_topc(k3_xboole_0(A_18,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc(A_18,'#skF_1')
      | ~ r1_tarski(A_18,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_20,c_682])).

tff(c_2,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k4_xboole_0(A_1,B_2)) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_185,plain,(
    ! [A_72,B_73,C_74] :
      ( k7_subset_1(A_72,B_73,C_74) = k4_xboole_0(B_73,C_74)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_320,plain,(
    ! [C_88] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_88) = k4_xboole_0('#skF_2',C_88) ),
    inference(resolution,[status(thm)],[c_38,c_185])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9] :
      ( m1_subset_1(k7_subset_1(A_7,B_8,C_9),k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_329,plain,(
    ! [C_88] :
      ( m1_subset_1(k4_xboole_0('#skF_2',C_88),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_10])).

tff(c_337,plain,(
    ! [C_88] : m1_subset_1(k4_xboole_0('#skF_2',C_88),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_329])).

tff(c_6,plain,(
    ! [A_5] : k2_subset_1(A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_6] : m1_subset_1(k2_subset_1(A_6),k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_43,plain,(
    ! [A_6] : m1_subset_1(A_6,k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_200,plain,(
    ! [A_6,C_74] : k7_subset_1(A_6,A_6,C_74) = k4_xboole_0(A_6,C_74) ),
    inference(resolution,[status(thm)],[c_43,c_185])).

tff(c_160,plain,(
    ! [A_63,B_64,C_65] :
      ( m1_subset_1(k7_subset_1(A_63,B_64,C_65),k1_zfmisc_1(A_63))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | ~ m1_subset_1(A_18,k1_zfmisc_1(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_167,plain,(
    ! [A_63,B_64,C_65] :
      ( r1_tarski(k7_subset_1(A_63,B_64,C_65),A_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_63)) ) ),
    inference(resolution,[status(thm)],[c_160,c_18])).

tff(c_424,plain,(
    ! [C_95,A_96,B_97] :
      ( v2_compts_1(C_95,A_96)
      | ~ v4_pre_topc(C_95,A_96)
      | ~ r1_tarski(C_95,B_97)
      | ~ v2_compts_1(B_97,A_96)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96)
      | ~ v2_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3428,plain,(
    ! [A_305,B_306,C_307,A_308] :
      ( v2_compts_1(k7_subset_1(A_305,B_306,C_307),A_308)
      | ~ v4_pre_topc(k7_subset_1(A_305,B_306,C_307),A_308)
      | ~ v2_compts_1(A_305,A_308)
      | ~ m1_subset_1(k7_subset_1(A_305,B_306,C_307),k1_zfmisc_1(u1_struct_0(A_308)))
      | ~ m1_subset_1(A_305,k1_zfmisc_1(u1_struct_0(A_308)))
      | ~ l1_pre_topc(A_308)
      | ~ v2_pre_topc(A_308)
      | ~ m1_subset_1(B_306,k1_zfmisc_1(A_305)) ) ),
    inference(resolution,[status(thm)],[c_167,c_424])).

tff(c_3464,plain,(
    ! [A_6,C_74,A_308] :
      ( v2_compts_1(k7_subset_1(A_6,A_6,C_74),A_308)
      | ~ v4_pre_topc(k7_subset_1(A_6,A_6,C_74),A_308)
      | ~ v2_compts_1(A_6,A_308)
      | ~ m1_subset_1(k4_xboole_0(A_6,C_74),k1_zfmisc_1(u1_struct_0(A_308)))
      | ~ m1_subset_1(A_6,k1_zfmisc_1(u1_struct_0(A_308)))
      | ~ l1_pre_topc(A_308)
      | ~ v2_pre_topc(A_308)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(A_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_3428])).

tff(c_17464,plain,(
    ! [A_1006,C_1007,A_1008] :
      ( v2_compts_1(k4_xboole_0(A_1006,C_1007),A_1008)
      | ~ v4_pre_topc(k4_xboole_0(A_1006,C_1007),A_1008)
      | ~ v2_compts_1(A_1006,A_1008)
      | ~ m1_subset_1(k4_xboole_0(A_1006,C_1007),k1_zfmisc_1(u1_struct_0(A_1008)))
      | ~ m1_subset_1(A_1006,k1_zfmisc_1(u1_struct_0(A_1008)))
      | ~ l1_pre_topc(A_1008)
      | ~ v2_pre_topc(A_1008) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_200,c_200,c_3464])).

tff(c_17627,plain,(
    ! [C_88] :
      ( v2_compts_1(k4_xboole_0('#skF_2',C_88),'#skF_1')
      | ~ v4_pre_topc(k4_xboole_0('#skF_2',C_88),'#skF_1')
      | ~ v2_compts_1('#skF_2','#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_337,c_17464])).

tff(c_17788,plain,(
    ! [C_1009] :
      ( v2_compts_1(k4_xboole_0('#skF_2',C_1009),'#skF_1')
      | ~ v4_pre_topc(k4_xboole_0('#skF_2',C_1009),'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_32,c_17627])).

tff(c_17815,plain,(
    ! [B_2] :
      ( v2_compts_1(k4_xboole_0('#skF_2',k4_xboole_0('#skF_2',B_2)),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0('#skF_2',B_2),'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_17788])).

tff(c_17858,plain,(
    ! [B_1011] :
      ( v2_compts_1(k3_xboole_0('#skF_2',B_1011),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0('#skF_2',B_1011),'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_17815])).

tff(c_17882,plain,
    ( v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_728,c_17858])).

tff(c_17909,plain,(
    v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_295,c_17882])).

tff(c_17911,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_17909])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:00:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.80/4.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.80/4.67  
% 10.80/4.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.80/4.67  %$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 10.80/4.67  
% 10.80/4.67  %Foreground sorts:
% 10.80/4.67  
% 10.80/4.67  
% 10.80/4.67  %Background operators:
% 10.80/4.67  
% 10.80/4.67  
% 10.80/4.67  %Foreground operators:
% 10.80/4.67  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 10.80/4.67  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 10.80/4.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.80/4.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.80/4.67  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.80/4.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.80/4.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.80/4.67  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.80/4.67  tff('#skF_2', type, '#skF_2': $i).
% 10.80/4.67  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 10.80/4.67  tff('#skF_3', type, '#skF_3': $i).
% 10.80/4.67  tff('#skF_1', type, '#skF_1': $i).
% 10.80/4.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.80/4.67  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 10.80/4.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.80/4.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.80/4.67  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.80/4.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.80/4.67  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.80/4.67  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 10.80/4.67  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 10.80/4.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.80/4.67  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 10.80/4.67  
% 10.80/4.68  tff(f_117, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v8_pre_topc(A) & v2_compts_1(B, A)) & v2_compts_1(C, A)) => v2_compts_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_compts_1)).
% 10.80/4.68  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 10.80/4.68  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 10.80/4.68  tff(f_80, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v8_pre_topc(A) & v2_compts_1(B, A)) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_compts_1)).
% 10.80/4.68  tff(f_67, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & v4_pre_topc(C, A)) => v4_pre_topc(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tops_1)).
% 10.80/4.68  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.80/4.68  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 10.80/4.68  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 10.80/4.68  tff(f_31, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 10.80/4.68  tff(f_33, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 10.80/4.68  tff(f_98, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v2_compts_1(B, A) & r1_tarski(C, B)) & v4_pre_topc(C, A)) => v2_compts_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_compts_1)).
% 10.80/4.68  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.80/4.68  tff(c_118, plain, (![A_56, B_57, C_58]: (k9_subset_1(A_56, B_57, C_58)=k3_xboole_0(B_57, C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.80/4.68  tff(c_128, plain, (![B_57]: (k9_subset_1(u1_struct_0('#skF_1'), B_57, '#skF_3')=k3_xboole_0(B_57, '#skF_3'))), inference(resolution, [status(thm)], [c_36, c_118])).
% 10.80/4.68  tff(c_28, plain, (~v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.80/4.68  tff(c_140, plain, (~v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_28])).
% 10.80/4.68  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.80/4.68  tff(c_64, plain, (![A_47, B_48]: (r1_tarski(A_47, B_48) | ~m1_subset_1(A_47, k1_zfmisc_1(B_48)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.80/4.68  tff(c_79, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_64])).
% 10.80/4.68  tff(c_42, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.80/4.68  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.80/4.68  tff(c_34, plain, (v8_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.80/4.68  tff(c_32, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.80/4.68  tff(c_269, plain, (![B_84, A_85]: (v4_pre_topc(B_84, A_85) | ~v2_compts_1(B_84, A_85) | ~v8_pre_topc(A_85) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85) | ~v2_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.80/4.68  tff(c_283, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_269])).
% 10.80/4.68  tff(c_295, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_34, c_32, c_283])).
% 10.80/4.68  tff(c_20, plain, (![A_18, B_19]: (m1_subset_1(A_18, k1_zfmisc_1(B_19)) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.80/4.68  tff(c_30, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.80/4.68  tff(c_280, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_269])).
% 10.80/4.68  tff(c_292, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_34, c_30, c_280])).
% 10.80/4.68  tff(c_509, plain, (![A_101, B_102, C_103]: (v4_pre_topc(k9_subset_1(u1_struct_0(A_101), B_102, C_103), A_101) | ~v4_pre_topc(C_103, A_101) | ~v4_pre_topc(B_102, A_101) | ~m1_subset_1(C_103, k1_zfmisc_1(u1_struct_0(A_101))) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101) | ~v2_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.80/4.68  tff(c_515, plain, (![B_57]: (v4_pre_topc(k3_xboole_0(B_57, '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1') | ~v4_pre_topc(B_57, '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_128, c_509])).
% 10.80/4.68  tff(c_682, plain, (![B_125]: (v4_pre_topc(k3_xboole_0(B_125, '#skF_3'), '#skF_1') | ~v4_pre_topc(B_125, '#skF_1') | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_36, c_292, c_515])).
% 10.80/4.68  tff(c_728, plain, (![A_18]: (v4_pre_topc(k3_xboole_0(A_18, '#skF_3'), '#skF_1') | ~v4_pre_topc(A_18, '#skF_1') | ~r1_tarski(A_18, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_20, c_682])).
% 10.80/4.68  tff(c_2, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k4_xboole_0(A_1, B_2))=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.80/4.68  tff(c_185, plain, (![A_72, B_73, C_74]: (k7_subset_1(A_72, B_73, C_74)=k4_xboole_0(B_73, C_74) | ~m1_subset_1(B_73, k1_zfmisc_1(A_72)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.80/4.68  tff(c_320, plain, (![C_88]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_88)=k4_xboole_0('#skF_2', C_88))), inference(resolution, [status(thm)], [c_38, c_185])).
% 10.80/4.68  tff(c_10, plain, (![A_7, B_8, C_9]: (m1_subset_1(k7_subset_1(A_7, B_8, C_9), k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.80/4.68  tff(c_329, plain, (![C_88]: (m1_subset_1(k4_xboole_0('#skF_2', C_88), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_320, c_10])).
% 10.80/4.68  tff(c_337, plain, (![C_88]: (m1_subset_1(k4_xboole_0('#skF_2', C_88), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_329])).
% 10.80/4.68  tff(c_6, plain, (![A_5]: (k2_subset_1(A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.80/4.68  tff(c_8, plain, (![A_6]: (m1_subset_1(k2_subset_1(A_6), k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.80/4.68  tff(c_43, plain, (![A_6]: (m1_subset_1(A_6, k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 10.80/4.68  tff(c_200, plain, (![A_6, C_74]: (k7_subset_1(A_6, A_6, C_74)=k4_xboole_0(A_6, C_74))), inference(resolution, [status(thm)], [c_43, c_185])).
% 10.80/4.68  tff(c_160, plain, (![A_63, B_64, C_65]: (m1_subset_1(k7_subset_1(A_63, B_64, C_65), k1_zfmisc_1(A_63)) | ~m1_subset_1(B_64, k1_zfmisc_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.80/4.68  tff(c_18, plain, (![A_18, B_19]: (r1_tarski(A_18, B_19) | ~m1_subset_1(A_18, k1_zfmisc_1(B_19)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.80/4.68  tff(c_167, plain, (![A_63, B_64, C_65]: (r1_tarski(k7_subset_1(A_63, B_64, C_65), A_63) | ~m1_subset_1(B_64, k1_zfmisc_1(A_63)))), inference(resolution, [status(thm)], [c_160, c_18])).
% 10.80/4.68  tff(c_424, plain, (![C_95, A_96, B_97]: (v2_compts_1(C_95, A_96) | ~v4_pre_topc(C_95, A_96) | ~r1_tarski(C_95, B_97) | ~v2_compts_1(B_97, A_96) | ~m1_subset_1(C_95, k1_zfmisc_1(u1_struct_0(A_96))) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96) | ~v2_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_98])).
% 10.80/4.68  tff(c_3428, plain, (![A_305, B_306, C_307, A_308]: (v2_compts_1(k7_subset_1(A_305, B_306, C_307), A_308) | ~v4_pre_topc(k7_subset_1(A_305, B_306, C_307), A_308) | ~v2_compts_1(A_305, A_308) | ~m1_subset_1(k7_subset_1(A_305, B_306, C_307), k1_zfmisc_1(u1_struct_0(A_308))) | ~m1_subset_1(A_305, k1_zfmisc_1(u1_struct_0(A_308))) | ~l1_pre_topc(A_308) | ~v2_pre_topc(A_308) | ~m1_subset_1(B_306, k1_zfmisc_1(A_305)))), inference(resolution, [status(thm)], [c_167, c_424])).
% 10.80/4.69  tff(c_3464, plain, (![A_6, C_74, A_308]: (v2_compts_1(k7_subset_1(A_6, A_6, C_74), A_308) | ~v4_pre_topc(k7_subset_1(A_6, A_6, C_74), A_308) | ~v2_compts_1(A_6, A_308) | ~m1_subset_1(k4_xboole_0(A_6, C_74), k1_zfmisc_1(u1_struct_0(A_308))) | ~m1_subset_1(A_6, k1_zfmisc_1(u1_struct_0(A_308))) | ~l1_pre_topc(A_308) | ~v2_pre_topc(A_308) | ~m1_subset_1(A_6, k1_zfmisc_1(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_200, c_3428])).
% 10.80/4.69  tff(c_17464, plain, (![A_1006, C_1007, A_1008]: (v2_compts_1(k4_xboole_0(A_1006, C_1007), A_1008) | ~v4_pre_topc(k4_xboole_0(A_1006, C_1007), A_1008) | ~v2_compts_1(A_1006, A_1008) | ~m1_subset_1(k4_xboole_0(A_1006, C_1007), k1_zfmisc_1(u1_struct_0(A_1008))) | ~m1_subset_1(A_1006, k1_zfmisc_1(u1_struct_0(A_1008))) | ~l1_pre_topc(A_1008) | ~v2_pre_topc(A_1008))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_200, c_200, c_3464])).
% 10.80/4.69  tff(c_17627, plain, (![C_88]: (v2_compts_1(k4_xboole_0('#skF_2', C_88), '#skF_1') | ~v4_pre_topc(k4_xboole_0('#skF_2', C_88), '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_337, c_17464])).
% 10.80/4.69  tff(c_17788, plain, (![C_1009]: (v2_compts_1(k4_xboole_0('#skF_2', C_1009), '#skF_1') | ~v4_pre_topc(k4_xboole_0('#skF_2', C_1009), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_32, c_17627])).
% 10.80/4.69  tff(c_17815, plain, (![B_2]: (v2_compts_1(k4_xboole_0('#skF_2', k4_xboole_0('#skF_2', B_2)), '#skF_1') | ~v4_pre_topc(k3_xboole_0('#skF_2', B_2), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_17788])).
% 10.80/4.69  tff(c_17858, plain, (![B_1011]: (v2_compts_1(k3_xboole_0('#skF_2', B_1011), '#skF_1') | ~v4_pre_topc(k3_xboole_0('#skF_2', B_1011), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_17815])).
% 10.80/4.69  tff(c_17882, plain, (v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1') | ~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_728, c_17858])).
% 10.80/4.69  tff(c_17909, plain, (v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_295, c_17882])).
% 10.80/4.69  tff(c_17911, plain, $false, inference(negUnitSimplification, [status(thm)], [c_140, c_17909])).
% 10.80/4.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.80/4.69  
% 10.80/4.69  Inference rules
% 10.80/4.69  ----------------------
% 10.80/4.69  #Ref     : 0
% 10.80/4.69  #Sup     : 4103
% 10.80/4.69  #Fact    : 0
% 10.80/4.69  #Define  : 0
% 10.80/4.69  #Split   : 1
% 10.80/4.69  #Chain   : 0
% 10.80/4.69  #Close   : 0
% 10.80/4.69  
% 10.80/4.69  Ordering : KBO
% 10.80/4.69  
% 10.80/4.69  Simplification rules
% 10.80/4.69  ----------------------
% 10.80/4.69  #Subsume      : 98
% 10.80/4.69  #Demod        : 3319
% 10.80/4.69  #Tautology    : 881
% 10.80/4.69  #SimpNegUnit  : 1
% 10.80/4.69  #BackRed      : 1
% 10.80/4.69  
% 10.80/4.69  #Partial instantiations: 0
% 10.80/4.69  #Strategies tried      : 1
% 10.80/4.69  
% 10.80/4.69  Timing (in seconds)
% 10.80/4.69  ----------------------
% 10.80/4.69  Preprocessing        : 0.31
% 10.80/4.69  Parsing              : 0.17
% 10.80/4.69  CNF conversion       : 0.02
% 10.80/4.69  Main loop            : 3.55
% 10.80/4.69  Inferencing          : 0.81
% 10.80/4.69  Reduction            : 1.69
% 10.80/4.69  Demodulation         : 1.43
% 10.80/4.69  BG Simplification    : 0.11
% 10.80/4.69  Subsumption          : 0.72
% 10.80/4.69  Abstraction          : 0.16
% 10.80/4.69  MUC search           : 0.00
% 10.80/4.69  Cooper               : 0.00
% 10.80/4.69  Total                : 3.90
% 10.80/4.69  Index Insertion      : 0.00
% 10.80/4.69  Index Deletion       : 0.00
% 10.80/4.69  Index Matching       : 0.00
% 10.80/4.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
