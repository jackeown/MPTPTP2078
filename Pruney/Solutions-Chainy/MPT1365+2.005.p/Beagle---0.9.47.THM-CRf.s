%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:54 EST 2020

% Result     : Theorem 4.00s
% Output     : CNFRefutation 4.00s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 124 expanded)
%              Number of leaves         :   32 (  60 expanded)
%              Depth                    :    9
%              Number of atoms          :  131 ( 348 expanded)
%              Number of equality atoms :   15 (  27 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_45,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_111,negated_conjecture,(
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

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v8_pre_topc(A)
              & v2_compts_1(B,A) )
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_compts_1)).

tff(f_61,axiom,(
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

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_92,axiom,(
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

tff(c_6,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_71,plain,(
    ! [A_43,B_44] : k1_setfam_1(k2_tarski(A_43,B_44)) = k3_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_86,plain,(
    ! [B_45,A_46] : k1_setfam_1(k2_tarski(B_45,A_46)) = k3_xboole_0(A_46,B_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_71])).

tff(c_14,plain,(
    ! [A_16,B_17] : k1_setfam_1(k2_tarski(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_92,plain,(
    ! [B_45,A_46] : k3_xboole_0(B_45,A_46) = k3_xboole_0(A_46,B_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_14])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_225,plain,(
    ! [A_60,B_61,C_62] :
      ( k9_subset_1(A_60,B_61,C_62) = k3_xboole_0(B_61,C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_234,plain,(
    ! [B_61] : k9_subset_1(u1_struct_0('#skF_1'),B_61,'#skF_3') = k3_xboole_0(B_61,'#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_225])).

tff(c_22,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_254,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_22])).

tff(c_255,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_254])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_28,plain,(
    v8_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_26,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_378,plain,(
    ! [B_75,A_76] :
      ( v4_pre_topc(B_75,A_76)
      | ~ v2_compts_1(B_75,A_76)
      | ~ v8_pre_topc(A_76)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76)
      | ~ v2_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_400,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_378])).

tff(c_422,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_28,c_26,c_400])).

tff(c_24,plain,(
    v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_403,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_378])).

tff(c_425,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_28,c_24,c_403])).

tff(c_699,plain,(
    ! [A_96,B_97,C_98] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(A_96),B_97,C_98),A_96)
      | ~ v4_pre_topc(C_98,A_96)
      | ~ v4_pre_topc(B_97,A_96)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96)
      | ~ v2_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_702,plain,(
    ! [B_61] :
      ( v4_pre_topc(k3_xboole_0(B_61,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc('#skF_3','#skF_1')
      | ~ v4_pre_topc(B_61,'#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_699])).

tff(c_747,plain,(
    ! [B_101] :
      ( v4_pre_topc(k3_xboole_0(B_101,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc(B_101,'#skF_1')
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_425,c_702])).

tff(c_790,plain,
    ( v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_747])).

tff(c_822,plain,(
    v4_pre_topc(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_92,c_790])).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_244,plain,(
    ! [A_64,B_65,C_66] :
      ( k7_subset_1(A_64,B_65,C_66) = k4_xboole_0(B_65,C_66)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_279,plain,(
    ! [C_69] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_3',C_69) = k4_xboole_0('#skF_3',C_69) ),
    inference(resolution,[status(thm)],[c_30,c_244])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] :
      ( m1_subset_1(k7_subset_1(A_7,B_8,C_9),k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_285,plain,(
    ! [C_69] :
      ( m1_subset_1(k4_xboole_0('#skF_3',C_69),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_8])).

tff(c_312,plain,(
    ! [C_71] : m1_subset_1(k4_xboole_0('#skF_3',C_71),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_285])).

tff(c_328,plain,(
    ! [B_4] : m1_subset_1(k3_xboole_0('#skF_3',B_4),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_312])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_455,plain,(
    ! [C_78,A_79,B_80] :
      ( v2_compts_1(C_78,A_79)
      | ~ v4_pre_topc(C_78,A_79)
      | ~ r1_tarski(C_78,B_80)
      | ~ v2_compts_1(B_80,A_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79)
      | ~ v2_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1572,plain,(
    ! [A_143,B_144,A_145] :
      ( v2_compts_1(k3_xboole_0(A_143,B_144),A_145)
      | ~ v4_pre_topc(k3_xboole_0(A_143,B_144),A_145)
      | ~ v2_compts_1(A_143,A_145)
      | ~ m1_subset_1(k3_xboole_0(A_143,B_144),k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ m1_subset_1(A_143,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_pre_topc(A_145)
      | ~ v2_pre_topc(A_145) ) ),
    inference(resolution,[status(thm)],[c_2,c_455])).

tff(c_1617,plain,(
    ! [B_4] :
      ( v2_compts_1(k3_xboole_0('#skF_3',B_4),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0('#skF_3',B_4),'#skF_1')
      | ~ v2_compts_1('#skF_3','#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_328,c_1572])).

tff(c_1826,plain,(
    ! [B_148] :
      ( v2_compts_1(k3_xboole_0('#skF_3',B_148),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0('#skF_3',B_148),'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_24,c_1617])).

tff(c_1835,plain,(
    v2_compts_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_822,c_1826])).

tff(c_1849,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_255,c_1835])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:29:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.00/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.00/1.71  
% 4.00/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.00/1.72  %$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 4.00/1.72  
% 4.00/1.72  %Foreground sorts:
% 4.00/1.72  
% 4.00/1.72  
% 4.00/1.72  %Background operators:
% 4.00/1.72  
% 4.00/1.72  
% 4.00/1.72  %Foreground operators:
% 4.00/1.72  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 4.00/1.72  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 4.00/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.00/1.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.00/1.72  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.00/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.00/1.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.00/1.72  tff('#skF_2', type, '#skF_2': $i).
% 4.00/1.72  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.00/1.72  tff('#skF_3', type, '#skF_3': $i).
% 4.00/1.72  tff('#skF_1', type, '#skF_1': $i).
% 4.00/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.00/1.72  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.00/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.00/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.00/1.72  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.00/1.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.00/1.72  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.00/1.72  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.00/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.00/1.72  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.00/1.72  
% 4.00/1.73  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.00/1.73  tff(f_45, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.00/1.73  tff(f_111, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v8_pre_topc(A) & v2_compts_1(B, A)) & v2_compts_1(C, A)) => v2_compts_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_compts_1)).
% 4.00/1.73  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.00/1.73  tff(f_74, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v8_pre_topc(A) & v2_compts_1(B, A)) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_compts_1)).
% 4.00/1.73  tff(f_61, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & v4_pre_topc(C, A)) => v4_pre_topc(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tops_1)).
% 4.00/1.73  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.00/1.73  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.00/1.73  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 4.00/1.73  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.00/1.73  tff(f_92, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v2_compts_1(B, A) & r1_tarski(C, B)) & v4_pre_topc(C, A)) => v2_compts_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_compts_1)).
% 4.00/1.73  tff(c_6, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.00/1.73  tff(c_71, plain, (![A_43, B_44]: (k1_setfam_1(k2_tarski(A_43, B_44))=k3_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.00/1.73  tff(c_86, plain, (![B_45, A_46]: (k1_setfam_1(k2_tarski(B_45, A_46))=k3_xboole_0(A_46, B_45))), inference(superposition, [status(thm), theory('equality')], [c_6, c_71])).
% 4.00/1.73  tff(c_14, plain, (![A_16, B_17]: (k1_setfam_1(k2_tarski(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.00/1.73  tff(c_92, plain, (![B_45, A_46]: (k3_xboole_0(B_45, A_46)=k3_xboole_0(A_46, B_45))), inference(superposition, [status(thm), theory('equality')], [c_86, c_14])).
% 4.00/1.73  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.00/1.73  tff(c_225, plain, (![A_60, B_61, C_62]: (k9_subset_1(A_60, B_61, C_62)=k3_xboole_0(B_61, C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.00/1.73  tff(c_234, plain, (![B_61]: (k9_subset_1(u1_struct_0('#skF_1'), B_61, '#skF_3')=k3_xboole_0(B_61, '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_225])).
% 4.00/1.73  tff(c_22, plain, (~v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.00/1.73  tff(c_254, plain, (~v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_234, c_22])).
% 4.00/1.73  tff(c_255, plain, (~v2_compts_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_254])).
% 4.00/1.73  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.00/1.73  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.00/1.73  tff(c_28, plain, (v8_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.00/1.73  tff(c_26, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.00/1.73  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.00/1.73  tff(c_378, plain, (![B_75, A_76]: (v4_pre_topc(B_75, A_76) | ~v2_compts_1(B_75, A_76) | ~v8_pre_topc(A_76) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76) | ~v2_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.00/1.73  tff(c_400, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_378])).
% 4.00/1.73  tff(c_422, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_28, c_26, c_400])).
% 4.00/1.73  tff(c_24, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.00/1.73  tff(c_403, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_378])).
% 4.00/1.73  tff(c_425, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_28, c_24, c_403])).
% 4.00/1.73  tff(c_699, plain, (![A_96, B_97, C_98]: (v4_pre_topc(k9_subset_1(u1_struct_0(A_96), B_97, C_98), A_96) | ~v4_pre_topc(C_98, A_96) | ~v4_pre_topc(B_97, A_96) | ~m1_subset_1(C_98, k1_zfmisc_1(u1_struct_0(A_96))) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96) | ~v2_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.00/1.73  tff(c_702, plain, (![B_61]: (v4_pre_topc(k3_xboole_0(B_61, '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1') | ~v4_pre_topc(B_61, '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_234, c_699])).
% 4.00/1.73  tff(c_747, plain, (![B_101]: (v4_pre_topc(k3_xboole_0(B_101, '#skF_3'), '#skF_1') | ~v4_pre_topc(B_101, '#skF_1') | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_425, c_702])).
% 4.00/1.73  tff(c_790, plain, (v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_747])).
% 4.00/1.73  tff(c_822, plain, (v4_pre_topc(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_422, c_92, c_790])).
% 4.00/1.73  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k4_xboole_0(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.00/1.73  tff(c_244, plain, (![A_64, B_65, C_66]: (k7_subset_1(A_64, B_65, C_66)=k4_xboole_0(B_65, C_66) | ~m1_subset_1(B_65, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.00/1.73  tff(c_279, plain, (![C_69]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_3', C_69)=k4_xboole_0('#skF_3', C_69))), inference(resolution, [status(thm)], [c_30, c_244])).
% 4.00/1.73  tff(c_8, plain, (![A_7, B_8, C_9]: (m1_subset_1(k7_subset_1(A_7, B_8, C_9), k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.00/1.73  tff(c_285, plain, (![C_69]: (m1_subset_1(k4_xboole_0('#skF_3', C_69), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_279, c_8])).
% 4.00/1.73  tff(c_312, plain, (![C_71]: (m1_subset_1(k4_xboole_0('#skF_3', C_71), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_285])).
% 4.00/1.73  tff(c_328, plain, (![B_4]: (m1_subset_1(k3_xboole_0('#skF_3', B_4), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_4, c_312])).
% 4.00/1.73  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.00/1.73  tff(c_455, plain, (![C_78, A_79, B_80]: (v2_compts_1(C_78, A_79) | ~v4_pre_topc(C_78, A_79) | ~r1_tarski(C_78, B_80) | ~v2_compts_1(B_80, A_79) | ~m1_subset_1(C_78, k1_zfmisc_1(u1_struct_0(A_79))) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79) | ~v2_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.00/1.73  tff(c_1572, plain, (![A_143, B_144, A_145]: (v2_compts_1(k3_xboole_0(A_143, B_144), A_145) | ~v4_pre_topc(k3_xboole_0(A_143, B_144), A_145) | ~v2_compts_1(A_143, A_145) | ~m1_subset_1(k3_xboole_0(A_143, B_144), k1_zfmisc_1(u1_struct_0(A_145))) | ~m1_subset_1(A_143, k1_zfmisc_1(u1_struct_0(A_145))) | ~l1_pre_topc(A_145) | ~v2_pre_topc(A_145))), inference(resolution, [status(thm)], [c_2, c_455])).
% 4.00/1.73  tff(c_1617, plain, (![B_4]: (v2_compts_1(k3_xboole_0('#skF_3', B_4), '#skF_1') | ~v4_pre_topc(k3_xboole_0('#skF_3', B_4), '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_328, c_1572])).
% 4.00/1.73  tff(c_1826, plain, (![B_148]: (v2_compts_1(k3_xboole_0('#skF_3', B_148), '#skF_1') | ~v4_pre_topc(k3_xboole_0('#skF_3', B_148), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_24, c_1617])).
% 4.00/1.73  tff(c_1835, plain, (v2_compts_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_822, c_1826])).
% 4.00/1.73  tff(c_1849, plain, $false, inference(negUnitSimplification, [status(thm)], [c_255, c_1835])).
% 4.00/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.00/1.73  
% 4.00/1.73  Inference rules
% 4.00/1.73  ----------------------
% 4.00/1.73  #Ref     : 0
% 4.00/1.73  #Sup     : 408
% 4.00/1.73  #Fact    : 0
% 4.00/1.73  #Define  : 0
% 4.00/1.73  #Split   : 0
% 4.00/1.73  #Chain   : 0
% 4.00/1.73  #Close   : 0
% 4.00/1.73  
% 4.00/1.73  Ordering : KBO
% 4.00/1.73  
% 4.00/1.73  Simplification rules
% 4.00/1.73  ----------------------
% 4.00/1.73  #Subsume      : 3
% 4.00/1.73  #Demod        : 315
% 4.00/1.73  #Tautology    : 111
% 4.00/1.73  #SimpNegUnit  : 1
% 4.00/1.73  #BackRed      : 1
% 4.00/1.73  
% 4.00/1.73  #Partial instantiations: 0
% 4.00/1.73  #Strategies tried      : 1
% 4.00/1.73  
% 4.00/1.73  Timing (in seconds)
% 4.00/1.73  ----------------------
% 4.00/1.74  Preprocessing        : 0.32
% 4.29/1.74  Parsing              : 0.17
% 4.29/1.74  CNF conversion       : 0.02
% 4.29/1.74  Main loop            : 0.64
% 4.29/1.74  Inferencing          : 0.19
% 4.29/1.74  Reduction            : 0.29
% 4.29/1.74  Demodulation         : 0.23
% 4.29/1.74  BG Simplification    : 0.03
% 4.29/1.74  Subsumption          : 0.09
% 4.29/1.74  Abstraction          : 0.04
% 4.29/1.74  MUC search           : 0.00
% 4.29/1.74  Cooper               : 0.00
% 4.29/1.74  Total                : 1.00
% 4.29/1.74  Index Insertion      : 0.00
% 4.29/1.74  Index Deletion       : 0.00
% 4.29/1.74  Index Matching       : 0.00
% 4.29/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
