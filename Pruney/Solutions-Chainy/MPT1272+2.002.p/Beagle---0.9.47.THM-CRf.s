%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:58 EST 2020

% Result     : Theorem 24.84s
% Output     : CNFRefutation 24.84s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 160 expanded)
%              Number of leaves         :   42 (  74 expanded)
%              Depth                    :   16
%              Number of atoms          :  156 ( 332 expanded)
%              Number of equality atoms :   14 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tops_1 > v2_tops_1 > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

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

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_176,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_tops_1(B,A)
             => v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_tops_1)).

tff(f_166,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_130,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
          <=> v2_tops_1(k2_pre_topc(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_1)).

tff(f_112,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_150,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_143,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k2_tops_1(A,k3_subset_1(u1_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

tff(f_136,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_157,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k2_tops_1(A,k2_pre_topc(A,B)),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_tops_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_121,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).

tff(c_80,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_78,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_3242,plain,(
    ! [B_248,A_249] :
      ( r1_tarski(B_248,k2_tops_1(A_249,B_248))
      | ~ v2_tops_1(B_248,A_249)
      | ~ m1_subset_1(B_248,k1_zfmisc_1(u1_struct_0(A_249)))
      | ~ l1_pre_topc(A_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_3254,plain,
    ( r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_78,c_3242])).

tff(c_3267,plain,
    ( r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_3254])).

tff(c_3271,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3267])).

tff(c_76,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_3524,plain,(
    ! [A_259,B_260] :
      ( v2_tops_1(k2_pre_topc(A_259,B_260),A_259)
      | ~ v3_tops_1(B_260,A_259)
      | ~ m1_subset_1(B_260,k1_zfmisc_1(u1_struct_0(A_259)))
      | ~ l1_pre_topc(A_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_3536,plain,
    ( v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_78,c_3524])).

tff(c_3549,plain,(
    v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_3536])).

tff(c_52,plain,(
    ! [A_51,B_52] :
      ( m1_subset_1(k2_pre_topc(A_51,B_52),k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_3261,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(k2_pre_topc(A_51,B_52),k2_tops_1(A_51,k2_pre_topc(A_51,B_52)))
      | ~ v2_tops_1(k2_pre_topc(A_51,B_52),A_51)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(resolution,[status(thm)],[c_52,c_3242])).

tff(c_6340,plain,(
    ! [A_306,B_307] :
      ( k4_subset_1(u1_struct_0(A_306),B_307,k2_tops_1(A_306,B_307)) = k2_pre_topc(A_306,B_307)
      | ~ m1_subset_1(B_307,k1_zfmisc_1(u1_struct_0(A_306)))
      | ~ l1_pre_topc(A_306) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_6352,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_78,c_6340])).

tff(c_6365,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_6352])).

tff(c_32,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(k3_subset_1(A_30,B_31),k1_zfmisc_1(A_30))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4977,plain,(
    ! [A_284,B_285] :
      ( k2_tops_1(A_284,k3_subset_1(u1_struct_0(A_284),B_285)) = k2_tops_1(A_284,B_285)
      | ~ m1_subset_1(B_285,k1_zfmisc_1(u1_struct_0(A_284)))
      | ~ l1_pre_topc(A_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_4989,plain,
    ( k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_78,c_4977])).

tff(c_5002,plain,(
    k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4989])).

tff(c_1660,plain,(
    ! [A_201,B_202] :
      ( m1_subset_1(k2_tops_1(A_201,B_202),k1_zfmisc_1(u1_struct_0(A_201)))
      | ~ m1_subset_1(B_202,k1_zfmisc_1(u1_struct_0(A_201)))
      | ~ l1_pre_topc(A_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_46,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,B_47)
      | ~ m1_subset_1(A_46,k1_zfmisc_1(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_15656,plain,(
    ! [A_464,B_465] :
      ( r1_tarski(k2_tops_1(A_464,B_465),u1_struct_0(A_464))
      | ~ m1_subset_1(B_465,k1_zfmisc_1(u1_struct_0(A_464)))
      | ~ l1_pre_topc(A_464) ) ),
    inference(resolution,[status(thm)],[c_1660,c_46])).

tff(c_15679,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5002,c_15656])).

tff(c_15691,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_15679])).

tff(c_88923,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_15691])).

tff(c_88926,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_32,c_88923])).

tff(c_88933,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_88926])).

tff(c_88934,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_15691])).

tff(c_48,plain,(
    ! [A_46,B_47] :
      ( m1_subset_1(A_46,k1_zfmisc_1(B_47))
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2717,plain,(
    ! [A_232,B_233,C_234] :
      ( k4_subset_1(A_232,B_233,C_234) = k2_xboole_0(B_233,C_234)
      | ~ m1_subset_1(C_234,k1_zfmisc_1(A_232))
      | ~ m1_subset_1(B_233,k1_zfmisc_1(A_232)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_21742,plain,(
    ! [B_529,B_530,A_531] :
      ( k4_subset_1(B_529,B_530,A_531) = k2_xboole_0(B_530,A_531)
      | ~ m1_subset_1(B_530,k1_zfmisc_1(B_529))
      | ~ r1_tarski(A_531,B_529) ) ),
    inference(resolution,[status(thm)],[c_48,c_2717])).

tff(c_21761,plain,(
    ! [A_531] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_531) = k2_xboole_0('#skF_2',A_531)
      | ~ r1_tarski(A_531,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_78,c_21742])).

tff(c_88946,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_88934,c_21761])).

tff(c_88972,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6365,c_88946])).

tff(c_6,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(k2_xboole_0(A_5,B_6),C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_93201,plain,(
    ! [C_1096] :
      ( r1_tarski('#skF_2',C_1096)
      | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),C_1096) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88972,c_6])).

tff(c_93213,plain,
    ( r1_tarski('#skF_2',k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | ~ v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_3261,c_93201])).

tff(c_93266,plain,(
    r1_tarski('#skF_2',k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_3549,c_93213])).

tff(c_4069,plain,(
    ! [A_269,B_270] :
      ( r1_tarski(k2_tops_1(A_269,k2_pre_topc(A_269,B_270)),k2_tops_1(A_269,B_270))
      | ~ m1_subset_1(B_270,k1_zfmisc_1(u1_struct_0(A_269)))
      | ~ l1_pre_topc(A_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_10,plain,(
    ! [A_10,C_12,B_11] :
      ( r1_tarski(A_10,C_12)
      | ~ r1_tarski(B_11,C_12)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4076,plain,(
    ! [A_10,A_269,B_270] :
      ( r1_tarski(A_10,k2_tops_1(A_269,B_270))
      | ~ r1_tarski(A_10,k2_tops_1(A_269,k2_pre_topc(A_269,B_270)))
      | ~ m1_subset_1(B_270,k1_zfmisc_1(u1_struct_0(A_269)))
      | ~ l1_pre_topc(A_269) ) ),
    inference(resolution,[status(thm)],[c_4069,c_10])).

tff(c_93295,plain,
    ( r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_93266,c_4076])).

tff(c_93319,plain,(
    r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_93295])).

tff(c_70,plain,(
    ! [B_72,A_70] :
      ( v2_tops_1(B_72,A_70)
      | ~ r1_tarski(B_72,k2_tops_1(A_70,B_72))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_93349,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_93319,c_70])).

tff(c_93365,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_93349])).

tff(c_93367,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3271,c_93365])).

tff(c_93369,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_3267])).

tff(c_95147,plain,(
    ! [A_1138,B_1139] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_1138),B_1139),A_1138)
      | ~ v2_tops_1(B_1139,A_1138)
      | ~ m1_subset_1(B_1139,k1_zfmisc_1(u1_struct_0(A_1138)))
      | ~ l1_pre_topc(A_1138) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_74,plain,(
    ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_95150,plain,
    ( ~ v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_95147,c_74])).

tff(c_95166,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_93369,c_95150])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:31:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 24.84/16.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 24.84/16.01  
% 24.84/16.01  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 24.84/16.02  %$ v3_tops_1 > v2_tops_1 > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 24.84/16.02  
% 24.84/16.02  %Foreground sorts:
% 24.84/16.02  
% 24.84/16.02  
% 24.84/16.02  %Background operators:
% 24.84/16.02  
% 24.84/16.02  
% 24.84/16.02  %Foreground operators:
% 24.84/16.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 24.84/16.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 24.84/16.02  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 24.84/16.02  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 24.84/16.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 24.84/16.02  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 24.84/16.02  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 24.84/16.02  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 24.84/16.02  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 24.84/16.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 24.84/16.02  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 24.84/16.02  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 24.84/16.02  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 24.84/16.02  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 24.84/16.02  tff('#skF_2', type, '#skF_2': $i).
% 24.84/16.02  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 24.84/16.02  tff('#skF_1', type, '#skF_1': $i).
% 24.84/16.02  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 24.84/16.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 24.84/16.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 24.84/16.02  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 24.84/16.02  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 24.84/16.02  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 24.84/16.02  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 24.84/16.02  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 24.84/16.02  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 24.84/16.02  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 24.84/16.02  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 24.84/16.02  
% 24.84/16.03  tff(f_176, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_tops_1)).
% 24.84/16.03  tff(f_166, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tops_1)).
% 24.84/16.03  tff(f_130, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) <=> v2_tops_1(k2_pre_topc(A, B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tops_1)).
% 24.84/16.03  tff(f_112, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 24.84/16.03  tff(f_150, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 24.84/16.03  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 24.84/16.03  tff(f_143, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k2_tops_1(A, k3_subset_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_1)).
% 24.84/16.03  tff(f_136, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 24.84/16.03  tff(f_100, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 24.84/16.03  tff(f_79, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 24.84/16.03  tff(f_33, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 24.84/16.03  tff(f_157, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_tops_1(A, k2_pre_topc(A, B)), k2_tops_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_tops_1)).
% 24.84/16.03  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 24.84/16.03  tff(f_121, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_1)).
% 24.84/16.03  tff(c_80, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_176])).
% 24.84/16.03  tff(c_78, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_176])).
% 24.84/16.03  tff(c_3242, plain, (![B_248, A_249]: (r1_tarski(B_248, k2_tops_1(A_249, B_248)) | ~v2_tops_1(B_248, A_249) | ~m1_subset_1(B_248, k1_zfmisc_1(u1_struct_0(A_249))) | ~l1_pre_topc(A_249))), inference(cnfTransformation, [status(thm)], [f_166])).
% 24.84/16.03  tff(c_3254, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_78, c_3242])).
% 24.84/16.03  tff(c_3267, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_3254])).
% 24.84/16.03  tff(c_3271, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_3267])).
% 24.84/16.03  tff(c_76, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_176])).
% 24.84/16.03  tff(c_3524, plain, (![A_259, B_260]: (v2_tops_1(k2_pre_topc(A_259, B_260), A_259) | ~v3_tops_1(B_260, A_259) | ~m1_subset_1(B_260, k1_zfmisc_1(u1_struct_0(A_259))) | ~l1_pre_topc(A_259))), inference(cnfTransformation, [status(thm)], [f_130])).
% 24.84/16.03  tff(c_3536, plain, (v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_78, c_3524])).
% 24.84/16.03  tff(c_3549, plain, (v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_3536])).
% 24.84/16.03  tff(c_52, plain, (![A_51, B_52]: (m1_subset_1(k2_pre_topc(A_51, B_52), k1_zfmisc_1(u1_struct_0(A_51))) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_112])).
% 24.84/16.03  tff(c_3261, plain, (![A_51, B_52]: (r1_tarski(k2_pre_topc(A_51, B_52), k2_tops_1(A_51, k2_pre_topc(A_51, B_52))) | ~v2_tops_1(k2_pre_topc(A_51, B_52), A_51) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(resolution, [status(thm)], [c_52, c_3242])).
% 24.84/16.03  tff(c_6340, plain, (![A_306, B_307]: (k4_subset_1(u1_struct_0(A_306), B_307, k2_tops_1(A_306, B_307))=k2_pre_topc(A_306, B_307) | ~m1_subset_1(B_307, k1_zfmisc_1(u1_struct_0(A_306))) | ~l1_pre_topc(A_306))), inference(cnfTransformation, [status(thm)], [f_150])).
% 24.84/16.03  tff(c_6352, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_78, c_6340])).
% 24.84/16.03  tff(c_6365, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_6352])).
% 24.84/16.03  tff(c_32, plain, (![A_30, B_31]: (m1_subset_1(k3_subset_1(A_30, B_31), k1_zfmisc_1(A_30)) | ~m1_subset_1(B_31, k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 24.84/16.03  tff(c_4977, plain, (![A_284, B_285]: (k2_tops_1(A_284, k3_subset_1(u1_struct_0(A_284), B_285))=k2_tops_1(A_284, B_285) | ~m1_subset_1(B_285, k1_zfmisc_1(u1_struct_0(A_284))) | ~l1_pre_topc(A_284))), inference(cnfTransformation, [status(thm)], [f_143])).
% 24.84/16.03  tff(c_4989, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_78, c_4977])).
% 24.84/16.03  tff(c_5002, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_4989])).
% 24.84/16.03  tff(c_1660, plain, (![A_201, B_202]: (m1_subset_1(k2_tops_1(A_201, B_202), k1_zfmisc_1(u1_struct_0(A_201))) | ~m1_subset_1(B_202, k1_zfmisc_1(u1_struct_0(A_201))) | ~l1_pre_topc(A_201))), inference(cnfTransformation, [status(thm)], [f_136])).
% 24.84/16.03  tff(c_46, plain, (![A_46, B_47]: (r1_tarski(A_46, B_47) | ~m1_subset_1(A_46, k1_zfmisc_1(B_47)))), inference(cnfTransformation, [status(thm)], [f_100])).
% 24.84/16.03  tff(c_15656, plain, (![A_464, B_465]: (r1_tarski(k2_tops_1(A_464, B_465), u1_struct_0(A_464)) | ~m1_subset_1(B_465, k1_zfmisc_1(u1_struct_0(A_464))) | ~l1_pre_topc(A_464))), inference(resolution, [status(thm)], [c_1660, c_46])).
% 24.84/16.03  tff(c_15679, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5002, c_15656])).
% 24.84/16.03  tff(c_15691, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_15679])).
% 24.84/16.03  tff(c_88923, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_15691])).
% 24.84/16.03  tff(c_88926, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_32, c_88923])).
% 24.84/16.03  tff(c_88933, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_88926])).
% 24.84/16.03  tff(c_88934, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_15691])).
% 24.84/16.03  tff(c_48, plain, (![A_46, B_47]: (m1_subset_1(A_46, k1_zfmisc_1(B_47)) | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_100])).
% 24.84/16.03  tff(c_2717, plain, (![A_232, B_233, C_234]: (k4_subset_1(A_232, B_233, C_234)=k2_xboole_0(B_233, C_234) | ~m1_subset_1(C_234, k1_zfmisc_1(A_232)) | ~m1_subset_1(B_233, k1_zfmisc_1(A_232)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 24.84/16.03  tff(c_21742, plain, (![B_529, B_530, A_531]: (k4_subset_1(B_529, B_530, A_531)=k2_xboole_0(B_530, A_531) | ~m1_subset_1(B_530, k1_zfmisc_1(B_529)) | ~r1_tarski(A_531, B_529))), inference(resolution, [status(thm)], [c_48, c_2717])).
% 24.84/16.03  tff(c_21761, plain, (![A_531]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_531)=k2_xboole_0('#skF_2', A_531) | ~r1_tarski(A_531, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_78, c_21742])).
% 24.84/16.03  tff(c_88946, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_88934, c_21761])).
% 24.84/16.03  tff(c_88972, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6365, c_88946])).
% 24.84/16.03  tff(c_6, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(k2_xboole_0(A_5, B_6), C_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 24.84/16.03  tff(c_93201, plain, (![C_1096]: (r1_tarski('#skF_2', C_1096) | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), C_1096))), inference(superposition, [status(thm), theory('equality')], [c_88972, c_6])).
% 24.84/16.03  tff(c_93213, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))) | ~v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_3261, c_93201])).
% 24.84/16.03  tff(c_93266, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_3549, c_93213])).
% 24.84/16.03  tff(c_4069, plain, (![A_269, B_270]: (r1_tarski(k2_tops_1(A_269, k2_pre_topc(A_269, B_270)), k2_tops_1(A_269, B_270)) | ~m1_subset_1(B_270, k1_zfmisc_1(u1_struct_0(A_269))) | ~l1_pre_topc(A_269))), inference(cnfTransformation, [status(thm)], [f_157])).
% 24.84/16.03  tff(c_10, plain, (![A_10, C_12, B_11]: (r1_tarski(A_10, C_12) | ~r1_tarski(B_11, C_12) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 24.84/16.03  tff(c_4076, plain, (![A_10, A_269, B_270]: (r1_tarski(A_10, k2_tops_1(A_269, B_270)) | ~r1_tarski(A_10, k2_tops_1(A_269, k2_pre_topc(A_269, B_270))) | ~m1_subset_1(B_270, k1_zfmisc_1(u1_struct_0(A_269))) | ~l1_pre_topc(A_269))), inference(resolution, [status(thm)], [c_4069, c_10])).
% 24.84/16.03  tff(c_93295, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_93266, c_4076])).
% 24.84/16.03  tff(c_93319, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_93295])).
% 24.84/16.03  tff(c_70, plain, (![B_72, A_70]: (v2_tops_1(B_72, A_70) | ~r1_tarski(B_72, k2_tops_1(A_70, B_72)) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_166])).
% 24.84/16.03  tff(c_93349, plain, (v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_93319, c_70])).
% 24.84/16.03  tff(c_93365, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_93349])).
% 24.84/16.03  tff(c_93367, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3271, c_93365])).
% 24.84/16.03  tff(c_93369, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_3267])).
% 24.84/16.03  tff(c_95147, plain, (![A_1138, B_1139]: (v1_tops_1(k3_subset_1(u1_struct_0(A_1138), B_1139), A_1138) | ~v2_tops_1(B_1139, A_1138) | ~m1_subset_1(B_1139, k1_zfmisc_1(u1_struct_0(A_1138))) | ~l1_pre_topc(A_1138))), inference(cnfTransformation, [status(thm)], [f_121])).
% 24.84/16.03  tff(c_74, plain, (~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_176])).
% 24.84/16.03  tff(c_95150, plain, (~v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_95147, c_74])).
% 24.84/16.03  tff(c_95166, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_93369, c_95150])).
% 24.84/16.03  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 24.84/16.03  
% 24.84/16.03  Inference rules
% 24.84/16.03  ----------------------
% 24.84/16.03  #Ref     : 0
% 24.84/16.03  #Sup     : 22954
% 24.84/16.03  #Fact    : 0
% 24.84/16.03  #Define  : 0
% 24.84/16.03  #Split   : 6
% 24.84/16.03  #Chain   : 0
% 24.84/16.03  #Close   : 0
% 24.84/16.03  
% 24.84/16.03  Ordering : KBO
% 24.84/16.03  
% 24.84/16.03  Simplification rules
% 24.84/16.03  ----------------------
% 24.84/16.03  #Subsume      : 1244
% 24.84/16.03  #Demod        : 28017
% 24.84/16.03  #Tautology    : 15093
% 24.84/16.03  #SimpNegUnit  : 1
% 24.84/16.03  #BackRed      : 62
% 24.84/16.03  
% 24.84/16.03  #Partial instantiations: 0
% 24.84/16.03  #Strategies tried      : 1
% 24.84/16.03  
% 24.84/16.03  Timing (in seconds)
% 24.84/16.03  ----------------------
% 24.84/16.03  Preprocessing        : 0.37
% 24.84/16.03  Parsing              : 0.20
% 24.84/16.03  CNF conversion       : 0.03
% 24.84/16.03  Main loop            : 14.91
% 24.84/16.03  Inferencing          : 1.81
% 24.84/16.03  Reduction            : 9.11
% 24.84/16.03  Demodulation         : 8.20
% 24.84/16.03  BG Simplification    : 0.19
% 24.84/16.03  Subsumption          : 3.18
% 24.84/16.04  Abstraction          : 0.37
% 24.84/16.04  MUC search           : 0.00
% 24.84/16.04  Cooper               : 0.00
% 24.84/16.04  Total                : 15.31
% 24.84/16.04  Index Insertion      : 0.00
% 24.84/16.04  Index Deletion       : 0.00
% 24.84/16.04  Index Matching       : 0.00
% 24.84/16.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
