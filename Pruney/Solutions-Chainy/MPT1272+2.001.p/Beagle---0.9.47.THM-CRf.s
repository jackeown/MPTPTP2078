%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:58 EST 2020

% Result     : Theorem 24.53s
% Output     : CNFRefutation 24.53s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 156 expanded)
%              Number of leaves         :   38 (  70 expanded)
%              Depth                    :   16
%              Number of atoms          :  156 ( 332 expanded)
%              Number of equality atoms :   14 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tops_1 > v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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

tff(f_179,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_tops_1(B,A)
             => v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_tops_1)).

tff(f_169,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_133,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
          <=> v2_tops_1(k2_pre_topc(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_1)).

tff(f_115,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_153,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_146,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k2_tops_1(A,k3_subset_1(u1_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

tff(f_139,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_160,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k2_tops_1(A,k2_pre_topc(A,B)),k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tops_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_124,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

tff(c_78,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_76,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_2253,plain,(
    ! [B_204,A_205] :
      ( r1_tarski(B_204,k2_tops_1(A_205,B_204))
      | ~ v2_tops_1(B_204,A_205)
      | ~ m1_subset_1(B_204,k1_zfmisc_1(u1_struct_0(A_205)))
      | ~ l1_pre_topc(A_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_2265,plain,
    ( r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_2253])).

tff(c_2272,plain,
    ( r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2265])).

tff(c_2276,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2272])).

tff(c_74,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_2749,plain,(
    ! [A_231,B_232] :
      ( v2_tops_1(k2_pre_topc(A_231,B_232),A_231)
      | ~ v3_tops_1(B_232,A_231)
      | ~ m1_subset_1(B_232,k1_zfmisc_1(u1_struct_0(A_231)))
      | ~ l1_pre_topc(A_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2761,plain,
    ( v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_2749])).

tff(c_2768,plain,(
    v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_2761])).

tff(c_50,plain,(
    ! [A_50,B_51] :
      ( m1_subset_1(k2_pre_topc(A_50,B_51),k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2266,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(k2_pre_topc(A_50,B_51),k2_tops_1(A_50,k2_pre_topc(A_50,B_51)))
      | ~ v2_tops_1(k2_pre_topc(A_50,B_51),A_50)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(resolution,[status(thm)],[c_50,c_2253])).

tff(c_4812,plain,(
    ! [A_288,B_289] :
      ( k4_subset_1(u1_struct_0(A_288),B_289,k2_tops_1(A_288,B_289)) = k2_pre_topc(A_288,B_289)
      | ~ m1_subset_1(B_289,k1_zfmisc_1(u1_struct_0(A_288)))
      | ~ l1_pre_topc(A_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_4830,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_4812])).

tff(c_4839,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_4830])).

tff(c_36,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(k3_subset_1(A_33,B_34),k1_zfmisc_1(A_33))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_3255,plain,(
    ! [A_255,B_256] :
      ( k2_tops_1(A_255,k3_subset_1(u1_struct_0(A_255),B_256)) = k2_tops_1(A_255,B_256)
      | ~ m1_subset_1(B_256,k1_zfmisc_1(u1_struct_0(A_255)))
      | ~ l1_pre_topc(A_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_3267,plain,
    ( k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_3255])).

tff(c_3274,plain,(
    k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_3267])).

tff(c_1743,plain,(
    ! [A_192,B_193] :
      ( m1_subset_1(k2_tops_1(A_192,B_193),k1_zfmisc_1(u1_struct_0(A_192)))
      | ~ m1_subset_1(B_193,k1_zfmisc_1(u1_struct_0(A_192)))
      | ~ l1_pre_topc(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_46,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(A_48,B_49)
      | ~ m1_subset_1(A_48,k1_zfmisc_1(B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_14421,plain,(
    ! [A_411,B_412] :
      ( r1_tarski(k2_tops_1(A_411,B_412),u1_struct_0(A_411))
      | ~ m1_subset_1(B_412,k1_zfmisc_1(u1_struct_0(A_411)))
      | ~ l1_pre_topc(A_411) ) ),
    inference(resolution,[status(thm)],[c_1743,c_46])).

tff(c_14440,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3274,c_14421])).

tff(c_14450,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_14440])).

tff(c_88666,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_14450])).

tff(c_88669,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_36,c_88666])).

tff(c_88676,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_88669])).

tff(c_88677,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_14450])).

tff(c_48,plain,(
    ! [A_48,B_49] :
      ( m1_subset_1(A_48,k1_zfmisc_1(B_49))
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2490,plain,(
    ! [A_215,B_216,C_217] :
      ( k4_subset_1(A_215,B_216,C_217) = k2_xboole_0(B_216,C_217)
      | ~ m1_subset_1(C_217,k1_zfmisc_1(A_215))
      | ~ m1_subset_1(B_216,k1_zfmisc_1(A_215)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_17063,plain,(
    ! [B_437,B_438,A_439] :
      ( k4_subset_1(B_437,B_438,A_439) = k2_xboole_0(B_438,A_439)
      | ~ m1_subset_1(B_438,k1_zfmisc_1(B_437))
      | ~ r1_tarski(A_439,B_437) ) ),
    inference(resolution,[status(thm)],[c_48,c_2490])).

tff(c_17085,plain,(
    ! [A_439] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_439) = k2_xboole_0('#skF_2',A_439)
      | ~ r1_tarski(A_439,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_76,c_17063])).

tff(c_88692,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_88677,c_17085])).

tff(c_88713,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4839,c_88692])).

tff(c_12,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_tarski(A_7,C_9)
      | ~ r1_tarski(k2_xboole_0(A_7,B_8),C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_95516,plain,(
    ! [C_1156] :
      ( r1_tarski('#skF_2',C_1156)
      | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_2'),C_1156) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88713,c_12])).

tff(c_95624,plain,
    ( r1_tarski('#skF_2',k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')))
    | ~ v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2266,c_95516])).

tff(c_95716,plain,(
    r1_tarski('#skF_2',k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_2768,c_95624])).

tff(c_3631,plain,(
    ! [A_266,B_267] :
      ( r1_tarski(k2_tops_1(A_266,k2_pre_topc(A_266,B_267)),k2_tops_1(A_266,B_267))
      | ~ m1_subset_1(B_267,k1_zfmisc_1(u1_struct_0(A_266)))
      | ~ l1_pre_topc(A_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_16,plain,(
    ! [A_12,C_14,B_13] :
      ( r1_tarski(A_12,C_14)
      | ~ r1_tarski(B_13,C_14)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3646,plain,(
    ! [A_12,A_266,B_267] :
      ( r1_tarski(A_12,k2_tops_1(A_266,B_267))
      | ~ r1_tarski(A_12,k2_tops_1(A_266,k2_pre_topc(A_266,B_267)))
      | ~ m1_subset_1(B_267,k1_zfmisc_1(u1_struct_0(A_266)))
      | ~ l1_pre_topc(A_266) ) ),
    inference(resolution,[status(thm)],[c_3631,c_16])).

tff(c_96141,plain,
    ( r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_95716,c_3646])).

tff(c_96162,plain,(
    r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_96141])).

tff(c_68,plain,(
    ! [B_71,A_69] :
      ( v2_tops_1(B_71,A_69)
      | ~ r1_tarski(B_71,k2_tops_1(A_69,B_71))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_96188,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_96162,c_68])).

tff(c_96203,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_96188])).

tff(c_96205,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2276,c_96203])).

tff(c_96207,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_2272])).

tff(c_97646,plain,(
    ! [A_1222,B_1223] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_1222),B_1223),A_1222)
      | ~ v2_tops_1(B_1223,A_1222)
      | ~ m1_subset_1(B_1223,k1_zfmisc_1(u1_struct_0(A_1222)))
      | ~ l1_pre_topc(A_1222) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_72,plain,(
    ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_97649,plain,
    ( ~ v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_97646,c_72])).

tff(c_97665,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_96207,c_97649])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:38:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 24.53/16.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.53/16.41  
% 24.53/16.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.53/16.41  %$ v3_tops_1 > v2_tops_1 > v1_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 24.53/16.41  
% 24.53/16.41  %Foreground sorts:
% 24.53/16.41  
% 24.53/16.41  
% 24.53/16.41  %Background operators:
% 24.53/16.41  
% 24.53/16.41  
% 24.53/16.41  %Foreground operators:
% 24.53/16.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 24.53/16.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 24.53/16.41  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 24.53/16.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 24.53/16.41  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 24.53/16.41  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 24.53/16.41  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 24.53/16.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 24.53/16.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 24.53/16.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 24.53/16.41  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 24.53/16.41  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 24.53/16.41  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 24.53/16.41  tff('#skF_2', type, '#skF_2': $i).
% 24.53/16.41  tff('#skF_1', type, '#skF_1': $i).
% 24.53/16.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 24.53/16.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 24.53/16.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 24.53/16.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 24.53/16.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 24.53/16.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 24.53/16.41  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 24.53/16.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 24.53/16.41  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 24.53/16.41  
% 24.53/16.43  tff(f_179, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_tops_1)).
% 24.53/16.43  tff(f_169, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tops_1)).
% 24.53/16.43  tff(f_133, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) <=> v2_tops_1(k2_pre_topc(A, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tops_1)).
% 24.53/16.43  tff(f_115, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 24.53/16.43  tff(f_153, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 24.53/16.43  tff(f_79, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 24.53/16.43  tff(f_146, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k2_tops_1(A, k3_subset_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_1)).
% 24.53/16.43  tff(f_139, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 24.53/16.43  tff(f_109, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 24.53/16.43  tff(f_85, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 24.53/16.43  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 24.53/16.43  tff(f_160, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_tops_1(A, k2_pre_topc(A, B)), k2_tops_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_tops_1)).
% 24.53/16.43  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 24.53/16.43  tff(f_124, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_1)).
% 24.53/16.43  tff(c_78, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_179])).
% 24.53/16.43  tff(c_76, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_179])).
% 24.53/16.43  tff(c_2253, plain, (![B_204, A_205]: (r1_tarski(B_204, k2_tops_1(A_205, B_204)) | ~v2_tops_1(B_204, A_205) | ~m1_subset_1(B_204, k1_zfmisc_1(u1_struct_0(A_205))) | ~l1_pre_topc(A_205))), inference(cnfTransformation, [status(thm)], [f_169])).
% 24.53/16.43  tff(c_2265, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_76, c_2253])).
% 24.53/16.43  tff(c_2272, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2265])).
% 24.53/16.43  tff(c_2276, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_2272])).
% 24.53/16.43  tff(c_74, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_179])).
% 24.53/16.43  tff(c_2749, plain, (![A_231, B_232]: (v2_tops_1(k2_pre_topc(A_231, B_232), A_231) | ~v3_tops_1(B_232, A_231) | ~m1_subset_1(B_232, k1_zfmisc_1(u1_struct_0(A_231))) | ~l1_pre_topc(A_231))), inference(cnfTransformation, [status(thm)], [f_133])).
% 24.53/16.43  tff(c_2761, plain, (v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_76, c_2749])).
% 24.53/16.43  tff(c_2768, plain, (v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_2761])).
% 24.53/16.43  tff(c_50, plain, (![A_50, B_51]: (m1_subset_1(k2_pre_topc(A_50, B_51), k1_zfmisc_1(u1_struct_0(A_50))) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_115])).
% 24.53/16.43  tff(c_2266, plain, (![A_50, B_51]: (r1_tarski(k2_pre_topc(A_50, B_51), k2_tops_1(A_50, k2_pre_topc(A_50, B_51))) | ~v2_tops_1(k2_pre_topc(A_50, B_51), A_50) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50))), inference(resolution, [status(thm)], [c_50, c_2253])).
% 24.53/16.43  tff(c_4812, plain, (![A_288, B_289]: (k4_subset_1(u1_struct_0(A_288), B_289, k2_tops_1(A_288, B_289))=k2_pre_topc(A_288, B_289) | ~m1_subset_1(B_289, k1_zfmisc_1(u1_struct_0(A_288))) | ~l1_pre_topc(A_288))), inference(cnfTransformation, [status(thm)], [f_153])).
% 24.53/16.43  tff(c_4830, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_76, c_4812])).
% 24.53/16.43  tff(c_4839, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_4830])).
% 24.53/16.43  tff(c_36, plain, (![A_33, B_34]: (m1_subset_1(k3_subset_1(A_33, B_34), k1_zfmisc_1(A_33)) | ~m1_subset_1(B_34, k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 24.53/16.43  tff(c_3255, plain, (![A_255, B_256]: (k2_tops_1(A_255, k3_subset_1(u1_struct_0(A_255), B_256))=k2_tops_1(A_255, B_256) | ~m1_subset_1(B_256, k1_zfmisc_1(u1_struct_0(A_255))) | ~l1_pre_topc(A_255))), inference(cnfTransformation, [status(thm)], [f_146])).
% 24.53/16.43  tff(c_3267, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_76, c_3255])).
% 24.53/16.43  tff(c_3274, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_3267])).
% 24.53/16.43  tff(c_1743, plain, (![A_192, B_193]: (m1_subset_1(k2_tops_1(A_192, B_193), k1_zfmisc_1(u1_struct_0(A_192))) | ~m1_subset_1(B_193, k1_zfmisc_1(u1_struct_0(A_192))) | ~l1_pre_topc(A_192))), inference(cnfTransformation, [status(thm)], [f_139])).
% 24.53/16.43  tff(c_46, plain, (![A_48, B_49]: (r1_tarski(A_48, B_49) | ~m1_subset_1(A_48, k1_zfmisc_1(B_49)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 24.53/16.43  tff(c_14421, plain, (![A_411, B_412]: (r1_tarski(k2_tops_1(A_411, B_412), u1_struct_0(A_411)) | ~m1_subset_1(B_412, k1_zfmisc_1(u1_struct_0(A_411))) | ~l1_pre_topc(A_411))), inference(resolution, [status(thm)], [c_1743, c_46])).
% 24.53/16.43  tff(c_14440, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3274, c_14421])).
% 24.53/16.43  tff(c_14450, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_14440])).
% 24.53/16.43  tff(c_88666, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_14450])).
% 24.53/16.43  tff(c_88669, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_36, c_88666])).
% 24.53/16.43  tff(c_88676, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_88669])).
% 24.53/16.43  tff(c_88677, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_14450])).
% 24.53/16.43  tff(c_48, plain, (![A_48, B_49]: (m1_subset_1(A_48, k1_zfmisc_1(B_49)) | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_109])).
% 24.53/16.43  tff(c_2490, plain, (![A_215, B_216, C_217]: (k4_subset_1(A_215, B_216, C_217)=k2_xboole_0(B_216, C_217) | ~m1_subset_1(C_217, k1_zfmisc_1(A_215)) | ~m1_subset_1(B_216, k1_zfmisc_1(A_215)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 24.53/16.43  tff(c_17063, plain, (![B_437, B_438, A_439]: (k4_subset_1(B_437, B_438, A_439)=k2_xboole_0(B_438, A_439) | ~m1_subset_1(B_438, k1_zfmisc_1(B_437)) | ~r1_tarski(A_439, B_437))), inference(resolution, [status(thm)], [c_48, c_2490])).
% 24.53/16.43  tff(c_17085, plain, (![A_439]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_439)=k2_xboole_0('#skF_2', A_439) | ~r1_tarski(A_439, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_76, c_17063])).
% 24.53/16.43  tff(c_88692, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_88677, c_17085])).
% 24.53/16.43  tff(c_88713, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4839, c_88692])).
% 24.53/16.43  tff(c_12, plain, (![A_7, C_9, B_8]: (r1_tarski(A_7, C_9) | ~r1_tarski(k2_xboole_0(A_7, B_8), C_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 24.53/16.43  tff(c_95516, plain, (![C_1156]: (r1_tarski('#skF_2', C_1156) | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), C_1156))), inference(superposition, [status(thm), theory('equality')], [c_88713, c_12])).
% 24.53/16.43  tff(c_95624, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))) | ~v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2266, c_95516])).
% 24.53/16.43  tff(c_95716, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_2768, c_95624])).
% 24.53/16.43  tff(c_3631, plain, (![A_266, B_267]: (r1_tarski(k2_tops_1(A_266, k2_pre_topc(A_266, B_267)), k2_tops_1(A_266, B_267)) | ~m1_subset_1(B_267, k1_zfmisc_1(u1_struct_0(A_266))) | ~l1_pre_topc(A_266))), inference(cnfTransformation, [status(thm)], [f_160])).
% 24.53/16.43  tff(c_16, plain, (![A_12, C_14, B_13]: (r1_tarski(A_12, C_14) | ~r1_tarski(B_13, C_14) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 24.53/16.43  tff(c_3646, plain, (![A_12, A_266, B_267]: (r1_tarski(A_12, k2_tops_1(A_266, B_267)) | ~r1_tarski(A_12, k2_tops_1(A_266, k2_pre_topc(A_266, B_267))) | ~m1_subset_1(B_267, k1_zfmisc_1(u1_struct_0(A_266))) | ~l1_pre_topc(A_266))), inference(resolution, [status(thm)], [c_3631, c_16])).
% 24.53/16.43  tff(c_96141, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_95716, c_3646])).
% 24.53/16.43  tff(c_96162, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_96141])).
% 24.53/16.43  tff(c_68, plain, (![B_71, A_69]: (v2_tops_1(B_71, A_69) | ~r1_tarski(B_71, k2_tops_1(A_69, B_71)) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_169])).
% 24.53/16.43  tff(c_96188, plain, (v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_96162, c_68])).
% 24.53/16.43  tff(c_96203, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_96188])).
% 24.53/16.43  tff(c_96205, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2276, c_96203])).
% 24.53/16.43  tff(c_96207, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_2272])).
% 24.53/16.43  tff(c_97646, plain, (![A_1222, B_1223]: (v1_tops_1(k3_subset_1(u1_struct_0(A_1222), B_1223), A_1222) | ~v2_tops_1(B_1223, A_1222) | ~m1_subset_1(B_1223, k1_zfmisc_1(u1_struct_0(A_1222))) | ~l1_pre_topc(A_1222))), inference(cnfTransformation, [status(thm)], [f_124])).
% 24.53/16.43  tff(c_72, plain, (~v1_tops_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_179])).
% 24.53/16.43  tff(c_97649, plain, (~v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_97646, c_72])).
% 24.53/16.43  tff(c_97665, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_96207, c_97649])).
% 24.53/16.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.53/16.43  
% 24.53/16.43  Inference rules
% 24.53/16.43  ----------------------
% 24.53/16.43  #Ref     : 0
% 24.53/16.43  #Sup     : 23210
% 24.53/16.43  #Fact    : 0
% 24.53/16.43  #Define  : 0
% 24.53/16.43  #Split   : 7
% 24.53/16.43  #Chain   : 0
% 24.53/16.43  #Close   : 0
% 24.53/16.43  
% 24.53/16.43  Ordering : KBO
% 24.53/16.43  
% 24.53/16.43  Simplification rules
% 24.53/16.43  ----------------------
% 24.53/16.43  #Subsume      : 1846
% 24.53/16.43  #Demod        : 23649
% 24.53/16.43  #Tautology    : 13277
% 24.53/16.43  #SimpNegUnit  : 1
% 24.53/16.43  #BackRed      : 20
% 24.53/16.43  
% 24.53/16.43  #Partial instantiations: 0
% 24.53/16.43  #Strategies tried      : 1
% 24.53/16.43  
% 24.53/16.43  Timing (in seconds)
% 24.53/16.43  ----------------------
% 24.53/16.43  Preprocessing        : 0.37
% 24.53/16.43  Parsing              : 0.20
% 24.53/16.43  CNF conversion       : 0.02
% 24.53/16.43  Main loop            : 15.30
% 24.53/16.43  Inferencing          : 1.67
% 24.53/16.43  Reduction            : 9.22
% 24.53/16.43  Demodulation         : 8.33
% 24.53/16.43  BG Simplification    : 0.19
% 24.53/16.43  Subsumption          : 3.58
% 24.53/16.43  Abstraction          : 0.32
% 24.53/16.43  MUC search           : 0.00
% 24.53/16.43  Cooper               : 0.00
% 24.53/16.43  Total                : 15.70
% 24.53/16.43  Index Insertion      : 0.00
% 24.53/16.43  Index Deletion       : 0.00
% 24.53/16.43  Index Matching       : 0.00
% 24.53/16.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
