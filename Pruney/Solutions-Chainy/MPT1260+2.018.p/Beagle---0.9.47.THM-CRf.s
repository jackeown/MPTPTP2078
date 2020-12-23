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
% DateTime   : Thu Dec  3 10:21:02 EST 2020

% Result     : Theorem 9.25s
% Output     : CNFRefutation 9.25s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 350 expanded)
%              Number of leaves         :   47 ( 138 expanded)
%              Depth                    :   13
%              Number of atoms          :  214 ( 735 expanded)
%              Number of equality atoms :   70 ( 225 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_137,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_56,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_58,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_76,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_54,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_125,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_118,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_111,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_82,plain,
    ( k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') != k2_tops_1('#skF_5','#skF_6')
    | ~ v3_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_351,plain,(
    ~ v3_pre_topc('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_44,plain,(
    ! [B_16] : r1_tarski(B_16,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_54,plain,(
    ! [A_24] : k4_xboole_0(A_24,k1_xboole_0) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_48,plain,(
    ! [A_19,B_20] : r1_tarski(k3_xboole_0(A_19,B_20),A_19) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_50,plain,(
    ! [A_21] : r1_tarski(k1_xboole_0,A_21) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_244,plain,(
    ! [B_74,A_75] :
      ( B_74 = A_75
      | ~ r1_tarski(B_74,A_75)
      | ~ r1_tarski(A_75,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_263,plain,(
    ! [A_76] :
      ( k1_xboole_0 = A_76
      | ~ r1_tarski(A_76,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_50,c_244])).

tff(c_312,plain,(
    ! [B_78] : k3_xboole_0(k1_xboole_0,B_78) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_263])).

tff(c_56,plain,(
    ! [B_26,A_25] : k2_tarski(B_26,A_25) = k2_tarski(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_154,plain,(
    ! [A_66,B_67] : k1_setfam_1(k2_tarski(A_66,B_67)) = k3_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_169,plain,(
    ! [B_68,A_69] : k1_setfam_1(k2_tarski(B_68,A_69)) = k3_xboole_0(A_69,B_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_154])).

tff(c_62,plain,(
    ! [A_33,B_34] : k1_setfam_1(k2_tarski(A_33,B_34)) = k3_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_175,plain,(
    ! [B_68,A_69] : k3_xboole_0(B_68,A_69) = k3_xboole_0(A_69,B_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_62])).

tff(c_320,plain,(
    ! [B_78] : k3_xboole_0(B_78,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_175])).

tff(c_446,plain,(
    ! [A_88,B_89] : k5_xboole_0(A_88,k3_xboole_0(A_88,B_89)) = k4_xboole_0(A_88,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_455,plain,(
    ! [B_78] : k5_xboole_0(B_78,k1_xboole_0) = k4_xboole_0(B_78,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_446])).

tff(c_470,plain,(
    ! [B_78] : k5_xboole_0(B_78,k1_xboole_0) = B_78 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_455])).

tff(c_78,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_76,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_519,plain,(
    ! [A_98,B_99,C_100] :
      ( k7_subset_1(A_98,B_99,C_100) = k4_xboole_0(B_99,C_100)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(A_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_522,plain,(
    ! [C_100] : k7_subset_1(u1_struct_0('#skF_5'),'#skF_6',C_100) = k4_xboole_0('#skF_6',C_100) ),
    inference(resolution,[status(thm)],[c_76,c_519])).

tff(c_1877,plain,(
    ! [A_204,B_205] :
      ( k7_subset_1(u1_struct_0(A_204),B_205,k2_tops_1(A_204,B_205)) = k1_tops_1(A_204,B_205)
      | ~ m1_subset_1(B_205,k1_zfmisc_1(u1_struct_0(A_204)))
      | ~ l1_pre_topc(A_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1884,plain,
    ( k7_subset_1(u1_struct_0('#skF_5'),'#skF_6',k2_tops_1('#skF_5','#skF_6')) = k1_tops_1('#skF_5','#skF_6')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_1877])).

tff(c_1889,plain,(
    k4_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6')) = k1_tops_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_522,c_1884])).

tff(c_64,plain,(
    ! [A_35,B_36] :
      ( m1_subset_1(k2_tops_1(A_35,B_36),k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1690,plain,(
    ! [A_193,B_194] :
      ( k4_subset_1(u1_struct_0(A_193),B_194,k2_tops_1(A_193,B_194)) = k2_pre_topc(A_193,B_194)
      | ~ m1_subset_1(B_194,k1_zfmisc_1(u1_struct_0(A_193)))
      | ~ l1_pre_topc(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1697,plain,
    ( k4_subset_1(u1_struct_0('#skF_5'),'#skF_6',k2_tops_1('#skF_5','#skF_6')) = k2_pre_topc('#skF_5','#skF_6')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_1690])).

tff(c_1702,plain,(
    k4_subset_1(u1_struct_0('#skF_5'),'#skF_6',k2_tops_1('#skF_5','#skF_6')) = k2_pre_topc('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1697])).

tff(c_58,plain,(
    ! [A_27,B_28,C_29] :
      ( m1_subset_1(k4_subset_1(A_27,B_28,C_29),k1_zfmisc_1(A_27))
      | ~ m1_subset_1(C_29,k1_zfmisc_1(A_27))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1706,plain,
    ( m1_subset_1(k2_pre_topc('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1(k2_tops_1('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1702,c_58])).

tff(c_1710,plain,
    ( m1_subset_1(k2_pre_topc('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1(k2_tops_1('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1706])).

tff(c_3066,plain,(
    ~ m1_subset_1(k2_tops_1('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_1710])).

tff(c_3069,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_3066])).

tff(c_3073,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_3069])).

tff(c_3074,plain,(
    m1_subset_1(k2_pre_topc('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_1710])).

tff(c_60,plain,(
    ! [A_30,B_31,C_32] :
      ( k7_subset_1(A_30,B_31,C_32) = k4_xboole_0(B_31,C_32)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_3183,plain,(
    ! [C_240] : k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),C_240) = k4_xboole_0(k2_pre_topc('#skF_5','#skF_6'),C_240) ),
    inference(resolution,[status(thm)],[c_3074,c_60])).

tff(c_88,plain,
    ( v3_pre_topc('#skF_6','#skF_5')
    | k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_120,plain,(
    k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_3193,plain,(
    k4_xboole_0(k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3183,c_120])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_758,plain,(
    ! [A_129,B_130,C_131] :
      ( r2_hidden('#skF_1'(A_129,B_130,C_131),A_129)
      | r2_hidden('#skF_2'(A_129,B_130,C_131),C_131)
      | k3_xboole_0(A_129,B_130) = C_131 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_22,plain,(
    ! [D_12,B_8,A_7] :
      ( ~ r2_hidden(D_12,B_8)
      | ~ r2_hidden(D_12,k4_xboole_0(A_7,B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8222,plain,(
    ! [A_450,B_451,B_452,C_453] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_450,B_451),B_452,C_453),B_451)
      | r2_hidden('#skF_2'(k4_xboole_0(A_450,B_451),B_452,C_453),C_453)
      | k3_xboole_0(k4_xboole_0(A_450,B_451),B_452) = C_453 ) ),
    inference(resolution,[status(thm)],[c_758,c_22])).

tff(c_8253,plain,(
    ! [A_450,B_2,C_3] :
      ( r2_hidden('#skF_2'(k4_xboole_0(A_450,B_2),B_2,C_3),C_3)
      | k3_xboole_0(k4_xboole_0(A_450,B_2),B_2) = C_3 ) ),
    inference(resolution,[status(thm)],[c_16,c_8222])).

tff(c_8280,plain,(
    ! [A_450,B_2,C_3] :
      ( r2_hidden('#skF_2'(k4_xboole_0(A_450,B_2),B_2,C_3),C_3)
      | k3_xboole_0(B_2,k4_xboole_0(A_450,B_2)) = C_3 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_8253])).

tff(c_8586,plain,(
    ! [A_464,B_465,C_466] :
      ( r2_hidden('#skF_2'(k4_xboole_0(A_464,B_465),B_465,C_466),C_466)
      | k3_xboole_0(B_465,k4_xboole_0(A_464,B_465)) = C_466 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_8253])).

tff(c_512,plain,(
    ! [D_95,B_96,A_97] :
      ( ~ r2_hidden(D_95,B_96)
      | ~ r2_hidden(D_95,k4_xboole_0(A_97,B_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_518,plain,(
    ! [D_95,A_24] :
      ( ~ r2_hidden(D_95,k1_xboole_0)
      | ~ r2_hidden(D_95,A_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_512])).

tff(c_8923,plain,(
    ! [A_471,B_472,A_473] :
      ( ~ r2_hidden('#skF_2'(k4_xboole_0(A_471,B_472),B_472,k1_xboole_0),A_473)
      | k3_xboole_0(B_472,k4_xboole_0(A_471,B_472)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8586,c_518])).

tff(c_9018,plain,(
    ! [B_474,A_475] : k3_xboole_0(B_474,k4_xboole_0(A_475,B_474)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8280,c_8923])).

tff(c_9193,plain,(
    k3_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3193,c_9018])).

tff(c_46,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_9396,plain,(
    k4_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6')) = k5_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_9193,c_46])).

tff(c_9450,plain,(
    k1_tops_1('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_1889,c_9396])).

tff(c_52,plain,(
    ! [A_22,B_23] : r1_tarski(k4_xboole_0(A_22,B_23),A_22) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_256,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,B_23) = A_22
      | ~ r1_tarski(A_22,k4_xboole_0(A_22,B_23)) ) ),
    inference(resolution,[status(thm)],[c_52,c_244])).

tff(c_1905,plain,
    ( k4_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6')) = '#skF_6'
    | ~ r1_tarski('#skF_6',k1_tops_1('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1889,c_256])).

tff(c_1924,plain,
    ( k1_tops_1('#skF_5','#skF_6') = '#skF_6'
    | ~ r1_tarski('#skF_6',k1_tops_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1889,c_1905])).

tff(c_2141,plain,(
    ~ r1_tarski('#skF_6',k1_tops_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1924])).

tff(c_9482,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9450,c_2141])).

tff(c_9492,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_9482])).

tff(c_9493,plain,(
    k1_tops_1('#skF_5','#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1924])).

tff(c_80,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_741,plain,(
    ! [A_124,B_125] :
      ( v3_pre_topc(k1_tops_1(A_124,B_125),A_124)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ l1_pre_topc(A_124)
      | ~ v2_pre_topc(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_745,plain,
    ( v3_pre_topc(k1_tops_1('#skF_5','#skF_6'),'#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_741])).

tff(c_749,plain,(
    v3_pre_topc(k1_tops_1('#skF_5','#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_745])).

tff(c_9499,plain,(
    v3_pre_topc('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9493,c_749])).

tff(c_9502,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_351,c_9499])).

tff(c_9503,plain,(
    k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') != k2_tops_1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_9654,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9503,c_120])).

tff(c_9655,plain,(
    v3_pre_topc('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_9863,plain,(
    k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') != k2_tops_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9655,c_82])).

tff(c_10053,plain,(
    ! [A_525,B_526,C_527] :
      ( k7_subset_1(A_525,B_526,C_527) = k4_xboole_0(B_526,C_527)
      | ~ m1_subset_1(B_526,k1_zfmisc_1(A_525)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_10056,plain,(
    ! [C_527] : k7_subset_1(u1_struct_0('#skF_5'),'#skF_6',C_527) = k4_xboole_0('#skF_6',C_527) ),
    inference(resolution,[status(thm)],[c_76,c_10053])).

tff(c_10874,plain,(
    ! [A_592,B_593] :
      ( k7_subset_1(u1_struct_0(A_592),B_593,k2_tops_1(A_592,B_593)) = k1_tops_1(A_592,B_593)
      | ~ m1_subset_1(B_593,k1_zfmisc_1(u1_struct_0(A_592)))
      | ~ l1_pre_topc(A_592) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_10885,plain,
    ( k7_subset_1(u1_struct_0('#skF_5'),'#skF_6',k2_tops_1('#skF_5','#skF_6')) = k1_tops_1('#skF_5','#skF_6')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_10874])).

tff(c_10896,plain,(
    k4_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6')) = k1_tops_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_10056,c_10885])).

tff(c_9767,plain,(
    ! [B_497,A_498] :
      ( B_497 = A_498
      | ~ r1_tarski(B_497,A_498)
      | ~ r1_tarski(A_498,B_497) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_9776,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,B_23) = A_22
      | ~ r1_tarski(A_22,k4_xboole_0(A_22,B_23)) ) ),
    inference(resolution,[status(thm)],[c_52,c_9767])).

tff(c_10903,plain,
    ( k4_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6')) = '#skF_6'
    | ~ r1_tarski('#skF_6',k1_tops_1('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10896,c_9776])).

tff(c_10919,plain,
    ( k1_tops_1('#skF_5','#skF_6') = '#skF_6'
    | ~ r1_tarski('#skF_6',k1_tops_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10896,c_10903])).

tff(c_11046,plain,(
    ~ r1_tarski('#skF_6',k1_tops_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_10919])).

tff(c_14667,plain,(
    ! [B_787,A_788,C_789] :
      ( r1_tarski(B_787,k1_tops_1(A_788,C_789))
      | ~ r1_tarski(B_787,C_789)
      | ~ v3_pre_topc(B_787,A_788)
      | ~ m1_subset_1(C_789,k1_zfmisc_1(u1_struct_0(A_788)))
      | ~ m1_subset_1(B_787,k1_zfmisc_1(u1_struct_0(A_788)))
      | ~ l1_pre_topc(A_788) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_14678,plain,(
    ! [B_787] :
      ( r1_tarski(B_787,k1_tops_1('#skF_5','#skF_6'))
      | ~ r1_tarski(B_787,'#skF_6')
      | ~ v3_pre_topc(B_787,'#skF_5')
      | ~ m1_subset_1(B_787,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_76,c_14667])).

tff(c_14862,plain,(
    ! [B_796] :
      ( r1_tarski(B_796,k1_tops_1('#skF_5','#skF_6'))
      | ~ r1_tarski(B_796,'#skF_6')
      | ~ v3_pre_topc(B_796,'#skF_5')
      | ~ m1_subset_1(B_796,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_14678])).

tff(c_14879,plain,
    ( r1_tarski('#skF_6',k1_tops_1('#skF_5','#skF_6'))
    | ~ r1_tarski('#skF_6','#skF_6')
    | ~ v3_pre_topc('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_14862])).

tff(c_14888,plain,(
    r1_tarski('#skF_6',k1_tops_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9655,c_44,c_14879])).

tff(c_14890,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11046,c_14888])).

tff(c_14891,plain,(
    k1_tops_1('#skF_5','#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_10919])).

tff(c_14992,plain,(
    ! [A_798,B_799] :
      ( k7_subset_1(u1_struct_0(A_798),k2_pre_topc(A_798,B_799),k1_tops_1(A_798,B_799)) = k2_tops_1(A_798,B_799)
      | ~ m1_subset_1(B_799,k1_zfmisc_1(u1_struct_0(A_798)))
      | ~ l1_pre_topc(A_798) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_15001,plain,
    ( k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_14891,c_14992])).

tff(c_15005,plain,(
    k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_15001])).

tff(c_15007,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9863,c_15005])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:12:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.25/3.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.25/3.22  
% 9.25/3.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.25/3.22  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 9.25/3.22  
% 9.25/3.22  %Foreground sorts:
% 9.25/3.22  
% 9.25/3.22  
% 9.25/3.22  %Background operators:
% 9.25/3.22  
% 9.25/3.22  
% 9.25/3.22  %Foreground operators:
% 9.25/3.22  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 9.25/3.22  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 9.25/3.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.25/3.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.25/3.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.25/3.22  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 9.25/3.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.25/3.22  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.25/3.22  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 9.25/3.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.25/3.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.25/3.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.25/3.22  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 9.25/3.22  tff('#skF_5', type, '#skF_5': $i).
% 9.25/3.22  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 9.25/3.22  tff('#skF_6', type, '#skF_6': $i).
% 9.25/3.22  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 9.25/3.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.25/3.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.25/3.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.25/3.22  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 9.25/3.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.25/3.22  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.25/3.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.25/3.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.25/3.22  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 9.25/3.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.25/3.22  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.25/3.22  
% 9.25/3.24  tff(f_137, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tops_1)).
% 9.25/3.24  tff(f_52, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.25/3.24  tff(f_62, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 9.25/3.24  tff(f_56, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 9.25/3.24  tff(f_58, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.25/3.24  tff(f_64, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 9.25/3.24  tff(f_76, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 9.25/3.24  tff(f_54, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.25/3.24  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 9.25/3.24  tff(f_125, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 9.25/3.24  tff(f_82, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 9.25/3.24  tff(f_118, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 9.25/3.24  tff(f_70, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 9.25/3.24  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 9.25/3.24  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 9.25/3.24  tff(f_60, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 9.25/3.24  tff(f_90, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 9.25/3.24  tff(f_111, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 9.25/3.24  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 9.25/3.24  tff(c_82, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')!=k2_tops_1('#skF_5', '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.25/3.24  tff(c_351, plain, (~v3_pre_topc('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_82])).
% 9.25/3.24  tff(c_44, plain, (![B_16]: (r1_tarski(B_16, B_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.25/3.24  tff(c_54, plain, (![A_24]: (k4_xboole_0(A_24, k1_xboole_0)=A_24)), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.25/3.24  tff(c_48, plain, (![A_19, B_20]: (r1_tarski(k3_xboole_0(A_19, B_20), A_19))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.25/3.24  tff(c_50, plain, (![A_21]: (r1_tarski(k1_xboole_0, A_21))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.25/3.24  tff(c_244, plain, (![B_74, A_75]: (B_74=A_75 | ~r1_tarski(B_74, A_75) | ~r1_tarski(A_75, B_74))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.25/3.24  tff(c_263, plain, (![A_76]: (k1_xboole_0=A_76 | ~r1_tarski(A_76, k1_xboole_0))), inference(resolution, [status(thm)], [c_50, c_244])).
% 9.25/3.24  tff(c_312, plain, (![B_78]: (k3_xboole_0(k1_xboole_0, B_78)=k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_263])).
% 9.25/3.24  tff(c_56, plain, (![B_26, A_25]: (k2_tarski(B_26, A_25)=k2_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.25/3.24  tff(c_154, plain, (![A_66, B_67]: (k1_setfam_1(k2_tarski(A_66, B_67))=k3_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.25/3.24  tff(c_169, plain, (![B_68, A_69]: (k1_setfam_1(k2_tarski(B_68, A_69))=k3_xboole_0(A_69, B_68))), inference(superposition, [status(thm), theory('equality')], [c_56, c_154])).
% 9.25/3.24  tff(c_62, plain, (![A_33, B_34]: (k1_setfam_1(k2_tarski(A_33, B_34))=k3_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.25/3.24  tff(c_175, plain, (![B_68, A_69]: (k3_xboole_0(B_68, A_69)=k3_xboole_0(A_69, B_68))), inference(superposition, [status(thm), theory('equality')], [c_169, c_62])).
% 9.25/3.24  tff(c_320, plain, (![B_78]: (k3_xboole_0(B_78, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_312, c_175])).
% 9.25/3.24  tff(c_446, plain, (![A_88, B_89]: (k5_xboole_0(A_88, k3_xboole_0(A_88, B_89))=k4_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.25/3.24  tff(c_455, plain, (![B_78]: (k5_xboole_0(B_78, k1_xboole_0)=k4_xboole_0(B_78, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_320, c_446])).
% 9.25/3.24  tff(c_470, plain, (![B_78]: (k5_xboole_0(B_78, k1_xboole_0)=B_78)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_455])).
% 9.25/3.24  tff(c_78, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.25/3.24  tff(c_76, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.25/3.24  tff(c_519, plain, (![A_98, B_99, C_100]: (k7_subset_1(A_98, B_99, C_100)=k4_xboole_0(B_99, C_100) | ~m1_subset_1(B_99, k1_zfmisc_1(A_98)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.25/3.24  tff(c_522, plain, (![C_100]: (k7_subset_1(u1_struct_0('#skF_5'), '#skF_6', C_100)=k4_xboole_0('#skF_6', C_100))), inference(resolution, [status(thm)], [c_76, c_519])).
% 9.25/3.24  tff(c_1877, plain, (![A_204, B_205]: (k7_subset_1(u1_struct_0(A_204), B_205, k2_tops_1(A_204, B_205))=k1_tops_1(A_204, B_205) | ~m1_subset_1(B_205, k1_zfmisc_1(u1_struct_0(A_204))) | ~l1_pre_topc(A_204))), inference(cnfTransformation, [status(thm)], [f_125])).
% 9.25/3.24  tff(c_1884, plain, (k7_subset_1(u1_struct_0('#skF_5'), '#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k1_tops_1('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_76, c_1877])).
% 9.25/3.24  tff(c_1889, plain, (k4_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k1_tops_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_522, c_1884])).
% 9.25/3.24  tff(c_64, plain, (![A_35, B_36]: (m1_subset_1(k2_tops_1(A_35, B_36), k1_zfmisc_1(u1_struct_0(A_35))) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.25/3.24  tff(c_1690, plain, (![A_193, B_194]: (k4_subset_1(u1_struct_0(A_193), B_194, k2_tops_1(A_193, B_194))=k2_pre_topc(A_193, B_194) | ~m1_subset_1(B_194, k1_zfmisc_1(u1_struct_0(A_193))) | ~l1_pre_topc(A_193))), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.25/3.24  tff(c_1697, plain, (k4_subset_1(u1_struct_0('#skF_5'), '#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k2_pre_topc('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_76, c_1690])).
% 9.25/3.24  tff(c_1702, plain, (k4_subset_1(u1_struct_0('#skF_5'), '#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k2_pre_topc('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1697])).
% 9.25/3.24  tff(c_58, plain, (![A_27, B_28, C_29]: (m1_subset_1(k4_subset_1(A_27, B_28, C_29), k1_zfmisc_1(A_27)) | ~m1_subset_1(C_29, k1_zfmisc_1(A_27)) | ~m1_subset_1(B_28, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.25/3.24  tff(c_1706, plain, (m1_subset_1(k2_pre_topc('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(k2_tops_1('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_1702, c_58])).
% 9.25/3.24  tff(c_1710, plain, (m1_subset_1(k2_pre_topc('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(k2_tops_1('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1706])).
% 9.25/3.24  tff(c_3066, plain, (~m1_subset_1(k2_tops_1('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_1710])).
% 9.25/3.24  tff(c_3069, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_64, c_3066])).
% 9.25/3.24  tff(c_3073, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_3069])).
% 9.25/3.24  tff(c_3074, plain, (m1_subset_1(k2_pre_topc('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_1710])).
% 9.25/3.24  tff(c_60, plain, (![A_30, B_31, C_32]: (k7_subset_1(A_30, B_31, C_32)=k4_xboole_0(B_31, C_32) | ~m1_subset_1(B_31, k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.25/3.24  tff(c_3183, plain, (![C_240]: (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), C_240)=k4_xboole_0(k2_pre_topc('#skF_5', '#skF_6'), C_240))), inference(resolution, [status(thm)], [c_3074, c_60])).
% 9.25/3.24  tff(c_88, plain, (v3_pre_topc('#skF_6', '#skF_5') | k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.25/3.24  tff(c_120, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_88])).
% 9.25/3.24  tff(c_3193, plain, (k4_xboole_0(k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3183, c_120])).
% 9.25/3.24  tff(c_16, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.25/3.24  tff(c_758, plain, (![A_129, B_130, C_131]: (r2_hidden('#skF_1'(A_129, B_130, C_131), A_129) | r2_hidden('#skF_2'(A_129, B_130, C_131), C_131) | k3_xboole_0(A_129, B_130)=C_131)), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.25/3.24  tff(c_22, plain, (![D_12, B_8, A_7]: (~r2_hidden(D_12, B_8) | ~r2_hidden(D_12, k4_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.25/3.24  tff(c_8222, plain, (![A_450, B_451, B_452, C_453]: (~r2_hidden('#skF_1'(k4_xboole_0(A_450, B_451), B_452, C_453), B_451) | r2_hidden('#skF_2'(k4_xboole_0(A_450, B_451), B_452, C_453), C_453) | k3_xboole_0(k4_xboole_0(A_450, B_451), B_452)=C_453)), inference(resolution, [status(thm)], [c_758, c_22])).
% 9.25/3.24  tff(c_8253, plain, (![A_450, B_2, C_3]: (r2_hidden('#skF_2'(k4_xboole_0(A_450, B_2), B_2, C_3), C_3) | k3_xboole_0(k4_xboole_0(A_450, B_2), B_2)=C_3)), inference(resolution, [status(thm)], [c_16, c_8222])).
% 9.25/3.24  tff(c_8280, plain, (![A_450, B_2, C_3]: (r2_hidden('#skF_2'(k4_xboole_0(A_450, B_2), B_2, C_3), C_3) | k3_xboole_0(B_2, k4_xboole_0(A_450, B_2))=C_3)), inference(demodulation, [status(thm), theory('equality')], [c_175, c_8253])).
% 9.25/3.24  tff(c_8586, plain, (![A_464, B_465, C_466]: (r2_hidden('#skF_2'(k4_xboole_0(A_464, B_465), B_465, C_466), C_466) | k3_xboole_0(B_465, k4_xboole_0(A_464, B_465))=C_466)), inference(demodulation, [status(thm), theory('equality')], [c_175, c_8253])).
% 9.25/3.24  tff(c_512, plain, (![D_95, B_96, A_97]: (~r2_hidden(D_95, B_96) | ~r2_hidden(D_95, k4_xboole_0(A_97, B_96)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.25/3.24  tff(c_518, plain, (![D_95, A_24]: (~r2_hidden(D_95, k1_xboole_0) | ~r2_hidden(D_95, A_24))), inference(superposition, [status(thm), theory('equality')], [c_54, c_512])).
% 9.25/3.24  tff(c_8923, plain, (![A_471, B_472, A_473]: (~r2_hidden('#skF_2'(k4_xboole_0(A_471, B_472), B_472, k1_xboole_0), A_473) | k3_xboole_0(B_472, k4_xboole_0(A_471, B_472))=k1_xboole_0)), inference(resolution, [status(thm)], [c_8586, c_518])).
% 9.25/3.24  tff(c_9018, plain, (![B_474, A_475]: (k3_xboole_0(B_474, k4_xboole_0(A_475, B_474))=k1_xboole_0)), inference(resolution, [status(thm)], [c_8280, c_8923])).
% 9.25/3.24  tff(c_9193, plain, (k3_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3193, c_9018])).
% 9.25/3.24  tff(c_46, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.25/3.24  tff(c_9396, plain, (k4_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k5_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_9193, c_46])).
% 9.25/3.24  tff(c_9450, plain, (k1_tops_1('#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_470, c_1889, c_9396])).
% 9.25/3.24  tff(c_52, plain, (![A_22, B_23]: (r1_tarski(k4_xboole_0(A_22, B_23), A_22))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.25/3.24  tff(c_256, plain, (![A_22, B_23]: (k4_xboole_0(A_22, B_23)=A_22 | ~r1_tarski(A_22, k4_xboole_0(A_22, B_23)))), inference(resolution, [status(thm)], [c_52, c_244])).
% 9.25/3.24  tff(c_1905, plain, (k4_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6'))='#skF_6' | ~r1_tarski('#skF_6', k1_tops_1('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1889, c_256])).
% 9.25/3.24  tff(c_1924, plain, (k1_tops_1('#skF_5', '#skF_6')='#skF_6' | ~r1_tarski('#skF_6', k1_tops_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1889, c_1905])).
% 9.25/3.24  tff(c_2141, plain, (~r1_tarski('#skF_6', k1_tops_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_1924])).
% 9.25/3.24  tff(c_9482, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_9450, c_2141])).
% 9.25/3.24  tff(c_9492, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_9482])).
% 9.25/3.24  tff(c_9493, plain, (k1_tops_1('#skF_5', '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_1924])).
% 9.25/3.24  tff(c_80, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.25/3.24  tff(c_741, plain, (![A_124, B_125]: (v3_pre_topc(k1_tops_1(A_124, B_125), A_124) | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_124))) | ~l1_pre_topc(A_124) | ~v2_pre_topc(A_124))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.25/3.24  tff(c_745, plain, (v3_pre_topc(k1_tops_1('#skF_5', '#skF_6'), '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_76, c_741])).
% 9.25/3.24  tff(c_749, plain, (v3_pre_topc(k1_tops_1('#skF_5', '#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_745])).
% 9.25/3.24  tff(c_9499, plain, (v3_pre_topc('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_9493, c_749])).
% 9.25/3.24  tff(c_9502, plain, $false, inference(negUnitSimplification, [status(thm)], [c_351, c_9499])).
% 9.25/3.24  tff(c_9503, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')!=k2_tops_1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_82])).
% 9.25/3.24  tff(c_9654, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9503, c_120])).
% 9.25/3.24  tff(c_9655, plain, (v3_pre_topc('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_88])).
% 9.25/3.24  tff(c_9863, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')!=k2_tops_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_9655, c_82])).
% 9.25/3.24  tff(c_10053, plain, (![A_525, B_526, C_527]: (k7_subset_1(A_525, B_526, C_527)=k4_xboole_0(B_526, C_527) | ~m1_subset_1(B_526, k1_zfmisc_1(A_525)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.25/3.24  tff(c_10056, plain, (![C_527]: (k7_subset_1(u1_struct_0('#skF_5'), '#skF_6', C_527)=k4_xboole_0('#skF_6', C_527))), inference(resolution, [status(thm)], [c_76, c_10053])).
% 9.25/3.24  tff(c_10874, plain, (![A_592, B_593]: (k7_subset_1(u1_struct_0(A_592), B_593, k2_tops_1(A_592, B_593))=k1_tops_1(A_592, B_593) | ~m1_subset_1(B_593, k1_zfmisc_1(u1_struct_0(A_592))) | ~l1_pre_topc(A_592))), inference(cnfTransformation, [status(thm)], [f_125])).
% 9.25/3.24  tff(c_10885, plain, (k7_subset_1(u1_struct_0('#skF_5'), '#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k1_tops_1('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_76, c_10874])).
% 9.25/3.24  tff(c_10896, plain, (k4_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k1_tops_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_10056, c_10885])).
% 9.25/3.24  tff(c_9767, plain, (![B_497, A_498]: (B_497=A_498 | ~r1_tarski(B_497, A_498) | ~r1_tarski(A_498, B_497))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.25/3.24  tff(c_9776, plain, (![A_22, B_23]: (k4_xboole_0(A_22, B_23)=A_22 | ~r1_tarski(A_22, k4_xboole_0(A_22, B_23)))), inference(resolution, [status(thm)], [c_52, c_9767])).
% 9.25/3.24  tff(c_10903, plain, (k4_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6'))='#skF_6' | ~r1_tarski('#skF_6', k1_tops_1('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_10896, c_9776])).
% 9.25/3.24  tff(c_10919, plain, (k1_tops_1('#skF_5', '#skF_6')='#skF_6' | ~r1_tarski('#skF_6', k1_tops_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_10896, c_10903])).
% 9.25/3.24  tff(c_11046, plain, (~r1_tarski('#skF_6', k1_tops_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_10919])).
% 9.25/3.24  tff(c_14667, plain, (![B_787, A_788, C_789]: (r1_tarski(B_787, k1_tops_1(A_788, C_789)) | ~r1_tarski(B_787, C_789) | ~v3_pre_topc(B_787, A_788) | ~m1_subset_1(C_789, k1_zfmisc_1(u1_struct_0(A_788))) | ~m1_subset_1(B_787, k1_zfmisc_1(u1_struct_0(A_788))) | ~l1_pre_topc(A_788))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.25/3.24  tff(c_14678, plain, (![B_787]: (r1_tarski(B_787, k1_tops_1('#skF_5', '#skF_6')) | ~r1_tarski(B_787, '#skF_6') | ~v3_pre_topc(B_787, '#skF_5') | ~m1_subset_1(B_787, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_76, c_14667])).
% 9.25/3.24  tff(c_14862, plain, (![B_796]: (r1_tarski(B_796, k1_tops_1('#skF_5', '#skF_6')) | ~r1_tarski(B_796, '#skF_6') | ~v3_pre_topc(B_796, '#skF_5') | ~m1_subset_1(B_796, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_14678])).
% 9.25/3.24  tff(c_14879, plain, (r1_tarski('#skF_6', k1_tops_1('#skF_5', '#skF_6')) | ~r1_tarski('#skF_6', '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_76, c_14862])).
% 9.25/3.24  tff(c_14888, plain, (r1_tarski('#skF_6', k1_tops_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_9655, c_44, c_14879])).
% 9.25/3.24  tff(c_14890, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11046, c_14888])).
% 9.25/3.24  tff(c_14891, plain, (k1_tops_1('#skF_5', '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_10919])).
% 9.25/3.24  tff(c_14992, plain, (![A_798, B_799]: (k7_subset_1(u1_struct_0(A_798), k2_pre_topc(A_798, B_799), k1_tops_1(A_798, B_799))=k2_tops_1(A_798, B_799) | ~m1_subset_1(B_799, k1_zfmisc_1(u1_struct_0(A_798))) | ~l1_pre_topc(A_798))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.25/3.24  tff(c_15001, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_14891, c_14992])).
% 9.25/3.24  tff(c_15005, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_15001])).
% 9.25/3.24  tff(c_15007, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9863, c_15005])).
% 9.25/3.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.25/3.24  
% 9.25/3.24  Inference rules
% 9.25/3.24  ----------------------
% 9.25/3.24  #Ref     : 0
% 9.25/3.24  #Sup     : 3204
% 9.25/3.24  #Fact    : 0
% 9.25/3.24  #Define  : 0
% 9.25/3.24  #Split   : 22
% 9.25/3.24  #Chain   : 0
% 9.25/3.24  #Close   : 0
% 9.25/3.24  
% 9.25/3.24  Ordering : KBO
% 9.25/3.24  
% 9.25/3.24  Simplification rules
% 9.25/3.24  ----------------------
% 9.25/3.24  #Subsume      : 657
% 9.25/3.24  #Demod        : 2334
% 9.25/3.24  #Tautology    : 1251
% 9.25/3.24  #SimpNegUnit  : 82
% 9.25/3.24  #BackRed      : 133
% 9.25/3.24  
% 9.25/3.24  #Partial instantiations: 0
% 9.25/3.24  #Strategies tried      : 1
% 9.25/3.24  
% 9.25/3.24  Timing (in seconds)
% 9.25/3.24  ----------------------
% 9.25/3.24  Preprocessing        : 0.37
% 9.25/3.24  Parsing              : 0.19
% 9.25/3.24  CNF conversion       : 0.03
% 9.25/3.24  Main loop            : 2.09
% 9.25/3.24  Inferencing          : 0.60
% 9.25/3.24  Reduction            : 0.79
% 9.25/3.24  Demodulation         : 0.60
% 9.25/3.25  BG Simplification    : 0.07
% 9.25/3.25  Subsumption          : 0.47
% 9.25/3.25  Abstraction          : 0.09
% 9.25/3.25  MUC search           : 0.00
% 9.25/3.25  Cooper               : 0.00
% 9.25/3.25  Total                : 2.50
% 9.25/3.25  Index Insertion      : 0.00
% 9.25/3.25  Index Deletion       : 0.00
% 9.25/3.25  Index Matching       : 0.00
% 9.25/3.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
