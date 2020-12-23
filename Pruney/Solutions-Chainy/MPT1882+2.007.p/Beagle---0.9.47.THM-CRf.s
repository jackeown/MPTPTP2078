%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:13 EST 2020

% Result     : Theorem 4.69s
% Output     : CNFRefutation 4.69s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 391 expanded)
%              Number of leaves         :   39 ( 147 expanded)
%              Depth                    :   13
%              Number of atoms          :  230 (1418 expanded)
%              Number of equality atoms :   27 (  88 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k4_xboole_0 > k4_tarski > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_166,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v2_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ( v3_tex_2(B,A)
            <=> v1_zfmisc_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tex_2)).

tff(f_48,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_52,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_zfmisc_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).

tff(f_114,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tex_2(B,A)
          <=> ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( v2_tex_2(C,A)
                      & r1_tarski(B,C) )
                   => B = C ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_146,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ( v2_tex_2(B,A)
          <=> v1_zfmisc_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

tff(f_127,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_14,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_75,plain,(
    ! [A_53] :
      ( k1_xboole_0 = A_53
      | ~ r1_tarski(A_53,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_81,plain,(
    ! [B_54] : k4_xboole_0(k1_xboole_0,B_54) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_75])).

tff(c_20,plain,(
    ! [A_15,B_16] : r1_xboole_0(k4_xboole_0(A_15,B_16),B_16) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_86,plain,(
    ! [B_54] : r1_xboole_0(k1_xboole_0,B_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_20])).

tff(c_153,plain,(
    ! [A_63,B_64] :
      ( k3_xboole_0(A_63,B_64) = k1_xboole_0
      | ~ r1_xboole_0(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_162,plain,(
    ! [B_65] : k3_xboole_0(k1_xboole_0,B_65) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_86,c_153])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_167,plain,(
    ! [B_65] : k3_xboole_0(B_65,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_2])).

tff(c_70,plain,
    ( v3_tex_2('#skF_5','#skF_4')
    | v1_zfmisc_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_74,plain,(
    v1_zfmisc_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_64,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | ~ v3_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_96,plain,(
    ~ v3_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_64])).

tff(c_24,plain,(
    ! [A_19] :
      ( v1_zfmisc_1(A_19)
      | ~ v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_56,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_708,plain,(
    ! [A_125,B_126] :
      ( '#skF_3'(A_125,B_126) != B_126
      | v3_tex_2(B_126,A_125)
      | ~ v2_tex_2(B_126,A_125)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ l1_pre_topc(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_711,plain,
    ( '#skF_3'('#skF_4','#skF_5') != '#skF_5'
    | v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_708])).

tff(c_714,plain,
    ( '#skF_3'('#skF_4','#skF_5') != '#skF_5'
    | v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_711])).

tff(c_715,plain,
    ( '#skF_3'('#skF_4','#skF_5') != '#skF_5'
    | ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_714])).

tff(c_716,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_715])).

tff(c_60,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_58,plain,(
    v2_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_1274,plain,(
    ! [B_157,A_158] :
      ( v2_tex_2(B_157,A_158)
      | ~ v1_zfmisc_1(B_157)
      | ~ m1_subset_1(B_157,k1_zfmisc_1(u1_struct_0(A_158)))
      | v1_xboole_0(B_157)
      | ~ l1_pre_topc(A_158)
      | ~ v2_tdlat_3(A_158)
      | ~ v2_pre_topc(A_158)
      | v2_struct_0(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1280,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_1274])).

tff(c_1284,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_74,c_1280])).

tff(c_1286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_54,c_716,c_1284])).

tff(c_1287,plain,(
    '#skF_3'('#skF_4','#skF_5') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_715])).

tff(c_1288,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_715])).

tff(c_1385,plain,(
    ! [B_166,A_167] :
      ( r1_tarski(B_166,'#skF_3'(A_167,B_166))
      | v3_tex_2(B_166,A_167)
      | ~ v2_tex_2(B_166,A_167)
      | ~ m1_subset_1(B_166,k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ l1_pre_topc(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1387,plain,
    ( r1_tarski('#skF_5','#skF_3'('#skF_4','#skF_5'))
    | v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_1385])).

tff(c_1390,plain,
    ( r1_tarski('#skF_5','#skF_3'('#skF_4','#skF_5'))
    | v3_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1288,c_1387])).

tff(c_1391,plain,(
    r1_tarski('#skF_5','#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_1390])).

tff(c_46,plain,(
    ! [B_43,A_41] :
      ( B_43 = A_41
      | ~ r1_tarski(A_41,B_43)
      | ~ v1_zfmisc_1(B_43)
      | v1_xboole_0(B_43)
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1400,plain,
    ( '#skF_3'('#skF_4','#skF_5') = '#skF_5'
    | ~ v1_zfmisc_1('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1391,c_46])).

tff(c_1409,plain,
    ( ~ v1_zfmisc_1('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1287,c_1400])).

tff(c_1410,plain,(
    ~ v1_zfmisc_1('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1409])).

tff(c_1414,plain,(
    ~ v1_xboole_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_24,c_1410])).

tff(c_1289,plain,(
    ! [A_159,B_160] :
      ( v2_tex_2('#skF_3'(A_159,B_160),A_159)
      | v3_tex_2(B_160,A_159)
      | ~ v2_tex_2(B_160,A_159)
      | ~ m1_subset_1(B_160,k1_zfmisc_1(u1_struct_0(A_159)))
      | ~ l1_pre_topc(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1291,plain,
    ( v2_tex_2('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_1289])).

tff(c_1294,plain,
    ( v2_tex_2('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v3_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1288,c_1291])).

tff(c_1295,plain,(
    v2_tex_2('#skF_3'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_1294])).

tff(c_1670,plain,(
    ! [A_185,B_186] :
      ( m1_subset_1('#skF_3'(A_185,B_186),k1_zfmisc_1(u1_struct_0(A_185)))
      | v3_tex_2(B_186,A_185)
      | ~ v2_tex_2(B_186,A_185)
      | ~ m1_subset_1(B_186,k1_zfmisc_1(u1_struct_0(A_185)))
      | ~ l1_pre_topc(A_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_50,plain,(
    ! [B_46,A_44] :
      ( v1_zfmisc_1(B_46)
      | ~ v2_tex_2(B_46,A_44)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_44)))
      | v1_xboole_0(B_46)
      | ~ l1_pre_topc(A_44)
      | ~ v2_tdlat_3(A_44)
      | ~ v2_pre_topc(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_2504,plain,(
    ! [A_241,B_242] :
      ( v1_zfmisc_1('#skF_3'(A_241,B_242))
      | ~ v2_tex_2('#skF_3'(A_241,B_242),A_241)
      | v1_xboole_0('#skF_3'(A_241,B_242))
      | ~ v2_tdlat_3(A_241)
      | ~ v2_pre_topc(A_241)
      | v2_struct_0(A_241)
      | v3_tex_2(B_242,A_241)
      | ~ v2_tex_2(B_242,A_241)
      | ~ m1_subset_1(B_242,k1_zfmisc_1(u1_struct_0(A_241)))
      | ~ l1_pre_topc(A_241) ) ),
    inference(resolution,[status(thm)],[c_1670,c_50])).

tff(c_2508,plain,
    ( v1_zfmisc_1('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | v3_tex_2('#skF_5','#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_1295,c_2504])).

tff(c_2512,plain,
    ( v1_zfmisc_1('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4')
    | v3_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_1288,c_60,c_58,c_2508])).

tff(c_2514,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_62,c_1414,c_1410,c_2512])).

tff(c_2515,plain,(
    v1_xboole_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1409])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_136,plain,(
    ! [B_59,A_60] :
      ( ~ v1_xboole_0(B_59)
      | B_59 = A_60
      | ~ v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_139,plain,(
    ! [A_60] :
      ( k1_xboole_0 = A_60
      | ~ v1_xboole_0(A_60) ) ),
    inference(resolution,[status(thm)],[c_8,c_136])).

tff(c_2522,plain,(
    '#skF_3'('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2515,c_139])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_313,plain,(
    ! [B_77,A_78] :
      ( ~ r1_xboole_0(B_77,A_78)
      | ~ r1_tarski(B_77,A_78)
      | v1_xboole_0(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_323,plain,(
    ! [A_3,B_4] :
      ( ~ r1_tarski(A_3,B_4)
      | v1_xboole_0(A_3)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_313])).

tff(c_1397,plain,
    ( v1_xboole_0('#skF_5')
    | k3_xboole_0('#skF_5','#skF_3'('#skF_4','#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1391,c_323])).

tff(c_1406,plain,(
    k3_xboole_0('#skF_5','#skF_3'('#skF_4','#skF_5')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1397])).

tff(c_2530,plain,(
    k3_xboole_0('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2522,c_1406])).

tff(c_2537,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_2530])).

tff(c_2539,plain,(
    ~ v1_zfmisc_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_2538,plain,(
    v3_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_3017,plain,(
    ! [B_302,A_303] :
      ( v2_tex_2(B_302,A_303)
      | ~ v3_tex_2(B_302,A_303)
      | ~ m1_subset_1(B_302,k1_zfmisc_1(u1_struct_0(A_303)))
      | ~ l1_pre_topc(A_303) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_3020,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ v3_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_3017])).

tff(c_3023,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2538,c_3020])).

tff(c_3253,plain,(
    ! [B_342,A_343] :
      ( v1_zfmisc_1(B_342)
      | ~ v2_tex_2(B_342,A_343)
      | ~ m1_subset_1(B_342,k1_zfmisc_1(u1_struct_0(A_343)))
      | v1_xboole_0(B_342)
      | ~ l1_pre_topc(A_343)
      | ~ v2_tdlat_3(A_343)
      | ~ v2_pre_topc(A_343)
      | v2_struct_0(A_343) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_3259,plain,
    ( v1_zfmisc_1('#skF_5')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_3253])).

tff(c_3263,plain,
    ( v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_3023,c_3259])).

tff(c_3265,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_54,c_2539,c_3263])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:11:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.69/1.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.69/1.85  
% 4.69/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.69/1.85  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k4_xboole_0 > k4_tarski > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_4 > #skF_1
% 4.69/1.85  
% 4.69/1.85  %Foreground sorts:
% 4.69/1.85  
% 4.69/1.85  
% 4.69/1.85  %Background operators:
% 4.69/1.85  
% 4.69/1.85  
% 4.69/1.85  %Foreground operators:
% 4.69/1.85  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.69/1.85  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.69/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.69/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.69/1.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.69/1.85  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.69/1.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.69/1.85  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.69/1.85  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.69/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.69/1.85  tff('#skF_5', type, '#skF_5': $i).
% 4.69/1.85  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 4.69/1.85  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.69/1.85  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.69/1.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.69/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.69/1.85  tff('#skF_4', type, '#skF_4': $i).
% 4.69/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.69/1.85  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 4.69/1.85  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.69/1.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.69/1.85  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.69/1.85  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.69/1.85  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.69/1.85  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 4.69/1.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.69/1.85  
% 4.69/1.87  tff(f_166, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_tex_2)).
% 4.69/1.87  tff(f_48, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.69/1.87  tff(f_52, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 4.69/1.87  tff(f_62, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.69/1.87  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.69/1.87  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.69/1.87  tff(f_74, axiom, (![A]: (v1_xboole_0(A) => v1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_zfmisc_1)).
% 4.69/1.87  tff(f_114, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 4.69/1.87  tff(f_146, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 4.69/1.87  tff(f_127, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 4.69/1.87  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.69/1.87  tff(f_70, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 4.69/1.87  tff(f_60, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 4.69/1.87  tff(c_62, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_166])).
% 4.69/1.87  tff(c_54, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_166])).
% 4.69/1.87  tff(c_14, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.69/1.87  tff(c_75, plain, (![A_53]: (k1_xboole_0=A_53 | ~r1_tarski(A_53, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.69/1.87  tff(c_81, plain, (![B_54]: (k4_xboole_0(k1_xboole_0, B_54)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_75])).
% 4.69/1.87  tff(c_20, plain, (![A_15, B_16]: (r1_xboole_0(k4_xboole_0(A_15, B_16), B_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.69/1.87  tff(c_86, plain, (![B_54]: (r1_xboole_0(k1_xboole_0, B_54))), inference(superposition, [status(thm), theory('equality')], [c_81, c_20])).
% 4.69/1.87  tff(c_153, plain, (![A_63, B_64]: (k3_xboole_0(A_63, B_64)=k1_xboole_0 | ~r1_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.69/1.87  tff(c_162, plain, (![B_65]: (k3_xboole_0(k1_xboole_0, B_65)=k1_xboole_0)), inference(resolution, [status(thm)], [c_86, c_153])).
% 4.69/1.87  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.69/1.87  tff(c_167, plain, (![B_65]: (k3_xboole_0(B_65, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_162, c_2])).
% 4.69/1.87  tff(c_70, plain, (v3_tex_2('#skF_5', '#skF_4') | v1_zfmisc_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_166])).
% 4.69/1.87  tff(c_74, plain, (v1_zfmisc_1('#skF_5')), inference(splitLeft, [status(thm)], [c_70])).
% 4.69/1.87  tff(c_64, plain, (~v1_zfmisc_1('#skF_5') | ~v3_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_166])).
% 4.69/1.87  tff(c_96, plain, (~v3_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_64])).
% 4.69/1.87  tff(c_24, plain, (![A_19]: (v1_zfmisc_1(A_19) | ~v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.69/1.87  tff(c_56, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_166])).
% 4.69/1.87  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_166])).
% 4.69/1.87  tff(c_708, plain, (![A_125, B_126]: ('#skF_3'(A_125, B_126)!=B_126 | v3_tex_2(B_126, A_125) | ~v2_tex_2(B_126, A_125) | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0(A_125))) | ~l1_pre_topc(A_125))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.69/1.87  tff(c_711, plain, ('#skF_3'('#skF_4', '#skF_5')!='#skF_5' | v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_52, c_708])).
% 4.69/1.87  tff(c_714, plain, ('#skF_3'('#skF_4', '#skF_5')!='#skF_5' | v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_711])).
% 4.69/1.87  tff(c_715, plain, ('#skF_3'('#skF_4', '#skF_5')!='#skF_5' | ~v2_tex_2('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_96, c_714])).
% 4.69/1.87  tff(c_716, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_715])).
% 4.69/1.87  tff(c_60, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_166])).
% 4.69/1.87  tff(c_58, plain, (v2_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_166])).
% 4.69/1.87  tff(c_1274, plain, (![B_157, A_158]: (v2_tex_2(B_157, A_158) | ~v1_zfmisc_1(B_157) | ~m1_subset_1(B_157, k1_zfmisc_1(u1_struct_0(A_158))) | v1_xboole_0(B_157) | ~l1_pre_topc(A_158) | ~v2_tdlat_3(A_158) | ~v2_pre_topc(A_158) | v2_struct_0(A_158))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.69/1.87  tff(c_1280, plain, (v2_tex_2('#skF_5', '#skF_4') | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_1274])).
% 4.69/1.87  tff(c_1284, plain, (v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_74, c_1280])).
% 4.69/1.87  tff(c_1286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_54, c_716, c_1284])).
% 4.69/1.87  tff(c_1287, plain, ('#skF_3'('#skF_4', '#skF_5')!='#skF_5'), inference(splitRight, [status(thm)], [c_715])).
% 4.69/1.87  tff(c_1288, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_715])).
% 4.69/1.87  tff(c_1385, plain, (![B_166, A_167]: (r1_tarski(B_166, '#skF_3'(A_167, B_166)) | v3_tex_2(B_166, A_167) | ~v2_tex_2(B_166, A_167) | ~m1_subset_1(B_166, k1_zfmisc_1(u1_struct_0(A_167))) | ~l1_pre_topc(A_167))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.69/1.87  tff(c_1387, plain, (r1_tarski('#skF_5', '#skF_3'('#skF_4', '#skF_5')) | v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_52, c_1385])).
% 4.69/1.87  tff(c_1390, plain, (r1_tarski('#skF_5', '#skF_3'('#skF_4', '#skF_5')) | v3_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1288, c_1387])).
% 4.69/1.87  tff(c_1391, plain, (r1_tarski('#skF_5', '#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_96, c_1390])).
% 4.69/1.87  tff(c_46, plain, (![B_43, A_41]: (B_43=A_41 | ~r1_tarski(A_41, B_43) | ~v1_zfmisc_1(B_43) | v1_xboole_0(B_43) | v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.69/1.87  tff(c_1400, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5' | ~v1_zfmisc_1('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_1391, c_46])).
% 4.69/1.87  tff(c_1409, plain, (~v1_zfmisc_1('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_54, c_1287, c_1400])).
% 4.69/1.87  tff(c_1410, plain, (~v1_zfmisc_1('#skF_3'('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_1409])).
% 4.69/1.87  tff(c_1414, plain, (~v1_xboole_0('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_24, c_1410])).
% 4.69/1.87  tff(c_1289, plain, (![A_159, B_160]: (v2_tex_2('#skF_3'(A_159, B_160), A_159) | v3_tex_2(B_160, A_159) | ~v2_tex_2(B_160, A_159) | ~m1_subset_1(B_160, k1_zfmisc_1(u1_struct_0(A_159))) | ~l1_pre_topc(A_159))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.69/1.87  tff(c_1291, plain, (v2_tex_2('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_52, c_1289])).
% 4.69/1.87  tff(c_1294, plain, (v2_tex_2('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v3_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1288, c_1291])).
% 4.69/1.87  tff(c_1295, plain, (v2_tex_2('#skF_3'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_96, c_1294])).
% 4.69/1.87  tff(c_1670, plain, (![A_185, B_186]: (m1_subset_1('#skF_3'(A_185, B_186), k1_zfmisc_1(u1_struct_0(A_185))) | v3_tex_2(B_186, A_185) | ~v2_tex_2(B_186, A_185) | ~m1_subset_1(B_186, k1_zfmisc_1(u1_struct_0(A_185))) | ~l1_pre_topc(A_185))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.69/1.87  tff(c_50, plain, (![B_46, A_44]: (v1_zfmisc_1(B_46) | ~v2_tex_2(B_46, A_44) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_44))) | v1_xboole_0(B_46) | ~l1_pre_topc(A_44) | ~v2_tdlat_3(A_44) | ~v2_pre_topc(A_44) | v2_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.69/1.87  tff(c_2504, plain, (![A_241, B_242]: (v1_zfmisc_1('#skF_3'(A_241, B_242)) | ~v2_tex_2('#skF_3'(A_241, B_242), A_241) | v1_xboole_0('#skF_3'(A_241, B_242)) | ~v2_tdlat_3(A_241) | ~v2_pre_topc(A_241) | v2_struct_0(A_241) | v3_tex_2(B_242, A_241) | ~v2_tex_2(B_242, A_241) | ~m1_subset_1(B_242, k1_zfmisc_1(u1_struct_0(A_241))) | ~l1_pre_topc(A_241))), inference(resolution, [status(thm)], [c_1670, c_50])).
% 4.69/1.87  tff(c_2508, plain, (v1_zfmisc_1('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_3'('#skF_4', '#skF_5')) | ~v2_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | v3_tex_2('#skF_5', '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_1295, c_2504])).
% 4.69/1.87  tff(c_2512, plain, (v1_zfmisc_1('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_4') | v3_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_1288, c_60, c_58, c_2508])).
% 4.69/1.87  tff(c_2514, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_62, c_1414, c_1410, c_2512])).
% 4.69/1.87  tff(c_2515, plain, (v1_xboole_0('#skF_3'('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_1409])).
% 4.69/1.87  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.69/1.87  tff(c_136, plain, (![B_59, A_60]: (~v1_xboole_0(B_59) | B_59=A_60 | ~v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.69/1.87  tff(c_139, plain, (![A_60]: (k1_xboole_0=A_60 | ~v1_xboole_0(A_60))), inference(resolution, [status(thm)], [c_8, c_136])).
% 4.69/1.87  tff(c_2522, plain, ('#skF_3'('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_2515, c_139])).
% 4.69/1.87  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.69/1.87  tff(c_313, plain, (![B_77, A_78]: (~r1_xboole_0(B_77, A_78) | ~r1_tarski(B_77, A_78) | v1_xboole_0(B_77))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.69/1.87  tff(c_323, plain, (![A_3, B_4]: (~r1_tarski(A_3, B_4) | v1_xboole_0(A_3) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_313])).
% 4.69/1.87  tff(c_1397, plain, (v1_xboole_0('#skF_5') | k3_xboole_0('#skF_5', '#skF_3'('#skF_4', '#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_1391, c_323])).
% 4.69/1.87  tff(c_1406, plain, (k3_xboole_0('#skF_5', '#skF_3'('#skF_4', '#skF_5'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_54, c_1397])).
% 4.69/1.87  tff(c_2530, plain, (k3_xboole_0('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2522, c_1406])).
% 4.69/1.87  tff(c_2537, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_167, c_2530])).
% 4.69/1.87  tff(c_2539, plain, (~v1_zfmisc_1('#skF_5')), inference(splitRight, [status(thm)], [c_70])).
% 4.69/1.87  tff(c_2538, plain, (v3_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_70])).
% 4.69/1.87  tff(c_3017, plain, (![B_302, A_303]: (v2_tex_2(B_302, A_303) | ~v3_tex_2(B_302, A_303) | ~m1_subset_1(B_302, k1_zfmisc_1(u1_struct_0(A_303))) | ~l1_pre_topc(A_303))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.69/1.87  tff(c_3020, plain, (v2_tex_2('#skF_5', '#skF_4') | ~v3_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_52, c_3017])).
% 4.69/1.87  tff(c_3023, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2538, c_3020])).
% 4.69/1.87  tff(c_3253, plain, (![B_342, A_343]: (v1_zfmisc_1(B_342) | ~v2_tex_2(B_342, A_343) | ~m1_subset_1(B_342, k1_zfmisc_1(u1_struct_0(A_343))) | v1_xboole_0(B_342) | ~l1_pre_topc(A_343) | ~v2_tdlat_3(A_343) | ~v2_pre_topc(A_343) | v2_struct_0(A_343))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.69/1.87  tff(c_3259, plain, (v1_zfmisc_1('#skF_5') | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_3253])).
% 4.69/1.87  tff(c_3263, plain, (v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_3023, c_3259])).
% 4.69/1.87  tff(c_3265, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_54, c_2539, c_3263])).
% 4.69/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.69/1.87  
% 4.69/1.87  Inference rules
% 4.69/1.87  ----------------------
% 4.69/1.87  #Ref     : 0
% 4.69/1.87  #Sup     : 747
% 4.69/1.87  #Fact    : 6
% 4.69/1.87  #Define  : 0
% 4.69/1.87  #Split   : 10
% 4.69/1.87  #Chain   : 0
% 4.69/1.87  #Close   : 0
% 4.69/1.87  
% 4.69/1.87  Ordering : KBO
% 4.69/1.87  
% 4.69/1.87  Simplification rules
% 4.69/1.87  ----------------------
% 4.69/1.87  #Subsume      : 240
% 4.69/1.87  #Demod        : 401
% 4.69/1.87  #Tautology    : 346
% 4.69/1.87  #SimpNegUnit  : 96
% 4.69/1.87  #BackRed      : 8
% 4.69/1.87  
% 4.69/1.87  #Partial instantiations: 0
% 4.69/1.87  #Strategies tried      : 1
% 4.69/1.87  
% 4.69/1.87  Timing (in seconds)
% 4.69/1.87  ----------------------
% 4.69/1.88  Preprocessing        : 0.32
% 4.69/1.88  Parsing              : 0.17
% 4.69/1.88  CNF conversion       : 0.02
% 4.69/1.88  Main loop            : 0.74
% 4.69/1.88  Inferencing          : 0.25
% 4.69/1.88  Reduction            : 0.26
% 4.69/1.88  Demodulation         : 0.19
% 4.69/1.88  BG Simplification    : 0.03
% 4.69/1.88  Subsumption          : 0.14
% 4.69/1.88  Abstraction          : 0.03
% 4.69/1.88  MUC search           : 0.00
% 4.69/1.88  Cooper               : 0.00
% 4.69/1.88  Total                : 1.09
% 4.69/1.88  Index Insertion      : 0.00
% 4.69/1.88  Index Deletion       : 0.00
% 4.69/1.88  Index Matching       : 0.00
% 4.69/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
