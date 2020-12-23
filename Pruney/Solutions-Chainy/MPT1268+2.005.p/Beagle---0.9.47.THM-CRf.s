%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:47 EST 2020

% Result     : Theorem 7.67s
% Output     : CNFRefutation 7.67s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 164 expanded)
%              Number of leaves         :   37 (  71 expanded)
%              Depth                    :    8
%              Number of atoms          :  176 ( 473 expanded)
%              Number of equality atoms :   40 (  83 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_mcart_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_157,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r1_tarski(C,B)
                      & v3_pre_topc(C,A) )
                   => C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).

tff(f_138,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_129,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                 => ( ( v3_pre_topc(D,B)
                     => k1_tops_1(B,D) = D )
                    & ( k1_tops_1(A,C) = C
                     => v3_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_49,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(c_54,plain,
    ( k1_xboole_0 != '#skF_5'
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_74,plain,(
    ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_50,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_1762,plain,(
    ! [B_198,A_199] :
      ( v2_tops_1(B_198,A_199)
      | k1_tops_1(A_199,B_198) != k1_xboole_0
      | ~ m1_subset_1(B_198,k1_zfmisc_1(u1_struct_0(A_199)))
      | ~ l1_pre_topc(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1772,plain,
    ( v2_tops_1('#skF_4','#skF_3')
    | k1_tops_1('#skF_3','#skF_4') != k1_xboole_0
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_1762])).

tff(c_1777,plain,
    ( v2_tops_1('#skF_4','#skF_3')
    | k1_tops_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1772])).

tff(c_1778,plain,(
    k1_tops_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1777])).

tff(c_1374,plain,(
    ! [A_184,B_185] :
      ( r1_tarski(k1_tops_1(A_184,B_185),B_185)
      | ~ m1_subset_1(B_185,k1_zfmisc_1(u1_struct_0(A_184)))
      | ~ l1_pre_topc(A_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1381,plain,
    ( r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_1374])).

tff(c_1386,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1381])).

tff(c_52,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_1904,plain,(
    ! [A_204,B_205] :
      ( v3_pre_topc(k1_tops_1(A_204,B_205),A_204)
      | ~ m1_subset_1(B_205,k1_zfmisc_1(u1_struct_0(A_204)))
      | ~ l1_pre_topc(A_204)
      | ~ v2_pre_topc(A_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1911,plain,
    ( v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_1904])).

tff(c_1916,plain,(
    v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1911])).

tff(c_138,plain,(
    ! [A_88,B_89] :
      ( r1_tarski(A_88,B_89)
      | ~ m1_subset_1(A_88,k1_zfmisc_1(B_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_146,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_138])).

tff(c_863,plain,(
    ! [A_144,C_145,B_146] :
      ( r1_tarski(A_144,C_145)
      | ~ r1_tarski(B_146,C_145)
      | ~ r1_tarski(A_144,B_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_877,plain,(
    ! [A_144] :
      ( r1_tarski(A_144,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_144,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_146,c_863])).

tff(c_20,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,k1_zfmisc_1(B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_72,plain,(
    ! [C_75] :
      ( v2_tops_1('#skF_4','#skF_3')
      | k1_xboole_0 = C_75
      | ~ v3_pre_topc(C_75,'#skF_3')
      | ~ r1_tarski(C_75,'#skF_4')
      | ~ m1_subset_1(C_75,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_910,plain,(
    ! [C_151] :
      ( k1_xboole_0 = C_151
      | ~ v3_pre_topc(C_151,'#skF_3')
      | ~ r1_tarski(C_151,'#skF_4')
      | ~ m1_subset_1(C_151,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_72])).

tff(c_1425,plain,(
    ! [A_188] :
      ( k1_xboole_0 = A_188
      | ~ v3_pre_topc(A_188,'#skF_3')
      | ~ r1_tarski(A_188,'#skF_4')
      | ~ r1_tarski(A_188,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_20,c_910])).

tff(c_1472,plain,(
    ! [A_144] :
      ( k1_xboole_0 = A_144
      | ~ v3_pre_topc(A_144,'#skF_3')
      | ~ r1_tarski(A_144,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_877,c_1425])).

tff(c_1919,plain,
    ( k1_tops_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1916,c_1472])).

tff(c_1922,plain,(
    k1_tops_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1386,c_1919])).

tff(c_1924,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1778,c_1922])).

tff(c_1925,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1926,plain,(
    v2_tops_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_58,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_1967,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1926,c_58])).

tff(c_56,plain,
    ( v3_pre_topc('#skF_5','#skF_3')
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_1970,plain,(
    v3_pre_topc('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1926,c_56])).

tff(c_60,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_1995,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1926,c_60])).

tff(c_42,plain,(
    ! [B_58,D_64,C_62,A_50] :
      ( k1_tops_1(B_58,D_64) = D_64
      | ~ v3_pre_topc(D_64,B_58)
      | ~ m1_subset_1(D_64,k1_zfmisc_1(u1_struct_0(B_58)))
      | ~ m1_subset_1(C_62,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(B_58)
      | ~ l1_pre_topc(A_50)
      | ~ v2_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_4144,plain,(
    ! [C_317,A_318] :
      ( ~ m1_subset_1(C_317,k1_zfmisc_1(u1_struct_0(A_318)))
      | ~ l1_pre_topc(A_318)
      | ~ v2_pre_topc(A_318) ) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_4150,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1995,c_4144])).

tff(c_4162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_4150])).

tff(c_4223,plain,(
    ! [B_320,D_321] :
      ( k1_tops_1(B_320,D_321) = D_321
      | ~ v3_pre_topc(D_321,B_320)
      | ~ m1_subset_1(D_321,k1_zfmisc_1(u1_struct_0(B_320)))
      | ~ l1_pre_topc(B_320) ) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_4229,plain,
    ( k1_tops_1('#skF_3','#skF_5') = '#skF_5'
    | ~ v3_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1995,c_4223])).

tff(c_4240,plain,(
    k1_tops_1('#skF_3','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1970,c_4229])).

tff(c_14,plain,(
    ! [B_15,A_14] : k2_tarski(B_15,A_14) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1978,plain,(
    ! [A_213,B_214] : k1_setfam_1(k2_tarski(A_213,B_214)) = k3_xboole_0(A_213,B_214) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2104,plain,(
    ! [B_227,A_228] : k1_setfam_1(k2_tarski(B_227,A_228)) = k3_xboole_0(A_228,B_227) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1978])).

tff(c_16,plain,(
    ! [A_16,B_17] : k1_setfam_1(k2_tarski(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2217,plain,(
    ! [B_232,A_233] : k3_xboole_0(B_232,A_233) = k3_xboole_0(A_233,B_232) ),
    inference(superposition,[status(thm),theory(equality)],[c_2104,c_16])).

tff(c_10,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1996,plain,(
    ! [A_217,B_218] :
      ( k3_xboole_0(A_217,B_218) = A_217
      | ~ r1_tarski(A_217,B_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2004,plain,(
    ! [A_11] : k3_xboole_0(k1_xboole_0,A_11) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_1996])).

tff(c_2239,plain,(
    ! [B_232] : k3_xboole_0(B_232,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2217,c_2004])).

tff(c_3303,plain,(
    ! [A_289,B_290] :
      ( k1_tops_1(A_289,B_290) = k1_xboole_0
      | ~ v2_tops_1(B_290,A_289)
      | ~ m1_subset_1(B_290,k1_zfmisc_1(u1_struct_0(A_289)))
      | ~ l1_pre_topc(A_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_3316,plain,
    ( k1_tops_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ v2_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_3303])).

tff(c_3324,plain,(
    k1_tops_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1926,c_3316])).

tff(c_3690,plain,(
    ! [A_305,B_306,C_307] :
      ( r1_tarski(k1_tops_1(A_305,B_306),k1_tops_1(A_305,C_307))
      | ~ r1_tarski(B_306,C_307)
      | ~ m1_subset_1(C_307,k1_zfmisc_1(u1_struct_0(A_305)))
      | ~ m1_subset_1(B_306,k1_zfmisc_1(u1_struct_0(A_305)))
      | ~ l1_pre_topc(A_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_8,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_9531,plain,(
    ! [A_444,B_445,C_446] :
      ( k3_xboole_0(k1_tops_1(A_444,B_445),k1_tops_1(A_444,C_446)) = k1_tops_1(A_444,B_445)
      | ~ r1_tarski(B_445,C_446)
      | ~ m1_subset_1(C_446,k1_zfmisc_1(u1_struct_0(A_444)))
      | ~ m1_subset_1(B_445,k1_zfmisc_1(u1_struct_0(A_444)))
      | ~ l1_pre_topc(A_444) ) ),
    inference(resolution,[status(thm)],[c_3690,c_8])).

tff(c_9542,plain,(
    ! [B_445] :
      ( k3_xboole_0(k1_tops_1('#skF_3',B_445),k1_tops_1('#skF_3','#skF_4')) = k1_tops_1('#skF_3',B_445)
      | ~ r1_tarski(B_445,'#skF_4')
      | ~ m1_subset_1(B_445,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_9531])).

tff(c_9729,plain,(
    ! [B_451] :
      ( k1_tops_1('#skF_3',B_451) = k1_xboole_0
      | ~ r1_tarski(B_451,'#skF_4')
      | ~ m1_subset_1(B_451,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2239,c_3324,c_9542])).

tff(c_9739,plain,
    ( k1_tops_1('#skF_3','#skF_5') = k1_xboole_0
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_1995,c_9729])).

tff(c_9755,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1967,c_4240,c_9739])).

tff(c_9757,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1925,c_9755])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:29:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.67/2.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.67/2.60  
% 7.67/2.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.67/2.61  %$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_mcart_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 7.67/2.61  
% 7.67/2.61  %Foreground sorts:
% 7.67/2.61  
% 7.67/2.61  
% 7.67/2.61  %Background operators:
% 7.67/2.61  
% 7.67/2.61  
% 7.67/2.61  %Foreground operators:
% 7.67/2.61  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 7.67/2.61  tff('#skF_2', type, '#skF_2': $i > $i).
% 7.67/2.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.67/2.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.67/2.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.67/2.61  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.67/2.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.67/2.61  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 7.67/2.61  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 7.67/2.61  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.67/2.61  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.67/2.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.67/2.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.67/2.61  tff('#skF_5', type, '#skF_5': $i).
% 7.67/2.61  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 7.67/2.61  tff('#skF_3', type, '#skF_3': $i).
% 7.67/2.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.67/2.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.67/2.61  tff('#skF_4', type, '#skF_4': $i).
% 7.67/2.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.67/2.61  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.67/2.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.67/2.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.67/2.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.67/2.61  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.67/2.61  
% 7.67/2.62  tff(f_157, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tops_1)).
% 7.67/2.62  tff(f_138, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 7.67/2.62  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 7.67/2.62  tff(f_82, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 7.67/2.62  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.67/2.62  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 7.67/2.62  tff(f_129, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 7.67/2.62  tff(f_47, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 7.67/2.62  tff(f_49, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 7.67/2.62  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.67/2.62  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.67/2.62  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 7.67/2.62  tff(c_54, plain, (k1_xboole_0!='#skF_5' | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_157])).
% 7.67/2.62  tff(c_74, plain, (~v2_tops_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_54])).
% 7.67/2.62  tff(c_50, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_157])).
% 7.67/2.62  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_157])).
% 7.67/2.62  tff(c_1762, plain, (![B_198, A_199]: (v2_tops_1(B_198, A_199) | k1_tops_1(A_199, B_198)!=k1_xboole_0 | ~m1_subset_1(B_198, k1_zfmisc_1(u1_struct_0(A_199))) | ~l1_pre_topc(A_199))), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.67/2.62  tff(c_1772, plain, (v2_tops_1('#skF_4', '#skF_3') | k1_tops_1('#skF_3', '#skF_4')!=k1_xboole_0 | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_48, c_1762])).
% 7.67/2.62  tff(c_1777, plain, (v2_tops_1('#skF_4', '#skF_3') | k1_tops_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1772])).
% 7.67/2.62  tff(c_1778, plain, (k1_tops_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_74, c_1777])).
% 7.67/2.62  tff(c_1374, plain, (![A_184, B_185]: (r1_tarski(k1_tops_1(A_184, B_185), B_185) | ~m1_subset_1(B_185, k1_zfmisc_1(u1_struct_0(A_184))) | ~l1_pre_topc(A_184))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.67/2.62  tff(c_1381, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_48, c_1374])).
% 7.67/2.62  tff(c_1386, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1381])).
% 7.67/2.62  tff(c_52, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_157])).
% 7.67/2.62  tff(c_1904, plain, (![A_204, B_205]: (v3_pre_topc(k1_tops_1(A_204, B_205), A_204) | ~m1_subset_1(B_205, k1_zfmisc_1(u1_struct_0(A_204))) | ~l1_pre_topc(A_204) | ~v2_pre_topc(A_204))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.67/2.62  tff(c_1911, plain, (v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_48, c_1904])).
% 7.67/2.62  tff(c_1916, plain, (v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1911])).
% 7.67/2.62  tff(c_138, plain, (![A_88, B_89]: (r1_tarski(A_88, B_89) | ~m1_subset_1(A_88, k1_zfmisc_1(B_89)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.67/2.62  tff(c_146, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_138])).
% 7.67/2.62  tff(c_863, plain, (![A_144, C_145, B_146]: (r1_tarski(A_144, C_145) | ~r1_tarski(B_146, C_145) | ~r1_tarski(A_144, B_146))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.67/2.62  tff(c_877, plain, (![A_144]: (r1_tarski(A_144, u1_struct_0('#skF_3')) | ~r1_tarski(A_144, '#skF_4'))), inference(resolution, [status(thm)], [c_146, c_863])).
% 7.67/2.62  tff(c_20, plain, (![A_18, B_19]: (m1_subset_1(A_18, k1_zfmisc_1(B_19)) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.67/2.62  tff(c_72, plain, (![C_75]: (v2_tops_1('#skF_4', '#skF_3') | k1_xboole_0=C_75 | ~v3_pre_topc(C_75, '#skF_3') | ~r1_tarski(C_75, '#skF_4') | ~m1_subset_1(C_75, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_157])).
% 7.67/2.62  tff(c_910, plain, (![C_151]: (k1_xboole_0=C_151 | ~v3_pre_topc(C_151, '#skF_3') | ~r1_tarski(C_151, '#skF_4') | ~m1_subset_1(C_151, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_74, c_72])).
% 7.67/2.62  tff(c_1425, plain, (![A_188]: (k1_xboole_0=A_188 | ~v3_pre_topc(A_188, '#skF_3') | ~r1_tarski(A_188, '#skF_4') | ~r1_tarski(A_188, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_20, c_910])).
% 7.67/2.62  tff(c_1472, plain, (![A_144]: (k1_xboole_0=A_144 | ~v3_pre_topc(A_144, '#skF_3') | ~r1_tarski(A_144, '#skF_4'))), inference(resolution, [status(thm)], [c_877, c_1425])).
% 7.67/2.62  tff(c_1919, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0 | ~r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_1916, c_1472])).
% 7.67/2.62  tff(c_1922, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1386, c_1919])).
% 7.67/2.62  tff(c_1924, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1778, c_1922])).
% 7.67/2.62  tff(c_1925, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_54])).
% 7.67/2.62  tff(c_1926, plain, (v2_tops_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_54])).
% 7.67/2.62  tff(c_58, plain, (r1_tarski('#skF_5', '#skF_4') | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_157])).
% 7.67/2.62  tff(c_1967, plain, (r1_tarski('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1926, c_58])).
% 7.67/2.62  tff(c_56, plain, (v3_pre_topc('#skF_5', '#skF_3') | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_157])).
% 7.67/2.62  tff(c_1970, plain, (v3_pre_topc('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1926, c_56])).
% 7.67/2.62  tff(c_60, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_157])).
% 7.67/2.62  tff(c_1995, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1926, c_60])).
% 7.67/2.62  tff(c_42, plain, (![B_58, D_64, C_62, A_50]: (k1_tops_1(B_58, D_64)=D_64 | ~v3_pre_topc(D_64, B_58) | ~m1_subset_1(D_64, k1_zfmisc_1(u1_struct_0(B_58))) | ~m1_subset_1(C_62, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(B_58) | ~l1_pre_topc(A_50) | ~v2_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.67/2.62  tff(c_4144, plain, (![C_317, A_318]: (~m1_subset_1(C_317, k1_zfmisc_1(u1_struct_0(A_318))) | ~l1_pre_topc(A_318) | ~v2_pre_topc(A_318))), inference(splitLeft, [status(thm)], [c_42])).
% 7.67/2.62  tff(c_4150, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_1995, c_4144])).
% 7.67/2.62  tff(c_4162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_4150])).
% 7.67/2.62  tff(c_4223, plain, (![B_320, D_321]: (k1_tops_1(B_320, D_321)=D_321 | ~v3_pre_topc(D_321, B_320) | ~m1_subset_1(D_321, k1_zfmisc_1(u1_struct_0(B_320))) | ~l1_pre_topc(B_320))), inference(splitRight, [status(thm)], [c_42])).
% 7.67/2.62  tff(c_4229, plain, (k1_tops_1('#skF_3', '#skF_5')='#skF_5' | ~v3_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_1995, c_4223])).
% 7.67/2.62  tff(c_4240, plain, (k1_tops_1('#skF_3', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1970, c_4229])).
% 7.67/2.62  tff(c_14, plain, (![B_15, A_14]: (k2_tarski(B_15, A_14)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.67/2.62  tff(c_1978, plain, (![A_213, B_214]: (k1_setfam_1(k2_tarski(A_213, B_214))=k3_xboole_0(A_213, B_214))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.67/2.62  tff(c_2104, plain, (![B_227, A_228]: (k1_setfam_1(k2_tarski(B_227, A_228))=k3_xboole_0(A_228, B_227))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1978])).
% 7.67/2.62  tff(c_16, plain, (![A_16, B_17]: (k1_setfam_1(k2_tarski(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.67/2.62  tff(c_2217, plain, (![B_232, A_233]: (k3_xboole_0(B_232, A_233)=k3_xboole_0(A_233, B_232))), inference(superposition, [status(thm), theory('equality')], [c_2104, c_16])).
% 7.67/2.62  tff(c_10, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.67/2.62  tff(c_1996, plain, (![A_217, B_218]: (k3_xboole_0(A_217, B_218)=A_217 | ~r1_tarski(A_217, B_218))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.67/2.62  tff(c_2004, plain, (![A_11]: (k3_xboole_0(k1_xboole_0, A_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_1996])).
% 7.67/2.62  tff(c_2239, plain, (![B_232]: (k3_xboole_0(B_232, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2217, c_2004])).
% 7.67/2.62  tff(c_3303, plain, (![A_289, B_290]: (k1_tops_1(A_289, B_290)=k1_xboole_0 | ~v2_tops_1(B_290, A_289) | ~m1_subset_1(B_290, k1_zfmisc_1(u1_struct_0(A_289))) | ~l1_pre_topc(A_289))), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.67/2.62  tff(c_3316, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0 | ~v2_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_48, c_3303])).
% 7.67/2.62  tff(c_3324, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1926, c_3316])).
% 7.67/2.62  tff(c_3690, plain, (![A_305, B_306, C_307]: (r1_tarski(k1_tops_1(A_305, B_306), k1_tops_1(A_305, C_307)) | ~r1_tarski(B_306, C_307) | ~m1_subset_1(C_307, k1_zfmisc_1(u1_struct_0(A_305))) | ~m1_subset_1(B_306, k1_zfmisc_1(u1_struct_0(A_305))) | ~l1_pre_topc(A_305))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.67/2.62  tff(c_8, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.67/2.62  tff(c_9531, plain, (![A_444, B_445, C_446]: (k3_xboole_0(k1_tops_1(A_444, B_445), k1_tops_1(A_444, C_446))=k1_tops_1(A_444, B_445) | ~r1_tarski(B_445, C_446) | ~m1_subset_1(C_446, k1_zfmisc_1(u1_struct_0(A_444))) | ~m1_subset_1(B_445, k1_zfmisc_1(u1_struct_0(A_444))) | ~l1_pre_topc(A_444))), inference(resolution, [status(thm)], [c_3690, c_8])).
% 7.67/2.62  tff(c_9542, plain, (![B_445]: (k3_xboole_0(k1_tops_1('#skF_3', B_445), k1_tops_1('#skF_3', '#skF_4'))=k1_tops_1('#skF_3', B_445) | ~r1_tarski(B_445, '#skF_4') | ~m1_subset_1(B_445, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_9531])).
% 7.67/2.62  tff(c_9729, plain, (![B_451]: (k1_tops_1('#skF_3', B_451)=k1_xboole_0 | ~r1_tarski(B_451, '#skF_4') | ~m1_subset_1(B_451, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2239, c_3324, c_9542])).
% 7.67/2.62  tff(c_9739, plain, (k1_tops_1('#skF_3', '#skF_5')=k1_xboole_0 | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_1995, c_9729])).
% 7.67/2.62  tff(c_9755, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1967, c_4240, c_9739])).
% 7.67/2.62  tff(c_9757, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1925, c_9755])).
% 7.67/2.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.67/2.62  
% 7.67/2.62  Inference rules
% 7.67/2.62  ----------------------
% 7.67/2.62  #Ref     : 0
% 7.67/2.62  #Sup     : 2429
% 7.67/2.62  #Fact    : 0
% 7.67/2.62  #Define  : 0
% 7.67/2.62  #Split   : 26
% 7.67/2.62  #Chain   : 0
% 7.67/2.62  #Close   : 0
% 7.67/2.62  
% 7.67/2.62  Ordering : KBO
% 7.67/2.62  
% 7.67/2.62  Simplification rules
% 7.67/2.62  ----------------------
% 7.67/2.62  #Subsume      : 822
% 7.67/2.62  #Demod        : 1020
% 7.67/2.62  #Tautology    : 876
% 7.67/2.62  #SimpNegUnit  : 43
% 7.67/2.62  #BackRed      : 19
% 7.67/2.62  
% 7.67/2.62  #Partial instantiations: 0
% 7.67/2.62  #Strategies tried      : 1
% 7.67/2.62  
% 7.67/2.62  Timing (in seconds)
% 7.67/2.62  ----------------------
% 7.67/2.63  Preprocessing        : 0.35
% 7.67/2.63  Parsing              : 0.19
% 7.67/2.63  CNF conversion       : 0.03
% 7.67/2.63  Main loop            : 1.49
% 7.67/2.63  Inferencing          : 0.47
% 7.67/2.63  Reduction            : 0.55
% 7.67/2.63  Demodulation         : 0.40
% 7.67/2.63  BG Simplification    : 0.05
% 7.67/2.63  Subsumption          : 0.31
% 7.67/2.63  Abstraction          : 0.06
% 7.67/2.63  MUC search           : 0.00
% 7.67/2.63  Cooper               : 0.00
% 7.67/2.63  Total                : 1.88
% 7.67/2.63  Index Insertion      : 0.00
% 7.67/2.63  Index Deletion       : 0.00
% 7.67/2.63  Index Matching       : 0.00
% 7.67/2.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
