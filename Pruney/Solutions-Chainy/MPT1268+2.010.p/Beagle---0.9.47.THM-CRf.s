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
% DateTime   : Thu Dec  3 10:21:47 EST 2020

% Result     : Theorem 7.25s
% Output     : CNFRefutation 7.59s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 155 expanded)
%              Number of leaves         :   33 (  66 expanded)
%              Depth                    :    8
%              Number of atoms          :  171 ( 467 expanded)
%              Number of equality atoms :   35 (  77 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_tarski > k3_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_154,negated_conjecture,(
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

tff(f_135,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_93,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_51,axiom,(
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

tff(f_126,axiom,(
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

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(c_50,plain,
    ( k1_xboole_0 != '#skF_4'
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_71,plain,(
    ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1403,plain,(
    ! [B_171,A_172] :
      ( v2_tops_1(B_171,A_172)
      | k1_tops_1(A_172,B_171) != k1_xboole_0
      | ~ m1_subset_1(B_171,k1_zfmisc_1(u1_struct_0(A_172)))
      | ~ l1_pre_topc(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1414,plain,
    ( v2_tops_1('#skF_3','#skF_2')
    | k1_tops_1('#skF_2','#skF_3') != k1_xboole_0
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_1403])).

tff(c_1423,plain,
    ( v2_tops_1('#skF_3','#skF_2')
    | k1_tops_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1414])).

tff(c_1424,plain,(
    k1_tops_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_1423])).

tff(c_1138,plain,(
    ! [A_161,B_162] :
      ( r1_tarski(k1_tops_1(A_161,B_162),B_162)
      | ~ m1_subset_1(B_162,k1_zfmisc_1(u1_struct_0(A_161)))
      | ~ l1_pre_topc(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1146,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_1138])).

tff(c_1154,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1146])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1941,plain,(
    ! [A_188,B_189] :
      ( v3_pre_topc(k1_tops_1(A_188,B_189),A_188)
      | ~ m1_subset_1(B_189,k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ l1_pre_topc(A_188)
      | ~ v2_pre_topc(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1949,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_1941])).

tff(c_1957,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1949])).

tff(c_118,plain,(
    ! [A_78,B_79] :
      ( r1_tarski(A_78,B_79)
      | ~ m1_subset_1(A_78,k1_zfmisc_1(B_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_125,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_118])).

tff(c_270,plain,(
    ! [A_95,C_96,B_97] :
      ( r1_tarski(A_95,C_96)
      | ~ r1_tarski(B_97,C_96)
      | ~ r1_tarski(A_95,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_281,plain,(
    ! [A_95] :
      ( r1_tarski(A_95,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_95,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_125,c_270])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_68,plain,(
    ! [C_69] :
      ( v2_tops_1('#skF_3','#skF_2')
      | k1_xboole_0 = C_69
      | ~ v3_pre_topc(C_69,'#skF_2')
      | ~ r1_tarski(C_69,'#skF_3')
      | ~ m1_subset_1(C_69,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_914,plain,(
    ! [C_152] :
      ( k1_xboole_0 = C_152
      | ~ v3_pre_topc(C_152,'#skF_2')
      | ~ r1_tarski(C_152,'#skF_3')
      | ~ m1_subset_1(C_152,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_68])).

tff(c_1315,plain,(
    ! [A_168] :
      ( k1_xboole_0 = A_168
      | ~ v3_pre_topc(A_168,'#skF_2')
      | ~ r1_tarski(A_168,'#skF_3')
      | ~ r1_tarski(A_168,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_18,c_914])).

tff(c_1349,plain,(
    ! [A_95] :
      ( k1_xboole_0 = A_95
      | ~ v3_pre_topc(A_95,'#skF_2')
      | ~ r1_tarski(A_95,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_281,c_1315])).

tff(c_1961,plain,
    ( k1_tops_1('#skF_2','#skF_3') = k1_xboole_0
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1957,c_1349])).

tff(c_1964,plain,(
    k1_tops_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1154,c_1961])).

tff(c_1966,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1424,c_1964])).

tff(c_1967,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1968,plain,(
    v2_tops_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_54,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1978,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1968,c_54])).

tff(c_52,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1971,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1968,c_52])).

tff(c_56,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_2035,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1968,c_56])).

tff(c_38,plain,(
    ! [B_52,D_58,C_56,A_44] :
      ( k1_tops_1(B_52,D_58) = D_58
      | ~ v3_pre_topc(D_58,B_52)
      | ~ m1_subset_1(D_58,k1_zfmisc_1(u1_struct_0(B_52)))
      | ~ m1_subset_1(C_56,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(B_52)
      | ~ l1_pre_topc(A_44)
      | ~ v2_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_4500,plain,(
    ! [C_319,A_320] :
      ( ~ m1_subset_1(C_319,k1_zfmisc_1(u1_struct_0(A_320)))
      | ~ l1_pre_topc(A_320)
      | ~ v2_pre_topc(A_320) ) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_4503,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2035,c_4500])).

tff(c_4517,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_4503])).

tff(c_4600,plain,(
    ! [B_323,D_324] :
      ( k1_tops_1(B_323,D_324) = D_324
      | ~ v3_pre_topc(D_324,B_323)
      | ~ m1_subset_1(D_324,k1_zfmisc_1(u1_struct_0(B_323)))
      | ~ l1_pre_topc(B_323) ) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_4603,plain,
    ( k1_tops_1('#skF_2','#skF_4') = '#skF_4'
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2035,c_4600])).

tff(c_4617,plain,(
    k1_tops_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1971,c_4603])).

tff(c_10,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2049,plain,(
    ! [A_202,B_203] :
      ( k3_xboole_0(A_202,B_203) = A_202
      | ~ r1_tarski(A_202,B_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2070,plain,(
    ! [A_204] : k3_xboole_0(k1_xboole_0,A_204) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_2049])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2075,plain,(
    ! [A_204] : k3_xboole_0(A_204,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2070,c_2])).

tff(c_4184,plain,(
    ! [A_308,B_309] :
      ( k1_tops_1(A_308,B_309) = k1_xboole_0
      | ~ v2_tops_1(B_309,A_308)
      | ~ m1_subset_1(B_309,k1_zfmisc_1(u1_struct_0(A_308)))
      | ~ l1_pre_topc(A_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_4194,plain,
    ( k1_tops_1('#skF_2','#skF_3') = k1_xboole_0
    | ~ v2_tops_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_4184])).

tff(c_4206,plain,(
    k1_tops_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1968,c_4194])).

tff(c_4262,plain,(
    ! [A_311,B_312,C_313] :
      ( r1_tarski(k1_tops_1(A_311,B_312),k1_tops_1(A_311,C_313))
      | ~ r1_tarski(B_312,C_313)
      | ~ m1_subset_1(C_313,k1_zfmisc_1(u1_struct_0(A_311)))
      | ~ m1_subset_1(B_312,k1_zfmisc_1(u1_struct_0(A_311)))
      | ~ l1_pre_topc(A_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_8,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10393,plain,(
    ! [A_462,B_463,C_464] :
      ( k3_xboole_0(k1_tops_1(A_462,B_463),k1_tops_1(A_462,C_464)) = k1_tops_1(A_462,B_463)
      | ~ r1_tarski(B_463,C_464)
      | ~ m1_subset_1(C_464,k1_zfmisc_1(u1_struct_0(A_462)))
      | ~ m1_subset_1(B_463,k1_zfmisc_1(u1_struct_0(A_462)))
      | ~ l1_pre_topc(A_462) ) ),
    inference(resolution,[status(thm)],[c_4262,c_8])).

tff(c_10403,plain,(
    ! [B_463] :
      ( k3_xboole_0(k1_tops_1('#skF_2',B_463),k1_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2',B_463)
      | ~ r1_tarski(B_463,'#skF_3')
      | ~ m1_subset_1(B_463,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_44,c_10393])).

tff(c_10601,plain,(
    ! [B_467] :
      ( k1_tops_1('#skF_2',B_467) = k1_xboole_0
      | ~ r1_tarski(B_467,'#skF_3')
      | ~ m1_subset_1(B_467,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2075,c_4206,c_10403])).

tff(c_10608,plain,
    ( k1_tops_1('#skF_2','#skF_4') = k1_xboole_0
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_2035,c_10601])).

tff(c_10623,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1978,c_4617,c_10608])).

tff(c_10625,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1967,c_10623])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:39:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.25/2.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.59/2.56  
% 7.59/2.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.59/2.56  %$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_tarski > k3_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 7.59/2.56  
% 7.59/2.56  %Foreground sorts:
% 7.59/2.56  
% 7.59/2.56  
% 7.59/2.56  %Background operators:
% 7.59/2.56  
% 7.59/2.56  
% 7.59/2.56  %Foreground operators:
% 7.59/2.56  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 7.59/2.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.59/2.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.59/2.56  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.59/2.56  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.59/2.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.59/2.56  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 7.59/2.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.59/2.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.59/2.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.59/2.56  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 7.59/2.56  tff('#skF_2', type, '#skF_2': $i).
% 7.59/2.56  tff('#skF_3', type, '#skF_3': $i).
% 7.59/2.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.59/2.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.59/2.56  tff('#skF_4', type, '#skF_4': $i).
% 7.59/2.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.59/2.56  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.59/2.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.59/2.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.59/2.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.59/2.56  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.59/2.56  
% 7.59/2.57  tff(f_154, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tops_1)).
% 7.59/2.57  tff(f_135, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 7.59/2.57  tff(f_93, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 7.59/2.57  tff(f_86, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 7.59/2.57  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.59/2.57  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 7.59/2.57  tff(f_126, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 7.59/2.57  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.59/2.57  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.59/2.57  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.59/2.57  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 7.59/2.57  tff(c_50, plain, (k1_xboole_0!='#skF_4' | ~v2_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 7.59/2.57  tff(c_71, plain, (~v2_tops_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_50])).
% 7.59/2.57  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 7.59/2.57  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 7.59/2.57  tff(c_1403, plain, (![B_171, A_172]: (v2_tops_1(B_171, A_172) | k1_tops_1(A_172, B_171)!=k1_xboole_0 | ~m1_subset_1(B_171, k1_zfmisc_1(u1_struct_0(A_172))) | ~l1_pre_topc(A_172))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.59/2.57  tff(c_1414, plain, (v2_tops_1('#skF_3', '#skF_2') | k1_tops_1('#skF_2', '#skF_3')!=k1_xboole_0 | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_1403])).
% 7.59/2.57  tff(c_1423, plain, (v2_tops_1('#skF_3', '#skF_2') | k1_tops_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1414])).
% 7.59/2.57  tff(c_1424, plain, (k1_tops_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_71, c_1423])).
% 7.59/2.57  tff(c_1138, plain, (![A_161, B_162]: (r1_tarski(k1_tops_1(A_161, B_162), B_162) | ~m1_subset_1(B_162, k1_zfmisc_1(u1_struct_0(A_161))) | ~l1_pre_topc(A_161))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.59/2.57  tff(c_1146, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_1138])).
% 7.59/2.57  tff(c_1154, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1146])).
% 7.59/2.57  tff(c_48, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 7.59/2.57  tff(c_1941, plain, (![A_188, B_189]: (v3_pre_topc(k1_tops_1(A_188, B_189), A_188) | ~m1_subset_1(B_189, k1_zfmisc_1(u1_struct_0(A_188))) | ~l1_pre_topc(A_188) | ~v2_pre_topc(A_188))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.59/2.57  tff(c_1949, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_1941])).
% 7.59/2.57  tff(c_1957, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1949])).
% 7.59/2.57  tff(c_118, plain, (![A_78, B_79]: (r1_tarski(A_78, B_79) | ~m1_subset_1(A_78, k1_zfmisc_1(B_79)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.59/2.57  tff(c_125, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_118])).
% 7.59/2.57  tff(c_270, plain, (![A_95, C_96, B_97]: (r1_tarski(A_95, C_96) | ~r1_tarski(B_97, C_96) | ~r1_tarski(A_95, B_97))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.59/2.58  tff(c_281, plain, (![A_95]: (r1_tarski(A_95, u1_struct_0('#skF_2')) | ~r1_tarski(A_95, '#skF_3'))), inference(resolution, [status(thm)], [c_125, c_270])).
% 7.59/2.58  tff(c_18, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.59/2.58  tff(c_68, plain, (![C_69]: (v2_tops_1('#skF_3', '#skF_2') | k1_xboole_0=C_69 | ~v3_pre_topc(C_69, '#skF_2') | ~r1_tarski(C_69, '#skF_3') | ~m1_subset_1(C_69, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_154])).
% 7.59/2.58  tff(c_914, plain, (![C_152]: (k1_xboole_0=C_152 | ~v3_pre_topc(C_152, '#skF_2') | ~r1_tarski(C_152, '#skF_3') | ~m1_subset_1(C_152, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_71, c_68])).
% 7.59/2.58  tff(c_1315, plain, (![A_168]: (k1_xboole_0=A_168 | ~v3_pre_topc(A_168, '#skF_2') | ~r1_tarski(A_168, '#skF_3') | ~r1_tarski(A_168, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_18, c_914])).
% 7.59/2.58  tff(c_1349, plain, (![A_95]: (k1_xboole_0=A_95 | ~v3_pre_topc(A_95, '#skF_2') | ~r1_tarski(A_95, '#skF_3'))), inference(resolution, [status(thm)], [c_281, c_1315])).
% 7.59/2.58  tff(c_1961, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0 | ~r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_1957, c_1349])).
% 7.59/2.58  tff(c_1964, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1154, c_1961])).
% 7.59/2.58  tff(c_1966, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1424, c_1964])).
% 7.59/2.58  tff(c_1967, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_50])).
% 7.59/2.58  tff(c_1968, plain, (v2_tops_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 7.59/2.58  tff(c_54, plain, (r1_tarski('#skF_4', '#skF_3') | ~v2_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 7.59/2.58  tff(c_1978, plain, (r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1968, c_54])).
% 7.59/2.58  tff(c_52, plain, (v3_pre_topc('#skF_4', '#skF_2') | ~v2_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 7.59/2.58  tff(c_1971, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1968, c_52])).
% 7.59/2.58  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v2_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 7.59/2.58  tff(c_2035, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1968, c_56])).
% 7.59/2.58  tff(c_38, plain, (![B_52, D_58, C_56, A_44]: (k1_tops_1(B_52, D_58)=D_58 | ~v3_pre_topc(D_58, B_52) | ~m1_subset_1(D_58, k1_zfmisc_1(u1_struct_0(B_52))) | ~m1_subset_1(C_56, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(B_52) | ~l1_pre_topc(A_44) | ~v2_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_126])).
% 7.59/2.58  tff(c_4500, plain, (![C_319, A_320]: (~m1_subset_1(C_319, k1_zfmisc_1(u1_struct_0(A_320))) | ~l1_pre_topc(A_320) | ~v2_pre_topc(A_320))), inference(splitLeft, [status(thm)], [c_38])).
% 7.59/2.58  tff(c_4503, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2035, c_4500])).
% 7.59/2.58  tff(c_4517, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_4503])).
% 7.59/2.58  tff(c_4600, plain, (![B_323, D_324]: (k1_tops_1(B_323, D_324)=D_324 | ~v3_pre_topc(D_324, B_323) | ~m1_subset_1(D_324, k1_zfmisc_1(u1_struct_0(B_323))) | ~l1_pre_topc(B_323))), inference(splitRight, [status(thm)], [c_38])).
% 7.59/2.58  tff(c_4603, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4' | ~v3_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2035, c_4600])).
% 7.59/2.58  tff(c_4617, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1971, c_4603])).
% 7.59/2.58  tff(c_10, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.59/2.58  tff(c_2049, plain, (![A_202, B_203]: (k3_xboole_0(A_202, B_203)=A_202 | ~r1_tarski(A_202, B_203))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.59/2.58  tff(c_2070, plain, (![A_204]: (k3_xboole_0(k1_xboole_0, A_204)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_2049])).
% 7.59/2.58  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.59/2.58  tff(c_2075, plain, (![A_204]: (k3_xboole_0(A_204, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2070, c_2])).
% 7.59/2.58  tff(c_4184, plain, (![A_308, B_309]: (k1_tops_1(A_308, B_309)=k1_xboole_0 | ~v2_tops_1(B_309, A_308) | ~m1_subset_1(B_309, k1_zfmisc_1(u1_struct_0(A_308))) | ~l1_pre_topc(A_308))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.59/2.58  tff(c_4194, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0 | ~v2_tops_1('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_4184])).
% 7.59/2.58  tff(c_4206, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1968, c_4194])).
% 7.59/2.58  tff(c_4262, plain, (![A_311, B_312, C_313]: (r1_tarski(k1_tops_1(A_311, B_312), k1_tops_1(A_311, C_313)) | ~r1_tarski(B_312, C_313) | ~m1_subset_1(C_313, k1_zfmisc_1(u1_struct_0(A_311))) | ~m1_subset_1(B_312, k1_zfmisc_1(u1_struct_0(A_311))) | ~l1_pre_topc(A_311))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.59/2.58  tff(c_8, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.59/2.58  tff(c_10393, plain, (![A_462, B_463, C_464]: (k3_xboole_0(k1_tops_1(A_462, B_463), k1_tops_1(A_462, C_464))=k1_tops_1(A_462, B_463) | ~r1_tarski(B_463, C_464) | ~m1_subset_1(C_464, k1_zfmisc_1(u1_struct_0(A_462))) | ~m1_subset_1(B_463, k1_zfmisc_1(u1_struct_0(A_462))) | ~l1_pre_topc(A_462))), inference(resolution, [status(thm)], [c_4262, c_8])).
% 7.59/2.58  tff(c_10403, plain, (![B_463]: (k3_xboole_0(k1_tops_1('#skF_2', B_463), k1_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', B_463) | ~r1_tarski(B_463, '#skF_3') | ~m1_subset_1(B_463, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_10393])).
% 7.59/2.58  tff(c_10601, plain, (![B_467]: (k1_tops_1('#skF_2', B_467)=k1_xboole_0 | ~r1_tarski(B_467, '#skF_3') | ~m1_subset_1(B_467, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2075, c_4206, c_10403])).
% 7.59/2.58  tff(c_10608, plain, (k1_tops_1('#skF_2', '#skF_4')=k1_xboole_0 | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_2035, c_10601])).
% 7.59/2.58  tff(c_10623, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1978, c_4617, c_10608])).
% 7.59/2.58  tff(c_10625, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1967, c_10623])).
% 7.59/2.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.59/2.58  
% 7.59/2.58  Inference rules
% 7.59/2.58  ----------------------
% 7.59/2.58  #Ref     : 0
% 7.59/2.58  #Sup     : 2602
% 7.59/2.58  #Fact    : 0
% 7.59/2.58  #Define  : 0
% 7.59/2.58  #Split   : 25
% 7.59/2.58  #Chain   : 0
% 7.59/2.58  #Close   : 0
% 7.59/2.58  
% 7.59/2.58  Ordering : KBO
% 7.59/2.58  
% 7.59/2.58  Simplification rules
% 7.59/2.58  ----------------------
% 7.59/2.58  #Subsume      : 991
% 7.59/2.58  #Demod        : 1181
% 7.59/2.58  #Tautology    : 873
% 7.59/2.58  #SimpNegUnit  : 46
% 7.59/2.58  #BackRed      : 32
% 7.59/2.58  
% 7.59/2.58  #Partial instantiations: 0
% 7.59/2.58  #Strategies tried      : 1
% 7.59/2.58  
% 7.59/2.58  Timing (in seconds)
% 7.59/2.58  ----------------------
% 7.59/2.58  Preprocessing        : 0.34
% 7.59/2.58  Parsing              : 0.18
% 7.59/2.58  CNF conversion       : 0.02
% 7.59/2.58  Main loop            : 1.46
% 7.59/2.58  Inferencing          : 0.45
% 7.59/2.58  Reduction            : 0.52
% 7.59/2.58  Demodulation         : 0.37
% 7.59/2.58  BG Simplification    : 0.05
% 7.59/2.58  Subsumption          : 0.34
% 7.59/2.58  Abstraction          : 0.06
% 7.59/2.58  MUC search           : 0.00
% 7.59/2.58  Cooper               : 0.00
% 7.59/2.58  Total                : 1.84
% 7.59/2.58  Index Insertion      : 0.00
% 7.59/2.58  Index Deletion       : 0.00
% 7.59/2.58  Index Matching       : 0.00
% 7.59/2.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
