%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:52 EST 2020

% Result     : Theorem 5.56s
% Output     : CNFRefutation 5.68s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 524 expanded)
%              Number of leaves         :   31 ( 189 expanded)
%              Depth                    :   17
%              Number of atoms          :  265 (1548 expanded)
%              Number of equality atoms :   19 ( 127 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_zfmisc_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_122,negated_conjecture,(
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

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_tarski(A,k3_zfmisc_1(A,B,C))
          & ~ r1_tarski(A,k3_zfmisc_1(B,C,A))
          & ~ r1_tarski(A,k3_zfmisc_1(C,A,B)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_mcart_1)).

tff(f_94,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B,C] :
          ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,k1_tops_1(A,C))
          <=> ? [D] :
                ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                & v3_pre_topc(D,A)
                & r1_tarski(D,C)
                & r2_hidden(B,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tops_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_48,plain,
    ( k1_xboole_0 != '#skF_5'
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_68,plain,(
    ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_203,plain,(
    ! [A_86,B_87] :
      ( r1_tarski(k1_tops_1(A_86,B_87),B_87)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_208,plain,
    ( r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_203])).

tff(c_212,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_208])).

tff(c_46,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_359,plain,(
    ! [A_97,B_98] :
      ( v3_pre_topc(k1_tops_1(A_97,B_98),A_97)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97)
      | ~ v2_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_364,plain,
    ( v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_359])).

tff(c_368,plain,(
    v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_364])).

tff(c_102,plain,(
    ! [A_63,B_64] :
      ( r2_hidden('#skF_1'(A_63,B_64),A_63)
      | r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_110,plain,(
    ! [A_63] : r1_tarski(A_63,A_63) ),
    inference(resolution,[status(thm)],[c_102,c_4])).

tff(c_71,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(A_50,B_51)
      | ~ m1_subset_1(A_50,k1_zfmisc_1(B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_79,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_42,c_71])).

tff(c_121,plain,(
    ! [A_68,C_69,B_70] :
      ( r1_tarski(A_68,C_69)
      | ~ r1_tarski(B_70,C_69)
      | ~ r1_tarski(A_68,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_142,plain,(
    ! [A_73] :
      ( r1_tarski(A_73,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_73,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_79,c_121])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(B_7,C_8)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_145,plain,(
    ! [A_6,A_73] :
      ( r1_tarski(A_6,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_6,A_73)
      | ~ r1_tarski(A_73,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_142,c_8])).

tff(c_214,plain,
    ( r1_tarski(k1_tops_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'))
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_212,c_145])).

tff(c_219,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_214])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_66,plain,(
    ! [C_44] :
      ( v2_tops_1('#skF_4','#skF_3')
      | k1_xboole_0 = C_44
      | ~ v3_pre_topc(C_44,'#skF_3')
      | ~ r1_tarski(C_44,'#skF_4')
      | ~ m1_subset_1(C_44,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_190,plain,(
    ! [C_85] :
      ( k1_xboole_0 = C_85
      | ~ v3_pre_topc(C_85,'#skF_3')
      | ~ r1_tarski(C_85,'#skF_4')
      | ~ m1_subset_1(C_85,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_66])).

tff(c_391,plain,(
    ! [A_102] :
      ( k1_xboole_0 = A_102
      | ~ v3_pre_topc(A_102,'#skF_3')
      | ~ r1_tarski(A_102,'#skF_4')
      | ~ r1_tarski(A_102,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_14,c_190])).

tff(c_402,plain,
    ( k1_tops_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_219,c_391])).

tff(c_421,plain,(
    k1_tops_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_368,c_402])).

tff(c_455,plain,(
    ! [B_104,A_105] :
      ( v2_tops_1(B_104,A_105)
      | k1_tops_1(A_105,B_104) != k1_xboole_0
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_462,plain,
    ( v2_tops_1('#skF_4','#skF_3')
    | k1_tops_1('#skF_3','#skF_4') != k1_xboole_0
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_455])).

tff(c_466,plain,(
    v2_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_421,c_462])).

tff(c_468,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_466])).

tff(c_469,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_470,plain,(
    v2_tops_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_50,plain,
    ( v3_pre_topc('#skF_5','#skF_3')
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_472,plain,(
    v3_pre_topc('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_50])).

tff(c_52,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_475,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_52])).

tff(c_54,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_509,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_54])).

tff(c_10,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_661,plain,(
    ! [A_149,B_150] :
      ( r1_tarski(k1_tops_1(A_149,B_150),B_150)
      | ~ m1_subset_1(B_150,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ l1_pre_topc(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_854,plain,(
    ! [A_160,A_161] :
      ( r1_tarski(k1_tops_1(A_160,A_161),A_161)
      | ~ l1_pre_topc(A_160)
      | ~ r1_tarski(A_161,u1_struct_0(A_160)) ) ),
    inference(resolution,[status(thm)],[c_14,c_661])).

tff(c_532,plain,(
    ! [A_128,C_129,B_130] :
      ( r1_tarski(A_128,C_129)
      | ~ r1_tarski(B_130,C_129)
      | ~ r1_tarski(A_128,B_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_547,plain,(
    ! [A_128,A_9] :
      ( r1_tarski(A_128,A_9)
      | ~ r1_tarski(A_128,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_532])).

tff(c_877,plain,(
    ! [A_160,A_9] :
      ( r1_tarski(k1_tops_1(A_160,k1_xboole_0),A_9)
      | ~ l1_pre_topc(A_160)
      | ~ r1_tarski(k1_xboole_0,u1_struct_0(A_160)) ) ),
    inference(resolution,[status(thm)],[c_854,c_547])).

tff(c_900,plain,(
    ! [A_162,A_163] :
      ( r1_tarski(k1_tops_1(A_162,k1_xboole_0),A_163)
      | ~ l1_pre_topc(A_162) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_877])).

tff(c_20,plain,(
    ! [A_14,B_15,C_16] :
      ( ~ r1_tarski(A_14,k3_zfmisc_1(B_15,C_16,A_14))
      | k1_xboole_0 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_959,plain,(
    ! [A_164] :
      ( k1_tops_1(A_164,k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_164) ) ),
    inference(resolution,[status(thm)],[c_900,c_20])).

tff(c_963,plain,(
    k1_tops_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_959])).

tff(c_1100,plain,(
    ! [B_174,A_175,C_176] :
      ( r2_hidden(B_174,'#skF_2'(A_175,B_174,C_176))
      | ~ r2_hidden(B_174,k1_tops_1(A_175,C_176))
      | ~ m1_subset_1(C_176,k1_zfmisc_1(u1_struct_0(A_175)))
      | ~ l1_pre_topc(A_175)
      | ~ v2_pre_topc(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1102,plain,(
    ! [B_174] :
      ( r2_hidden(B_174,'#skF_2'('#skF_3',B_174,k1_xboole_0))
      | ~ r2_hidden(B_174,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_963,c_1100])).

tff(c_1112,plain,(
    ! [B_174] :
      ( r2_hidden(B_174,'#skF_2'('#skF_3',B_174,k1_xboole_0))
      | ~ r2_hidden(B_174,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_1102])).

tff(c_1190,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1112])).

tff(c_1193,plain,(
    ~ r1_tarski(k1_xboole_0,u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_14,c_1190])).

tff(c_1197,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1193])).

tff(c_1199,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1112])).

tff(c_1152,plain,(
    ! [A_182,B_183,C_184] :
      ( r1_tarski('#skF_2'(A_182,B_183,C_184),C_184)
      | ~ r2_hidden(B_183,k1_tops_1(A_182,C_184))
      | ~ m1_subset_1(C_184,k1_zfmisc_1(u1_struct_0(A_182)))
      | ~ l1_pre_topc(A_182)
      | ~ v2_pre_topc(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1154,plain,(
    ! [B_183] :
      ( r1_tarski('#skF_2'('#skF_3',B_183,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(B_183,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_963,c_1152])).

tff(c_1164,plain,(
    ! [B_183] :
      ( r1_tarski('#skF_2'('#skF_3',B_183,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(B_183,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_1154])).

tff(c_1626,plain,(
    ! [B_220] :
      ( r1_tarski('#skF_2'('#skF_3',B_220,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(B_220,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1199,c_1164])).

tff(c_1652,plain,(
    ! [B_221,A_222] :
      ( r1_tarski('#skF_2'('#skF_3',B_221,k1_xboole_0),A_222)
      | ~ r2_hidden(B_221,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1626,c_547])).

tff(c_1239,plain,(
    ! [B_186] :
      ( r2_hidden(B_186,'#skF_2'('#skF_3',B_186,k1_xboole_0))
      | ~ r2_hidden(B_186,k1_xboole_0) ) ),
    inference(splitRight,[status(thm)],[c_1112])).

tff(c_16,plain,(
    ! [B_13,A_12] :
      ( ~ r1_tarski(B_13,A_12)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1246,plain,(
    ! [B_186] :
      ( ~ r1_tarski('#skF_2'('#skF_3',B_186,k1_xboole_0),B_186)
      | ~ r2_hidden(B_186,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1239,c_16])).

tff(c_1723,plain,(
    ! [A_222] : ~ r2_hidden(A_222,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1652,c_1246])).

tff(c_823,plain,(
    ! [A_158,B_159] :
      ( k1_tops_1(A_158,B_159) = k1_xboole_0
      | ~ v2_tops_1(B_159,A_158)
      | ~ m1_subset_1(B_159,k1_zfmisc_1(u1_struct_0(A_158)))
      | ~ l1_pre_topc(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_833,plain,
    ( k1_tops_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ v2_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_823])).

tff(c_840,plain,(
    k1_tops_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_470,c_833])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1533,plain,(
    ! [B_213,A_214,C_215,D_216] :
      ( r2_hidden(B_213,k1_tops_1(A_214,C_215))
      | ~ r2_hidden(B_213,D_216)
      | ~ r1_tarski(D_216,C_215)
      | ~ v3_pre_topc(D_216,A_214)
      | ~ m1_subset_1(D_216,k1_zfmisc_1(u1_struct_0(A_214)))
      | ~ m1_subset_1(C_215,k1_zfmisc_1(u1_struct_0(A_214)))
      | ~ l1_pre_topc(A_214)
      | ~ v2_pre_topc(A_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3042,plain,(
    ! [A_357,B_358,A_359,C_360] :
      ( r2_hidden('#skF_1'(A_357,B_358),k1_tops_1(A_359,C_360))
      | ~ r1_tarski(A_357,C_360)
      | ~ v3_pre_topc(A_357,A_359)
      | ~ m1_subset_1(A_357,k1_zfmisc_1(u1_struct_0(A_359)))
      | ~ m1_subset_1(C_360,k1_zfmisc_1(u1_struct_0(A_359)))
      | ~ l1_pre_topc(A_359)
      | ~ v2_pre_topc(A_359)
      | r1_tarski(A_357,B_358) ) ),
    inference(resolution,[status(thm)],[c_6,c_1533])).

tff(c_3063,plain,(
    ! [A_357,B_358] :
      ( r2_hidden('#skF_1'(A_357,B_358),k1_xboole_0)
      | ~ r1_tarski(A_357,'#skF_4')
      | ~ v3_pre_topc(A_357,'#skF_3')
      | ~ m1_subset_1(A_357,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | r1_tarski(A_357,B_358) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_840,c_3042])).

tff(c_3074,plain,(
    ! [A_357,B_358] :
      ( r2_hidden('#skF_1'(A_357,B_358),k1_xboole_0)
      | ~ r1_tarski(A_357,'#skF_4')
      | ~ v3_pre_topc(A_357,'#skF_3')
      | ~ m1_subset_1(A_357,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | r1_tarski(A_357,B_358) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_3063])).

tff(c_3076,plain,(
    ! [A_361,B_362] :
      ( ~ r1_tarski(A_361,'#skF_4')
      | ~ v3_pre_topc(A_361,'#skF_3')
      | ~ m1_subset_1(A_361,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | r1_tarski(A_361,B_362) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1723,c_3074])).

tff(c_3083,plain,(
    ! [B_362] :
      ( ~ r1_tarski('#skF_5','#skF_4')
      | ~ v3_pre_topc('#skF_5','#skF_3')
      | r1_tarski('#skF_5',B_362) ) ),
    inference(resolution,[status(thm)],[c_509,c_3076])).

tff(c_3097,plain,(
    ! [B_362] : r1_tarski('#skF_5',B_362) ),
    inference(demodulation,[status(thm),theory(equality)],[c_472,c_475,c_3083])).

tff(c_663,plain,
    ( r1_tarski(k1_tops_1('#skF_3','#skF_5'),'#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_509,c_661])).

tff(c_671,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_663])).

tff(c_548,plain,(
    ! [C_131,B_132,A_133] :
      ( r2_hidden(C_131,B_132)
      | ~ r2_hidden(C_131,A_133)
      | ~ r1_tarski(A_133,B_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_637,plain,(
    ! [A_143,B_144,B_145] :
      ( r2_hidden('#skF_1'(A_143,B_144),B_145)
      | ~ r1_tarski(A_143,B_145)
      | r1_tarski(A_143,B_144) ) ),
    inference(resolution,[status(thm)],[c_6,c_548])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1789,plain,(
    ! [A_232,B_233,B_234,B_235] :
      ( r2_hidden('#skF_1'(A_232,B_233),B_234)
      | ~ r1_tarski(B_235,B_234)
      | ~ r1_tarski(A_232,B_235)
      | r1_tarski(A_232,B_233) ) ),
    inference(resolution,[status(thm)],[c_637,c_2])).

tff(c_1904,plain,(
    ! [A_251,B_252] :
      ( r2_hidden('#skF_1'(A_251,B_252),'#skF_5')
      | ~ r1_tarski(A_251,k1_tops_1('#skF_3','#skF_5'))
      | r1_tarski(A_251,B_252) ) ),
    inference(resolution,[status(thm)],[c_671,c_1789])).

tff(c_2989,plain,(
    ! [A_352,B_353,B_354] :
      ( r2_hidden('#skF_1'(A_352,B_353),B_354)
      | ~ r1_tarski('#skF_5',B_354)
      | ~ r1_tarski(A_352,k1_tops_1('#skF_3','#skF_5'))
      | r1_tarski(A_352,B_353) ) ),
    inference(resolution,[status(thm)],[c_1904,c_2])).

tff(c_3011,plain,(
    ! [A_352,B_353] :
      ( ~ r1_tarski('#skF_5',k1_xboole_0)
      | ~ r1_tarski(A_352,k1_tops_1('#skF_3','#skF_5'))
      | r1_tarski(A_352,B_353) ) ),
    inference(resolution,[status(thm)],[c_2989,c_1723])).

tff(c_3041,plain,(
    ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_3011])).

tff(c_3126,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3097,c_3041])).

tff(c_3128,plain,(
    r1_tarski('#skF_5',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_3011])).

tff(c_3195,plain,(
    ! [A_367] : r1_tarski('#skF_5',A_367) ),
    inference(resolution,[status(thm)],[c_3128,c_547])).

tff(c_3262,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3195,c_20])).

tff(c_3306,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_469,c_3262])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:39:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.56/2.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.56/2.14  
% 5.56/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.56/2.14  %$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_zfmisc_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 5.56/2.14  
% 5.56/2.14  %Foreground sorts:
% 5.56/2.14  
% 5.56/2.14  
% 5.56/2.14  %Background operators:
% 5.56/2.14  
% 5.56/2.14  
% 5.56/2.14  %Foreground operators:
% 5.56/2.14  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.56/2.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.56/2.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.56/2.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.56/2.14  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 5.56/2.14  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.56/2.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.56/2.14  tff('#skF_5', type, '#skF_5': $i).
% 5.56/2.14  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.56/2.14  tff('#skF_3', type, '#skF_3': $i).
% 5.56/2.14  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.56/2.14  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 5.56/2.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.56/2.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.56/2.14  tff('#skF_4', type, '#skF_4': $i).
% 5.56/2.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.56/2.14  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.56/2.14  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.56/2.14  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.56/2.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.56/2.14  
% 5.68/2.16  tff(f_122, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tops_1)).
% 5.68/2.16  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 5.68/2.16  tff(f_69, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 5.68/2.16  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.68/2.16  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.68/2.16  tff(f_38, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.68/2.16  tff(f_103, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 5.68/2.16  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.68/2.16  tff(f_61, axiom, (![A, B, C]: (~((~r1_tarski(A, k3_zfmisc_1(A, B, C)) & ~r1_tarski(A, k3_zfmisc_1(B, C, A))) & ~r1_tarski(A, k3_zfmisc_1(C, A, B))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_mcart_1)).
% 5.68/2.16  tff(f_94, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B, C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k1_tops_1(A, C)) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_tops_1)).
% 5.68/2.16  tff(f_49, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.68/2.16  tff(c_48, plain, (k1_xboole_0!='#skF_5' | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.68/2.16  tff(c_68, plain, (~v2_tops_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_48])).
% 5.68/2.16  tff(c_44, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.68/2.16  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.68/2.16  tff(c_203, plain, (![A_86, B_87]: (r1_tarski(k1_tops_1(A_86, B_87), B_87) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.68/2.16  tff(c_208, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_42, c_203])).
% 5.68/2.16  tff(c_212, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_208])).
% 5.68/2.16  tff(c_46, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.68/2.16  tff(c_359, plain, (![A_97, B_98]: (v3_pre_topc(k1_tops_1(A_97, B_98), A_97) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97) | ~v2_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.68/2.16  tff(c_364, plain, (v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_42, c_359])).
% 5.68/2.16  tff(c_368, plain, (v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_364])).
% 5.68/2.16  tff(c_102, plain, (![A_63, B_64]: (r2_hidden('#skF_1'(A_63, B_64), A_63) | r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.68/2.16  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.68/2.16  tff(c_110, plain, (![A_63]: (r1_tarski(A_63, A_63))), inference(resolution, [status(thm)], [c_102, c_4])).
% 5.68/2.16  tff(c_71, plain, (![A_50, B_51]: (r1_tarski(A_50, B_51) | ~m1_subset_1(A_50, k1_zfmisc_1(B_51)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.68/2.16  tff(c_79, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_42, c_71])).
% 5.68/2.16  tff(c_121, plain, (![A_68, C_69, B_70]: (r1_tarski(A_68, C_69) | ~r1_tarski(B_70, C_69) | ~r1_tarski(A_68, B_70))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.68/2.16  tff(c_142, plain, (![A_73]: (r1_tarski(A_73, u1_struct_0('#skF_3')) | ~r1_tarski(A_73, '#skF_4'))), inference(resolution, [status(thm)], [c_79, c_121])).
% 5.68/2.16  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(B_7, C_8) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.68/2.16  tff(c_145, plain, (![A_6, A_73]: (r1_tarski(A_6, u1_struct_0('#skF_3')) | ~r1_tarski(A_6, A_73) | ~r1_tarski(A_73, '#skF_4'))), inference(resolution, [status(thm)], [c_142, c_8])).
% 5.68/2.16  tff(c_214, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3')) | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_212, c_145])).
% 5.68/2.16  tff(c_219, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_214])).
% 5.68/2.16  tff(c_14, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.68/2.16  tff(c_66, plain, (![C_44]: (v2_tops_1('#skF_4', '#skF_3') | k1_xboole_0=C_44 | ~v3_pre_topc(C_44, '#skF_3') | ~r1_tarski(C_44, '#skF_4') | ~m1_subset_1(C_44, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.68/2.16  tff(c_190, plain, (![C_85]: (k1_xboole_0=C_85 | ~v3_pre_topc(C_85, '#skF_3') | ~r1_tarski(C_85, '#skF_4') | ~m1_subset_1(C_85, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_68, c_66])).
% 5.68/2.16  tff(c_391, plain, (![A_102]: (k1_xboole_0=A_102 | ~v3_pre_topc(A_102, '#skF_3') | ~r1_tarski(A_102, '#skF_4') | ~r1_tarski(A_102, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_14, c_190])).
% 5.68/2.16  tff(c_402, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3') | ~r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_219, c_391])).
% 5.68/2.16  tff(c_421, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_212, c_368, c_402])).
% 5.68/2.16  tff(c_455, plain, (![B_104, A_105]: (v2_tops_1(B_104, A_105) | k1_tops_1(A_105, B_104)!=k1_xboole_0 | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.68/2.16  tff(c_462, plain, (v2_tops_1('#skF_4', '#skF_3') | k1_tops_1('#skF_3', '#skF_4')!=k1_xboole_0 | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_42, c_455])).
% 5.68/2.16  tff(c_466, plain, (v2_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_421, c_462])).
% 5.68/2.16  tff(c_468, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_466])).
% 5.68/2.16  tff(c_469, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_48])).
% 5.68/2.16  tff(c_470, plain, (v2_tops_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_48])).
% 5.68/2.16  tff(c_50, plain, (v3_pre_topc('#skF_5', '#skF_3') | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.68/2.16  tff(c_472, plain, (v3_pre_topc('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_470, c_50])).
% 5.68/2.16  tff(c_52, plain, (r1_tarski('#skF_5', '#skF_4') | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.68/2.16  tff(c_475, plain, (r1_tarski('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_470, c_52])).
% 5.68/2.16  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.68/2.16  tff(c_509, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_470, c_54])).
% 5.68/2.16  tff(c_10, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.68/2.16  tff(c_661, plain, (![A_149, B_150]: (r1_tarski(k1_tops_1(A_149, B_150), B_150) | ~m1_subset_1(B_150, k1_zfmisc_1(u1_struct_0(A_149))) | ~l1_pre_topc(A_149))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.68/2.16  tff(c_854, plain, (![A_160, A_161]: (r1_tarski(k1_tops_1(A_160, A_161), A_161) | ~l1_pre_topc(A_160) | ~r1_tarski(A_161, u1_struct_0(A_160)))), inference(resolution, [status(thm)], [c_14, c_661])).
% 5.68/2.16  tff(c_532, plain, (![A_128, C_129, B_130]: (r1_tarski(A_128, C_129) | ~r1_tarski(B_130, C_129) | ~r1_tarski(A_128, B_130))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.68/2.16  tff(c_547, plain, (![A_128, A_9]: (r1_tarski(A_128, A_9) | ~r1_tarski(A_128, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_532])).
% 5.68/2.16  tff(c_877, plain, (![A_160, A_9]: (r1_tarski(k1_tops_1(A_160, k1_xboole_0), A_9) | ~l1_pre_topc(A_160) | ~r1_tarski(k1_xboole_0, u1_struct_0(A_160)))), inference(resolution, [status(thm)], [c_854, c_547])).
% 5.68/2.16  tff(c_900, plain, (![A_162, A_163]: (r1_tarski(k1_tops_1(A_162, k1_xboole_0), A_163) | ~l1_pre_topc(A_162))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_877])).
% 5.68/2.16  tff(c_20, plain, (![A_14, B_15, C_16]: (~r1_tarski(A_14, k3_zfmisc_1(B_15, C_16, A_14)) | k1_xboole_0=A_14)), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.68/2.16  tff(c_959, plain, (![A_164]: (k1_tops_1(A_164, k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_164))), inference(resolution, [status(thm)], [c_900, c_20])).
% 5.68/2.16  tff(c_963, plain, (k1_tops_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_959])).
% 5.68/2.16  tff(c_1100, plain, (![B_174, A_175, C_176]: (r2_hidden(B_174, '#skF_2'(A_175, B_174, C_176)) | ~r2_hidden(B_174, k1_tops_1(A_175, C_176)) | ~m1_subset_1(C_176, k1_zfmisc_1(u1_struct_0(A_175))) | ~l1_pre_topc(A_175) | ~v2_pre_topc(A_175))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.68/2.16  tff(c_1102, plain, (![B_174]: (r2_hidden(B_174, '#skF_2'('#skF_3', B_174, k1_xboole_0)) | ~r2_hidden(B_174, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_963, c_1100])).
% 5.68/2.16  tff(c_1112, plain, (![B_174]: (r2_hidden(B_174, '#skF_2'('#skF_3', B_174, k1_xboole_0)) | ~r2_hidden(B_174, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_1102])).
% 5.68/2.16  tff(c_1190, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_1112])).
% 5.68/2.16  tff(c_1193, plain, (~r1_tarski(k1_xboole_0, u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_14, c_1190])).
% 5.68/2.16  tff(c_1197, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_1193])).
% 5.68/2.16  tff(c_1199, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_1112])).
% 5.68/2.16  tff(c_1152, plain, (![A_182, B_183, C_184]: (r1_tarski('#skF_2'(A_182, B_183, C_184), C_184) | ~r2_hidden(B_183, k1_tops_1(A_182, C_184)) | ~m1_subset_1(C_184, k1_zfmisc_1(u1_struct_0(A_182))) | ~l1_pre_topc(A_182) | ~v2_pre_topc(A_182))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.68/2.16  tff(c_1154, plain, (![B_183]: (r1_tarski('#skF_2'('#skF_3', B_183, k1_xboole_0), k1_xboole_0) | ~r2_hidden(B_183, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_963, c_1152])).
% 5.68/2.16  tff(c_1164, plain, (![B_183]: (r1_tarski('#skF_2'('#skF_3', B_183, k1_xboole_0), k1_xboole_0) | ~r2_hidden(B_183, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_1154])).
% 5.68/2.16  tff(c_1626, plain, (![B_220]: (r1_tarski('#skF_2'('#skF_3', B_220, k1_xboole_0), k1_xboole_0) | ~r2_hidden(B_220, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_1199, c_1164])).
% 5.68/2.16  tff(c_1652, plain, (![B_221, A_222]: (r1_tarski('#skF_2'('#skF_3', B_221, k1_xboole_0), A_222) | ~r2_hidden(B_221, k1_xboole_0))), inference(resolution, [status(thm)], [c_1626, c_547])).
% 5.68/2.16  tff(c_1239, plain, (![B_186]: (r2_hidden(B_186, '#skF_2'('#skF_3', B_186, k1_xboole_0)) | ~r2_hidden(B_186, k1_xboole_0))), inference(splitRight, [status(thm)], [c_1112])).
% 5.68/2.16  tff(c_16, plain, (![B_13, A_12]: (~r1_tarski(B_13, A_12) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.68/2.16  tff(c_1246, plain, (![B_186]: (~r1_tarski('#skF_2'('#skF_3', B_186, k1_xboole_0), B_186) | ~r2_hidden(B_186, k1_xboole_0))), inference(resolution, [status(thm)], [c_1239, c_16])).
% 5.68/2.16  tff(c_1723, plain, (![A_222]: (~r2_hidden(A_222, k1_xboole_0))), inference(resolution, [status(thm)], [c_1652, c_1246])).
% 5.68/2.16  tff(c_823, plain, (![A_158, B_159]: (k1_tops_1(A_158, B_159)=k1_xboole_0 | ~v2_tops_1(B_159, A_158) | ~m1_subset_1(B_159, k1_zfmisc_1(u1_struct_0(A_158))) | ~l1_pre_topc(A_158))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.68/2.16  tff(c_833, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0 | ~v2_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_42, c_823])).
% 5.68/2.16  tff(c_840, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_470, c_833])).
% 5.68/2.16  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.68/2.16  tff(c_1533, plain, (![B_213, A_214, C_215, D_216]: (r2_hidden(B_213, k1_tops_1(A_214, C_215)) | ~r2_hidden(B_213, D_216) | ~r1_tarski(D_216, C_215) | ~v3_pre_topc(D_216, A_214) | ~m1_subset_1(D_216, k1_zfmisc_1(u1_struct_0(A_214))) | ~m1_subset_1(C_215, k1_zfmisc_1(u1_struct_0(A_214))) | ~l1_pre_topc(A_214) | ~v2_pre_topc(A_214))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.68/2.16  tff(c_3042, plain, (![A_357, B_358, A_359, C_360]: (r2_hidden('#skF_1'(A_357, B_358), k1_tops_1(A_359, C_360)) | ~r1_tarski(A_357, C_360) | ~v3_pre_topc(A_357, A_359) | ~m1_subset_1(A_357, k1_zfmisc_1(u1_struct_0(A_359))) | ~m1_subset_1(C_360, k1_zfmisc_1(u1_struct_0(A_359))) | ~l1_pre_topc(A_359) | ~v2_pre_topc(A_359) | r1_tarski(A_357, B_358))), inference(resolution, [status(thm)], [c_6, c_1533])).
% 5.68/2.16  tff(c_3063, plain, (![A_357, B_358]: (r2_hidden('#skF_1'(A_357, B_358), k1_xboole_0) | ~r1_tarski(A_357, '#skF_4') | ~v3_pre_topc(A_357, '#skF_3') | ~m1_subset_1(A_357, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | r1_tarski(A_357, B_358))), inference(superposition, [status(thm), theory('equality')], [c_840, c_3042])).
% 5.68/2.16  tff(c_3074, plain, (![A_357, B_358]: (r2_hidden('#skF_1'(A_357, B_358), k1_xboole_0) | ~r1_tarski(A_357, '#skF_4') | ~v3_pre_topc(A_357, '#skF_3') | ~m1_subset_1(A_357, k1_zfmisc_1(u1_struct_0('#skF_3'))) | r1_tarski(A_357, B_358))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_3063])).
% 5.68/2.16  tff(c_3076, plain, (![A_361, B_362]: (~r1_tarski(A_361, '#skF_4') | ~v3_pre_topc(A_361, '#skF_3') | ~m1_subset_1(A_361, k1_zfmisc_1(u1_struct_0('#skF_3'))) | r1_tarski(A_361, B_362))), inference(negUnitSimplification, [status(thm)], [c_1723, c_3074])).
% 5.68/2.16  tff(c_3083, plain, (![B_362]: (~r1_tarski('#skF_5', '#skF_4') | ~v3_pre_topc('#skF_5', '#skF_3') | r1_tarski('#skF_5', B_362))), inference(resolution, [status(thm)], [c_509, c_3076])).
% 5.68/2.16  tff(c_3097, plain, (![B_362]: (r1_tarski('#skF_5', B_362))), inference(demodulation, [status(thm), theory('equality')], [c_472, c_475, c_3083])).
% 5.68/2.16  tff(c_663, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_5'), '#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_509, c_661])).
% 5.68/2.16  tff(c_671, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_663])).
% 5.68/2.16  tff(c_548, plain, (![C_131, B_132, A_133]: (r2_hidden(C_131, B_132) | ~r2_hidden(C_131, A_133) | ~r1_tarski(A_133, B_132))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.68/2.16  tff(c_637, plain, (![A_143, B_144, B_145]: (r2_hidden('#skF_1'(A_143, B_144), B_145) | ~r1_tarski(A_143, B_145) | r1_tarski(A_143, B_144))), inference(resolution, [status(thm)], [c_6, c_548])).
% 5.68/2.16  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.68/2.16  tff(c_1789, plain, (![A_232, B_233, B_234, B_235]: (r2_hidden('#skF_1'(A_232, B_233), B_234) | ~r1_tarski(B_235, B_234) | ~r1_tarski(A_232, B_235) | r1_tarski(A_232, B_233))), inference(resolution, [status(thm)], [c_637, c_2])).
% 5.68/2.16  tff(c_1904, plain, (![A_251, B_252]: (r2_hidden('#skF_1'(A_251, B_252), '#skF_5') | ~r1_tarski(A_251, k1_tops_1('#skF_3', '#skF_5')) | r1_tarski(A_251, B_252))), inference(resolution, [status(thm)], [c_671, c_1789])).
% 5.68/2.16  tff(c_2989, plain, (![A_352, B_353, B_354]: (r2_hidden('#skF_1'(A_352, B_353), B_354) | ~r1_tarski('#skF_5', B_354) | ~r1_tarski(A_352, k1_tops_1('#skF_3', '#skF_5')) | r1_tarski(A_352, B_353))), inference(resolution, [status(thm)], [c_1904, c_2])).
% 5.68/2.16  tff(c_3011, plain, (![A_352, B_353]: (~r1_tarski('#skF_5', k1_xboole_0) | ~r1_tarski(A_352, k1_tops_1('#skF_3', '#skF_5')) | r1_tarski(A_352, B_353))), inference(resolution, [status(thm)], [c_2989, c_1723])).
% 5.68/2.16  tff(c_3041, plain, (~r1_tarski('#skF_5', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_3011])).
% 5.68/2.16  tff(c_3126, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3097, c_3041])).
% 5.68/2.16  tff(c_3128, plain, (r1_tarski('#skF_5', k1_xboole_0)), inference(splitRight, [status(thm)], [c_3011])).
% 5.68/2.16  tff(c_3195, plain, (![A_367]: (r1_tarski('#skF_5', A_367))), inference(resolution, [status(thm)], [c_3128, c_547])).
% 5.68/2.16  tff(c_3262, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_3195, c_20])).
% 5.68/2.16  tff(c_3306, plain, $false, inference(negUnitSimplification, [status(thm)], [c_469, c_3262])).
% 5.68/2.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.68/2.16  
% 5.68/2.16  Inference rules
% 5.68/2.16  ----------------------
% 5.68/2.16  #Ref     : 0
% 5.68/2.16  #Sup     : 695
% 5.68/2.16  #Fact    : 0
% 5.68/2.16  #Define  : 0
% 5.68/2.16  #Split   : 17
% 5.68/2.16  #Chain   : 0
% 5.68/2.16  #Close   : 0
% 5.68/2.16  
% 5.68/2.16  Ordering : KBO
% 5.68/2.16  
% 5.68/2.16  Simplification rules
% 5.68/2.16  ----------------------
% 5.68/2.16  #Subsume      : 235
% 5.68/2.16  #Demod        : 388
% 5.68/2.16  #Tautology    : 171
% 5.68/2.16  #SimpNegUnit  : 13
% 5.68/2.16  #BackRed      : 25
% 5.68/2.16  
% 5.68/2.16  #Partial instantiations: 0
% 5.68/2.16  #Strategies tried      : 1
% 5.68/2.16  
% 5.68/2.16  Timing (in seconds)
% 5.68/2.16  ----------------------
% 5.68/2.17  Preprocessing        : 0.35
% 5.68/2.17  Parsing              : 0.19
% 5.68/2.17  CNF conversion       : 0.03
% 5.68/2.17  Main loop            : 0.98
% 5.68/2.17  Inferencing          : 0.32
% 5.68/2.17  Reduction            : 0.29
% 5.68/2.17  Demodulation         : 0.20
% 5.68/2.17  BG Simplification    : 0.03
% 5.68/2.17  Subsumption          : 0.26
% 5.68/2.17  Abstraction          : 0.03
% 5.68/2.17  MUC search           : 0.00
% 5.68/2.17  Cooper               : 0.00
% 5.68/2.17  Total                : 1.39
% 5.68/2.17  Index Insertion      : 0.00
% 5.68/2.17  Index Deletion       : 0.00
% 5.68/2.17  Index Matching       : 0.00
% 5.68/2.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
