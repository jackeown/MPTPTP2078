%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:53 EST 2020

% Result     : Theorem 10.61s
% Output     : CNFRefutation 10.61s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 404 expanded)
%              Number of leaves         :   45 ( 171 expanded)
%              Depth                    :   14
%              Number of atoms          :  317 (1757 expanded)
%              Number of equality atoms :    5 (  11 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k7_tmap_1 > k6_tmap_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k7_tmap_1,type,(
    k7_tmap_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(k6_tmap_1,type,(
    k6_tmap_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_229,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ( r1_xboole_0(u1_struct_0(C),B)
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(C))
                     => r1_tmap_1(C,k6_tmap_1(A,B),k2_tmap_1(A,k6_tmap_1(A,B),k7_tmap_1(A,B),C),D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_tmap_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_84,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => m1_subset_1(C,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_165,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ~ r2_hidden(C,B)
               => r1_tmap_1(A,k6_tmap_1(A,B),k7_tmap_1(A,B),C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_tmap_1)).

tff(f_131,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_funct_1(k7_tmap_1(A,B))
        & v1_funct_2(k7_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B)))
        & m1_subset_1(k7_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B))))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).

tff(f_147,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( ~ v2_struct_0(k6_tmap_1(A,B))
        & v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_tmap_1)).

tff(f_116,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_205,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,B) )
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(D))
                         => ( ( E = F
                              & r1_tmap_1(B,A,C,E) )
                           => r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),F) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).

tff(f_101,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v3_pre_topc(B,A)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_tops_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_78,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_76,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_70,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_134,plain,(
    ! [B_134,A_135] :
      ( v2_pre_topc(B_134)
      | ~ m1_pre_topc(B_134,A_135)
      | ~ l1_pre_topc(A_135)
      | ~ v2_pre_topc(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_137,plain,
    ( v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_134])).

tff(c_140,plain,(
    v2_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_137])).

tff(c_90,plain,(
    ! [B_118,A_119] :
      ( l1_pre_topc(B_118)
      | ~ m1_pre_topc(B_118,A_119)
      | ~ l1_pre_topc(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_93,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_90])).

tff(c_96,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_93])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_66,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_533,plain,(
    ! [C_196,A_197,B_198] :
      ( m1_subset_1(C_196,u1_struct_0(A_197))
      | ~ m1_subset_1(C_196,u1_struct_0(B_198))
      | ~ m1_pre_topc(B_198,A_197)
      | v2_struct_0(B_198)
      | ~ l1_pre_topc(A_197)
      | v2_struct_0(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_535,plain,(
    ! [A_197] :
      ( m1_subset_1('#skF_7',u1_struct_0(A_197))
      | ~ m1_pre_topc('#skF_6',A_197)
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc(A_197)
      | v2_struct_0(A_197) ) ),
    inference(resolution,[status(thm)],[c_66,c_533])).

tff(c_538,plain,(
    ! [A_197] :
      ( m1_subset_1('#skF_7',u1_struct_0(A_197))
      | ~ m1_pre_topc('#skF_6',A_197)
      | ~ l1_pre_topc(A_197)
      | v2_struct_0(A_197) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_535])).

tff(c_111,plain,(
    ! [A_129,B_130] :
      ( r2_hidden(A_129,B_130)
      | v1_xboole_0(B_130)
      | ~ m1_subset_1(A_129,B_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_68,plain,(
    r1_xboole_0(u1_struct_0('#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_81,plain,(
    ! [A_116,B_117] :
      ( k4_xboole_0(A_116,B_117) = A_116
      | ~ r1_xboole_0(A_116,B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_85,plain,(
    k4_xboole_0(u1_struct_0('#skF_6'),'#skF_5') = u1_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_81])).

tff(c_106,plain,(
    ! [D_125,B_126,A_127] :
      ( ~ r2_hidden(D_125,B_126)
      | ~ r2_hidden(D_125,k4_xboole_0(A_127,B_126)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_109,plain,(
    ! [D_125] :
      ( ~ r2_hidden(D_125,'#skF_5')
      | ~ r2_hidden(D_125,u1_struct_0('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_106])).

tff(c_124,plain,(
    ! [A_129] :
      ( ~ r2_hidden(A_129,'#skF_5')
      | v1_xboole_0(u1_struct_0('#skF_6'))
      | ~ m1_subset_1(A_129,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_111,c_109])).

tff(c_144,plain,(
    ! [A_138] :
      ( ~ r2_hidden(A_138,'#skF_5')
      | ~ m1_subset_1(A_138,u1_struct_0('#skF_6')) ) ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_148,plain,(
    ~ r2_hidden('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_144])).

tff(c_74,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_60,plain,(
    ! [A_35,B_39,C_41] :
      ( r1_tmap_1(A_35,k6_tmap_1(A_35,B_39),k7_tmap_1(A_35,B_39),C_41)
      | r2_hidden(C_41,B_39)
      | ~ m1_subset_1(C_41,u1_struct_0(A_35))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_50,plain,(
    ! [A_31,B_32] :
      ( v1_funct_2(k7_tmap_1(A_31,B_32),u1_struct_0(A_31),u1_struct_0(k6_tmap_1(A_31,B_32)))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31)
      | ~ v2_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_181,plain,(
    ! [A_149,B_150] :
      ( ~ v2_struct_0(k6_tmap_1(A_149,B_150))
      | ~ m1_subset_1(B_150,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ l1_pre_topc(A_149)
      | ~ v2_pre_topc(A_149)
      | v2_struct_0(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_187,plain,
    ( ~ v2_struct_0(k6_tmap_1('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_181])).

tff(c_191,plain,
    ( ~ v2_struct_0(k6_tmap_1('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_187])).

tff(c_192,plain,(
    ~ v2_struct_0(k6_tmap_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_191])).

tff(c_208,plain,(
    ! [A_156,B_157] :
      ( v2_pre_topc(k6_tmap_1(A_156,B_157))
      | ~ m1_subset_1(B_157,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ l1_pre_topc(A_156)
      | ~ v2_pre_topc(A_156)
      | v2_struct_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_214,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_208])).

tff(c_218,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_214])).

tff(c_219,plain,(
    v2_pre_topc(k6_tmap_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_218])).

tff(c_195,plain,(
    ! [A_153,B_154] :
      ( l1_pre_topc(k6_tmap_1(A_153,B_154))
      | ~ m1_subset_1(B_154,k1_zfmisc_1(u1_struct_0(A_153)))
      | ~ l1_pre_topc(A_153)
      | ~ v2_pre_topc(A_153)
      | v2_struct_0(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_201,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_195])).

tff(c_205,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_201])).

tff(c_206,plain,(
    l1_pre_topc(k6_tmap_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_205])).

tff(c_234,plain,(
    ! [A_162,B_163] :
      ( v1_funct_1(k7_tmap_1(A_162,B_163))
      | ~ m1_subset_1(B_163,k1_zfmisc_1(u1_struct_0(A_162)))
      | ~ l1_pre_topc(A_162)
      | ~ v2_pre_topc(A_162)
      | v2_struct_0(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_240,plain,
    ( v1_funct_1(k7_tmap_1('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_234])).

tff(c_244,plain,
    ( v1_funct_1(k7_tmap_1('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_240])).

tff(c_245,plain,(
    v1_funct_1(k7_tmap_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_244])).

tff(c_48,plain,(
    ! [A_31,B_32] :
      ( m1_subset_1(k7_tmap_1(A_31,B_32),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_31),u1_struct_0(k6_tmap_1(A_31,B_32)))))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31)
      | ~ v2_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2619,plain,(
    ! [B_301,A_300,C_303,D_302,F_299] :
      ( r1_tmap_1(D_302,A_300,k2_tmap_1(B_301,A_300,C_303,D_302),F_299)
      | ~ r1_tmap_1(B_301,A_300,C_303,F_299)
      | ~ m1_subset_1(F_299,u1_struct_0(D_302))
      | ~ m1_subset_1(F_299,u1_struct_0(B_301))
      | ~ m1_pre_topc(D_302,B_301)
      | v2_struct_0(D_302)
      | ~ m1_subset_1(C_303,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_301),u1_struct_0(A_300))))
      | ~ v1_funct_2(C_303,u1_struct_0(B_301),u1_struct_0(A_300))
      | ~ v1_funct_1(C_303)
      | ~ l1_pre_topc(B_301)
      | ~ v2_pre_topc(B_301)
      | v2_struct_0(B_301)
      | ~ l1_pre_topc(A_300)
      | ~ v2_pre_topc(A_300)
      | v2_struct_0(A_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_17431,plain,(
    ! [D_3728,A_3729,B_3730,F_3731] :
      ( r1_tmap_1(D_3728,k6_tmap_1(A_3729,B_3730),k2_tmap_1(A_3729,k6_tmap_1(A_3729,B_3730),k7_tmap_1(A_3729,B_3730),D_3728),F_3731)
      | ~ r1_tmap_1(A_3729,k6_tmap_1(A_3729,B_3730),k7_tmap_1(A_3729,B_3730),F_3731)
      | ~ m1_subset_1(F_3731,u1_struct_0(D_3728))
      | ~ m1_subset_1(F_3731,u1_struct_0(A_3729))
      | ~ m1_pre_topc(D_3728,A_3729)
      | v2_struct_0(D_3728)
      | ~ v1_funct_2(k7_tmap_1(A_3729,B_3730),u1_struct_0(A_3729),u1_struct_0(k6_tmap_1(A_3729,B_3730)))
      | ~ v1_funct_1(k7_tmap_1(A_3729,B_3730))
      | ~ l1_pre_topc(k6_tmap_1(A_3729,B_3730))
      | ~ v2_pre_topc(k6_tmap_1(A_3729,B_3730))
      | v2_struct_0(k6_tmap_1(A_3729,B_3730))
      | ~ m1_subset_1(B_3730,k1_zfmisc_1(u1_struct_0(A_3729)))
      | ~ l1_pre_topc(A_3729)
      | ~ v2_pre_topc(A_3729)
      | v2_struct_0(A_3729) ) ),
    inference(resolution,[status(thm)],[c_48,c_2619])).

tff(c_64,plain,(
    ~ r1_tmap_1('#skF_6',k6_tmap_1('#skF_4','#skF_5'),k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_17434,plain,
    ( ~ r1_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | v2_struct_0('#skF_6')
    | ~ v1_funct_2(k7_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0(k6_tmap_1('#skF_4','#skF_5')))
    | ~ v1_funct_1(k7_tmap_1('#skF_4','#skF_5'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
    | ~ v2_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
    | v2_struct_0(k6_tmap_1('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_17431,c_64])).

tff(c_17449,plain,
    ( ~ r1_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_6')
    | ~ v1_funct_2(k7_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0(k6_tmap_1('#skF_4','#skF_5')))
    | v2_struct_0(k6_tmap_1('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_219,c_206,c_245,c_70,c_66,c_17434])).

tff(c_17450,plain,
    ( ~ r1_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_4'))
    | ~ v1_funct_2(k7_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0(k6_tmap_1('#skF_4','#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_192,c_72,c_17449])).

tff(c_17454,plain,(
    ~ v1_funct_2(k7_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0(k6_tmap_1('#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_17450])).

tff(c_17466,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_17454])).

tff(c_17470,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_17466])).

tff(c_17472,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_17470])).

tff(c_17473,plain,
    ( ~ m1_subset_1('#skF_7',u1_struct_0('#skF_4'))
    | ~ r1_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_17450])).

tff(c_17488,plain,(
    ~ r1_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_17473])).

tff(c_17497,plain,
    ( r2_hidden('#skF_7','#skF_5')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_17488])).

tff(c_17501,plain,
    ( r2_hidden('#skF_7','#skF_5')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_17497])).

tff(c_17502,plain,(
    ~ m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_148,c_17501])).

tff(c_17505,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_538,c_17502])).

tff(c_17508,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_70,c_17505])).

tff(c_17510,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_17508])).

tff(c_17511,plain,(
    ~ m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_17473])).

tff(c_17515,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_538,c_17511])).

tff(c_17518,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_70,c_17515])).

tff(c_17520,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_17518])).

tff(c_17521,plain,(
    v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_17534,plain,(
    ! [A_3861] :
      ( m1_subset_1('#skF_3'(A_3861),k1_zfmisc_1(u1_struct_0(A_3861)))
      | ~ l1_pre_topc(A_3861)
      | ~ v2_pre_topc(A_3861)
      | v2_struct_0(A_3861) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_24,plain,(
    ! [B_11,A_9] :
      ( v1_xboole_0(B_11)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_9))
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_17549,plain,(
    ! [A_3868] :
      ( v1_xboole_0('#skF_3'(A_3868))
      | ~ v1_xboole_0(u1_struct_0(A_3868))
      | ~ l1_pre_topc(A_3868)
      | ~ v2_pre_topc(A_3868)
      | v2_struct_0(A_3868) ) ),
    inference(resolution,[status(thm)],[c_17534,c_24])).

tff(c_17552,plain,
    ( v1_xboole_0('#skF_3'('#skF_6'))
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_17521,c_17549])).

tff(c_17555,plain,
    ( v1_xboole_0('#skF_3'('#skF_6'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_96,c_17552])).

tff(c_17556,plain,(
    v1_xboole_0('#skF_3'('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_17555])).

tff(c_38,plain,(
    ! [A_27] :
      ( ~ v1_xboole_0('#skF_3'(A_27))
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_17571,plain,
    ( ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_17556,c_38])).

tff(c_17574,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_96,c_17571])).

tff(c_17576,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_17574])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n001.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:48:30 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.61/3.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.61/3.93  
% 10.61/3.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.61/3.93  %$ r1_tmap_1 > v1_funct_2 > v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k7_tmap_1 > k6_tmap_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 10.61/3.93  
% 10.61/3.93  %Foreground sorts:
% 10.61/3.93  
% 10.61/3.93  
% 10.61/3.93  %Background operators:
% 10.61/3.93  
% 10.61/3.93  
% 10.61/3.93  %Foreground operators:
% 10.61/3.93  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 10.61/3.93  tff(k7_tmap_1, type, k7_tmap_1: ($i * $i) > $i).
% 10.61/3.93  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 10.61/3.93  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.61/3.93  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 10.61/3.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.61/3.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.61/3.93  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.61/3.93  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 10.61/3.93  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.61/3.93  tff('#skF_7', type, '#skF_7': $i).
% 10.61/3.93  tff('#skF_5', type, '#skF_5': $i).
% 10.61/3.93  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.61/3.93  tff('#skF_6', type, '#skF_6': $i).
% 10.61/3.93  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.61/3.93  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.61/3.93  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 10.61/3.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.61/3.93  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 10.61/3.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.61/3.93  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.61/3.93  tff('#skF_4', type, '#skF_4': $i).
% 10.61/3.93  tff('#skF_3', type, '#skF_3': $i > $i).
% 10.61/3.93  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 10.61/3.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.61/3.93  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 10.61/3.93  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.61/3.93  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 10.61/3.93  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.61/3.93  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.61/3.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.61/3.93  
% 10.61/3.95  tff(f_229, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (r1_xboole_0(u1_struct_0(C), B) => (![D]: (m1_subset_1(D, u1_struct_0(C)) => r1_tmap_1(C, k6_tmap_1(A, B), k2_tmap_1(A, k6_tmap_1(A, B), k7_tmap_1(A, B), C), D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_tmap_1)).
% 10.61/3.95  tff(f_61, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 10.61/3.95  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 10.61/3.95  tff(f_84, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 10.61/3.95  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 10.61/3.95  tff(f_39, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 10.61/3.95  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 10.61/3.95  tff(f_165, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (~r2_hidden(C, B) => r1_tmap_1(A, k6_tmap_1(A, B), k7_tmap_1(A, B), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_tmap_1)).
% 10.61/3.95  tff(f_131, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_funct_1(k7_tmap_1(A, B)) & v1_funct_2(k7_tmap_1(A, B), u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))) & m1_subset_1(k7_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 10.61/3.95  tff(f_147, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((~v2_struct_0(k6_tmap_1(A, B)) & v1_pre_topc(k6_tmap_1(A, B))) & v2_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_tmap_1)).
% 10.61/3.95  tff(f_116, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 10.61/3.95  tff(f_205, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tmap_1)).
% 10.61/3.95  tff(f_101, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: (((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v3_pre_topc(B, A)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_tops_1)).
% 10.61/3.95  tff(f_46, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 10.61/3.95  tff(c_72, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_229])).
% 10.61/3.95  tff(c_78, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_229])).
% 10.61/3.95  tff(c_76, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_229])).
% 10.61/3.95  tff(c_70, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_229])).
% 10.61/3.95  tff(c_134, plain, (![B_134, A_135]: (v2_pre_topc(B_134) | ~m1_pre_topc(B_134, A_135) | ~l1_pre_topc(A_135) | ~v2_pre_topc(A_135))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.61/3.95  tff(c_137, plain, (v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_70, c_134])).
% 10.61/3.95  tff(c_140, plain, (v2_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_137])).
% 10.61/3.95  tff(c_90, plain, (![B_118, A_119]: (l1_pre_topc(B_118) | ~m1_pre_topc(B_118, A_119) | ~l1_pre_topc(A_119))), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.61/3.95  tff(c_93, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_70, c_90])).
% 10.61/3.95  tff(c_96, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_93])).
% 10.61/3.95  tff(c_80, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_229])).
% 10.61/3.95  tff(c_66, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_229])).
% 10.61/3.95  tff(c_533, plain, (![C_196, A_197, B_198]: (m1_subset_1(C_196, u1_struct_0(A_197)) | ~m1_subset_1(C_196, u1_struct_0(B_198)) | ~m1_pre_topc(B_198, A_197) | v2_struct_0(B_198) | ~l1_pre_topc(A_197) | v2_struct_0(A_197))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.61/3.95  tff(c_535, plain, (![A_197]: (m1_subset_1('#skF_7', u1_struct_0(A_197)) | ~m1_pre_topc('#skF_6', A_197) | v2_struct_0('#skF_6') | ~l1_pre_topc(A_197) | v2_struct_0(A_197))), inference(resolution, [status(thm)], [c_66, c_533])).
% 10.61/3.95  tff(c_538, plain, (![A_197]: (m1_subset_1('#skF_7', u1_struct_0(A_197)) | ~m1_pre_topc('#skF_6', A_197) | ~l1_pre_topc(A_197) | v2_struct_0(A_197))), inference(negUnitSimplification, [status(thm)], [c_72, c_535])).
% 10.61/3.95  tff(c_111, plain, (![A_129, B_130]: (r2_hidden(A_129, B_130) | v1_xboole_0(B_130) | ~m1_subset_1(A_129, B_130))), inference(cnfTransformation, [status(thm)], [f_52])).
% 10.61/3.95  tff(c_68, plain, (r1_xboole_0(u1_struct_0('#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_229])).
% 10.61/3.95  tff(c_81, plain, (![A_116, B_117]: (k4_xboole_0(A_116, B_117)=A_116 | ~r1_xboole_0(A_116, B_117))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.61/3.95  tff(c_85, plain, (k4_xboole_0(u1_struct_0('#skF_6'), '#skF_5')=u1_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_68, c_81])).
% 10.61/3.95  tff(c_106, plain, (![D_125, B_126, A_127]: (~r2_hidden(D_125, B_126) | ~r2_hidden(D_125, k4_xboole_0(A_127, B_126)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.61/3.95  tff(c_109, plain, (![D_125]: (~r2_hidden(D_125, '#skF_5') | ~r2_hidden(D_125, u1_struct_0('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_85, c_106])).
% 10.61/3.95  tff(c_124, plain, (![A_129]: (~r2_hidden(A_129, '#skF_5') | v1_xboole_0(u1_struct_0('#skF_6')) | ~m1_subset_1(A_129, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_111, c_109])).
% 10.61/3.95  tff(c_144, plain, (![A_138]: (~r2_hidden(A_138, '#skF_5') | ~m1_subset_1(A_138, u1_struct_0('#skF_6')))), inference(splitLeft, [status(thm)], [c_124])).
% 10.61/3.95  tff(c_148, plain, (~r2_hidden('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_66, c_144])).
% 10.61/3.95  tff(c_74, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_229])).
% 10.61/3.95  tff(c_60, plain, (![A_35, B_39, C_41]: (r1_tmap_1(A_35, k6_tmap_1(A_35, B_39), k7_tmap_1(A_35, B_39), C_41) | r2_hidden(C_41, B_39) | ~m1_subset_1(C_41, u1_struct_0(A_35)) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35) | ~v2_pre_topc(A_35) | v2_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_165])).
% 10.61/3.95  tff(c_50, plain, (![A_31, B_32]: (v1_funct_2(k7_tmap_1(A_31, B_32), u1_struct_0(A_31), u1_struct_0(k6_tmap_1(A_31, B_32))) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31) | ~v2_pre_topc(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_131])).
% 10.61/3.95  tff(c_181, plain, (![A_149, B_150]: (~v2_struct_0(k6_tmap_1(A_149, B_150)) | ~m1_subset_1(B_150, k1_zfmisc_1(u1_struct_0(A_149))) | ~l1_pre_topc(A_149) | ~v2_pre_topc(A_149) | v2_struct_0(A_149))), inference(cnfTransformation, [status(thm)], [f_147])).
% 10.61/3.95  tff(c_187, plain, (~v2_struct_0(k6_tmap_1('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_74, c_181])).
% 10.61/3.95  tff(c_191, plain, (~v2_struct_0(k6_tmap_1('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_187])).
% 10.61/3.95  tff(c_192, plain, (~v2_struct_0(k6_tmap_1('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_80, c_191])).
% 10.61/3.95  tff(c_208, plain, (![A_156, B_157]: (v2_pre_topc(k6_tmap_1(A_156, B_157)) | ~m1_subset_1(B_157, k1_zfmisc_1(u1_struct_0(A_156))) | ~l1_pre_topc(A_156) | ~v2_pre_topc(A_156) | v2_struct_0(A_156))), inference(cnfTransformation, [status(thm)], [f_147])).
% 10.61/3.95  tff(c_214, plain, (v2_pre_topc(k6_tmap_1('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_74, c_208])).
% 10.61/3.95  tff(c_218, plain, (v2_pre_topc(k6_tmap_1('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_214])).
% 10.61/3.95  tff(c_219, plain, (v2_pre_topc(k6_tmap_1('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_80, c_218])).
% 10.61/3.95  tff(c_195, plain, (![A_153, B_154]: (l1_pre_topc(k6_tmap_1(A_153, B_154)) | ~m1_subset_1(B_154, k1_zfmisc_1(u1_struct_0(A_153))) | ~l1_pre_topc(A_153) | ~v2_pre_topc(A_153) | v2_struct_0(A_153))), inference(cnfTransformation, [status(thm)], [f_116])).
% 10.61/3.95  tff(c_201, plain, (l1_pre_topc(k6_tmap_1('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_74, c_195])).
% 10.61/3.95  tff(c_205, plain, (l1_pre_topc(k6_tmap_1('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_201])).
% 10.61/3.95  tff(c_206, plain, (l1_pre_topc(k6_tmap_1('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_80, c_205])).
% 10.61/3.95  tff(c_234, plain, (![A_162, B_163]: (v1_funct_1(k7_tmap_1(A_162, B_163)) | ~m1_subset_1(B_163, k1_zfmisc_1(u1_struct_0(A_162))) | ~l1_pre_topc(A_162) | ~v2_pre_topc(A_162) | v2_struct_0(A_162))), inference(cnfTransformation, [status(thm)], [f_131])).
% 10.61/3.95  tff(c_240, plain, (v1_funct_1(k7_tmap_1('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_74, c_234])).
% 10.61/3.95  tff(c_244, plain, (v1_funct_1(k7_tmap_1('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_240])).
% 10.61/3.95  tff(c_245, plain, (v1_funct_1(k7_tmap_1('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_80, c_244])).
% 10.61/3.95  tff(c_48, plain, (![A_31, B_32]: (m1_subset_1(k7_tmap_1(A_31, B_32), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_31), u1_struct_0(k6_tmap_1(A_31, B_32))))) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31) | ~v2_pre_topc(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_131])).
% 10.61/3.95  tff(c_2619, plain, (![B_301, A_300, C_303, D_302, F_299]: (r1_tmap_1(D_302, A_300, k2_tmap_1(B_301, A_300, C_303, D_302), F_299) | ~r1_tmap_1(B_301, A_300, C_303, F_299) | ~m1_subset_1(F_299, u1_struct_0(D_302)) | ~m1_subset_1(F_299, u1_struct_0(B_301)) | ~m1_pre_topc(D_302, B_301) | v2_struct_0(D_302) | ~m1_subset_1(C_303, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_301), u1_struct_0(A_300)))) | ~v1_funct_2(C_303, u1_struct_0(B_301), u1_struct_0(A_300)) | ~v1_funct_1(C_303) | ~l1_pre_topc(B_301) | ~v2_pre_topc(B_301) | v2_struct_0(B_301) | ~l1_pre_topc(A_300) | ~v2_pre_topc(A_300) | v2_struct_0(A_300))), inference(cnfTransformation, [status(thm)], [f_205])).
% 10.61/3.95  tff(c_17431, plain, (![D_3728, A_3729, B_3730, F_3731]: (r1_tmap_1(D_3728, k6_tmap_1(A_3729, B_3730), k2_tmap_1(A_3729, k6_tmap_1(A_3729, B_3730), k7_tmap_1(A_3729, B_3730), D_3728), F_3731) | ~r1_tmap_1(A_3729, k6_tmap_1(A_3729, B_3730), k7_tmap_1(A_3729, B_3730), F_3731) | ~m1_subset_1(F_3731, u1_struct_0(D_3728)) | ~m1_subset_1(F_3731, u1_struct_0(A_3729)) | ~m1_pre_topc(D_3728, A_3729) | v2_struct_0(D_3728) | ~v1_funct_2(k7_tmap_1(A_3729, B_3730), u1_struct_0(A_3729), u1_struct_0(k6_tmap_1(A_3729, B_3730))) | ~v1_funct_1(k7_tmap_1(A_3729, B_3730)) | ~l1_pre_topc(k6_tmap_1(A_3729, B_3730)) | ~v2_pre_topc(k6_tmap_1(A_3729, B_3730)) | v2_struct_0(k6_tmap_1(A_3729, B_3730)) | ~m1_subset_1(B_3730, k1_zfmisc_1(u1_struct_0(A_3729))) | ~l1_pre_topc(A_3729) | ~v2_pre_topc(A_3729) | v2_struct_0(A_3729))), inference(resolution, [status(thm)], [c_48, c_2619])).
% 10.61/3.95  tff(c_64, plain, (~r1_tmap_1('#skF_6', k6_tmap_1('#skF_4', '#skF_5'), k2_tmap_1('#skF_4', k6_tmap_1('#skF_4', '#skF_5'), k7_tmap_1('#skF_4', '#skF_5'), '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_229])).
% 10.61/3.95  tff(c_17434, plain, (~r1_tmap_1('#skF_4', k6_tmap_1('#skF_4', '#skF_5'), k7_tmap_1('#skF_4', '#skF_5'), '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_6') | ~v1_funct_2(k7_tmap_1('#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0(k6_tmap_1('#skF_4', '#skF_5'))) | ~v1_funct_1(k7_tmap_1('#skF_4', '#skF_5')) | ~l1_pre_topc(k6_tmap_1('#skF_4', '#skF_5')) | ~v2_pre_topc(k6_tmap_1('#skF_4', '#skF_5')) | v2_struct_0(k6_tmap_1('#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_17431, c_64])).
% 10.61/3.95  tff(c_17449, plain, (~r1_tmap_1('#skF_4', k6_tmap_1('#skF_4', '#skF_5'), k7_tmap_1('#skF_4', '#skF_5'), '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_4')) | v2_struct_0('#skF_6') | ~v1_funct_2(k7_tmap_1('#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0(k6_tmap_1('#skF_4', '#skF_5'))) | v2_struct_0(k6_tmap_1('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_219, c_206, c_245, c_70, c_66, c_17434])).
% 10.61/3.95  tff(c_17450, plain, (~r1_tmap_1('#skF_4', k6_tmap_1('#skF_4', '#skF_5'), k7_tmap_1('#skF_4', '#skF_5'), '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_4')) | ~v1_funct_2(k7_tmap_1('#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0(k6_tmap_1('#skF_4', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_80, c_192, c_72, c_17449])).
% 10.61/3.95  tff(c_17454, plain, (~v1_funct_2(k7_tmap_1('#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0(k6_tmap_1('#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_17450])).
% 10.61/3.95  tff(c_17466, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_50, c_17454])).
% 10.61/3.95  tff(c_17470, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_17466])).
% 10.61/3.95  tff(c_17472, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_17470])).
% 10.61/3.95  tff(c_17473, plain, (~m1_subset_1('#skF_7', u1_struct_0('#skF_4')) | ~r1_tmap_1('#skF_4', k6_tmap_1('#skF_4', '#skF_5'), k7_tmap_1('#skF_4', '#skF_5'), '#skF_7')), inference(splitRight, [status(thm)], [c_17450])).
% 10.61/3.95  tff(c_17488, plain, (~r1_tmap_1('#skF_4', k6_tmap_1('#skF_4', '#skF_5'), k7_tmap_1('#skF_4', '#skF_5'), '#skF_7')), inference(splitLeft, [status(thm)], [c_17473])).
% 10.61/3.95  tff(c_17497, plain, (r2_hidden('#skF_7', '#skF_5') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_60, c_17488])).
% 10.61/3.95  tff(c_17501, plain, (r2_hidden('#skF_7', '#skF_5') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_17497])).
% 10.61/3.95  tff(c_17502, plain, (~m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_80, c_148, c_17501])).
% 10.61/3.95  tff(c_17505, plain, (~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_538, c_17502])).
% 10.61/3.95  tff(c_17508, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_70, c_17505])).
% 10.61/3.95  tff(c_17510, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_17508])).
% 10.61/3.95  tff(c_17511, plain, (~m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_17473])).
% 10.61/3.95  tff(c_17515, plain, (~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_538, c_17511])).
% 10.61/3.95  tff(c_17518, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_70, c_17515])).
% 10.61/3.95  tff(c_17520, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_17518])).
% 10.61/3.95  tff(c_17521, plain, (v1_xboole_0(u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_124])).
% 10.61/3.95  tff(c_17534, plain, (![A_3861]: (m1_subset_1('#skF_3'(A_3861), k1_zfmisc_1(u1_struct_0(A_3861))) | ~l1_pre_topc(A_3861) | ~v2_pre_topc(A_3861) | v2_struct_0(A_3861))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.61/3.95  tff(c_24, plain, (![B_11, A_9]: (v1_xboole_0(B_11) | ~m1_subset_1(B_11, k1_zfmisc_1(A_9)) | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.61/3.95  tff(c_17549, plain, (![A_3868]: (v1_xboole_0('#skF_3'(A_3868)) | ~v1_xboole_0(u1_struct_0(A_3868)) | ~l1_pre_topc(A_3868) | ~v2_pre_topc(A_3868) | v2_struct_0(A_3868))), inference(resolution, [status(thm)], [c_17534, c_24])).
% 10.61/3.95  tff(c_17552, plain, (v1_xboole_0('#skF_3'('#skF_6')) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_17521, c_17549])).
% 10.61/3.95  tff(c_17555, plain, (v1_xboole_0('#skF_3'('#skF_6')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_96, c_17552])).
% 10.61/3.95  tff(c_17556, plain, (v1_xboole_0('#skF_3'('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_72, c_17555])).
% 10.61/3.95  tff(c_38, plain, (![A_27]: (~v1_xboole_0('#skF_3'(A_27)) | ~l1_pre_topc(A_27) | ~v2_pre_topc(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.61/3.95  tff(c_17571, plain, (~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_17556, c_38])).
% 10.61/3.95  tff(c_17574, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_96, c_17571])).
% 10.61/3.95  tff(c_17576, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_17574])).
% 10.61/3.95  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.61/3.95  
% 10.61/3.95  Inference rules
% 10.61/3.95  ----------------------
% 10.61/3.95  #Ref     : 0
% 10.61/3.95  #Sup     : 4293
% 10.61/3.95  #Fact    : 0
% 10.61/3.95  #Define  : 0
% 10.61/3.95  #Split   : 19
% 10.61/3.95  #Chain   : 0
% 10.61/3.95  #Close   : 0
% 10.61/3.95  
% 10.61/3.95  Ordering : KBO
% 10.61/3.95  
% 10.61/3.95  Simplification rules
% 10.61/3.95  ----------------------
% 10.61/3.95  #Subsume      : 1353
% 10.61/3.95  #Demod        : 1446
% 10.61/3.95  #Tautology    : 733
% 10.61/3.95  #SimpNegUnit  : 19
% 10.61/3.95  #BackRed      : 0
% 10.61/3.95  
% 10.61/3.95  #Partial instantiations: 2212
% 10.61/3.95  #Strategies tried      : 1
% 10.61/3.95  
% 10.61/3.95  Timing (in seconds)
% 10.61/3.95  ----------------------
% 10.61/3.95  Preprocessing        : 0.38
% 10.61/3.95  Parsing              : 0.21
% 10.61/3.95  CNF conversion       : 0.04
% 10.61/3.95  Main loop            : 2.77
% 10.61/3.95  Inferencing          : 0.69
% 10.61/3.95  Reduction            : 1.11
% 10.61/3.95  Demodulation         : 0.92
% 10.61/3.95  BG Simplification    : 0.09
% 10.61/3.95  Subsumption          : 0.72
% 10.61/3.95  Abstraction          : 0.11
% 10.61/3.95  MUC search           : 0.00
% 10.61/3.95  Cooper               : 0.00
% 10.61/3.95  Total                : 3.19
% 10.61/3.96  Index Insertion      : 0.00
% 10.61/3.96  Index Deletion       : 0.00
% 10.61/3.96  Index Matching       : 0.00
% 10.61/3.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
