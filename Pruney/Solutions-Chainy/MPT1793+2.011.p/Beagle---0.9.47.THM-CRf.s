%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:55 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.43s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 374 expanded)
%              Number of leaves         :   41 ( 158 expanded)
%              Depth                    :   14
%              Number of atoms          :  320 (1680 expanded)
%              Number of equality atoms :    1 (   3 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k7_tmap_1 > k6_tmap_1 > k2_zfmisc_1 > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k7_tmap_1,type,(
    k7_tmap_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_connsp_2,type,(
    k1_connsp_2: ( $i * $i ) > $i )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_239,negated_conjecture,(
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

tff(f_65,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_88,axiom,(
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

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_175,axiom,(
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

tff(f_141,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_funct_1(k7_tmap_1(A,B))
        & v1_funct_2(k7_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B)))
        & m1_subset_1(k7_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B))))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).

tff(f_157,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( ~ v2_struct_0(k6_tmap_1(A,B))
        & v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_tmap_1)).

tff(f_126,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_215,axiom,(
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

tff(f_111,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r2_hidden(B,k1_connsp_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_connsp_2)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k1_connsp_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_connsp_2)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_58,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_56,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_50,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_107,plain,(
    ! [B_132,A_133] :
      ( v2_pre_topc(B_132)
      | ~ m1_pre_topc(B_132,A_133)
      | ~ l1_pre_topc(A_133)
      | ~ v2_pre_topc(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_110,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_107])).

tff(c_113,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_110])).

tff(c_61,plain,(
    ! [B_116,A_117] :
      ( l1_pre_topc(B_116)
      | ~ m1_pre_topc(B_116,A_117)
      | ~ l1_pre_topc(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_64,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_61])).

tff(c_67,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_64])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_206,plain,(
    ! [C_152,A_153,B_154] :
      ( m1_subset_1(C_152,u1_struct_0(A_153))
      | ~ m1_subset_1(C_152,u1_struct_0(B_154))
      | ~ m1_pre_topc(B_154,A_153)
      | v2_struct_0(B_154)
      | ~ l1_pre_topc(A_153)
      | v2_struct_0(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_208,plain,(
    ! [A_153] :
      ( m1_subset_1('#skF_5',u1_struct_0(A_153))
      | ~ m1_pre_topc('#skF_4',A_153)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_153)
      | v2_struct_0(A_153) ) ),
    inference(resolution,[status(thm)],[c_46,c_206])).

tff(c_211,plain,(
    ! [A_153] :
      ( m1_subset_1('#skF_5',u1_struct_0(A_153))
      | ~ m1_pre_topc('#skF_4',A_153)
      | ~ l1_pre_topc(A_153)
      | v2_struct_0(A_153) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_208])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | v1_xboole_0(B_7)
      | ~ m1_subset_1(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_48,plain,(
    r1_xboole_0(u1_struct_0('#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_71,plain,(
    ! [A_124,B_125,C_126] :
      ( ~ r1_xboole_0(A_124,B_125)
      | ~ r2_hidden(C_126,B_125)
      | ~ r2_hidden(C_126,A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_80,plain,(
    ! [C_130] :
      ( ~ r2_hidden(C_130,'#skF_3')
      | ~ r2_hidden(C_130,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_48,c_71])).

tff(c_94,plain,(
    ! [A_6] :
      ( ~ r2_hidden(A_6,'#skF_3')
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_6,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_8,c_80])).

tff(c_115,plain,(
    ! [A_134] :
      ( ~ r2_hidden(A_134,'#skF_3')
      | ~ m1_subset_1(A_134,u1_struct_0('#skF_4')) ) ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_119,plain,(
    ~ r2_hidden('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_115])).

tff(c_54,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_40,plain,(
    ! [A_35,B_39,C_41] :
      ( r1_tmap_1(A_35,k6_tmap_1(A_35,B_39),k7_tmap_1(A_35,B_39),C_41)
      | r2_hidden(C_41,B_39)
      | ~ m1_subset_1(C_41,u1_struct_0(A_35))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_30,plain,(
    ! [A_31,B_32] :
      ( v1_funct_2(k7_tmap_1(A_31,B_32),u1_struct_0(A_31),u1_struct_0(k6_tmap_1(A_31,B_32)))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31)
      | ~ v2_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_148,plain,(
    ! [A_138,B_139] :
      ( ~ v2_struct_0(k6_tmap_1(A_138,B_139))
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_151,plain,
    ( ~ v2_struct_0(k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_148])).

tff(c_154,plain,
    ( ~ v2_struct_0(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_151])).

tff(c_155,plain,(
    ~ v2_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_154])).

tff(c_165,plain,(
    ! [A_144,B_145] :
      ( v2_pre_topc(k6_tmap_1(A_144,B_145))
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ l1_pre_topc(A_144)
      | ~ v2_pre_topc(A_144)
      | v2_struct_0(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_168,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_165])).

tff(c_171,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_168])).

tff(c_172,plain,(
    v2_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_171])).

tff(c_156,plain,(
    ! [A_140,B_141] :
      ( l1_pre_topc(k6_tmap_1(A_140,B_141))
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ l1_pre_topc(A_140)
      | ~ v2_pre_topc(A_140)
      | v2_struct_0(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_159,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_156])).

tff(c_162,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_159])).

tff(c_163,plain,(
    l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_162])).

tff(c_173,plain,(
    ! [A_146,B_147] :
      ( v1_funct_1(k7_tmap_1(A_146,B_147))
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ l1_pre_topc(A_146)
      | ~ v2_pre_topc(A_146)
      | v2_struct_0(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_176,plain,
    ( v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_173])).

tff(c_179,plain,
    ( v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_176])).

tff(c_180,plain,(
    v1_funct_1(k7_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_179])).

tff(c_28,plain,(
    ! [A_31,B_32] :
      ( m1_subset_1(k7_tmap_1(A_31,B_32),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_31),u1_struct_0(k6_tmap_1(A_31,B_32)))))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31)
      | ~ v2_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_276,plain,(
    ! [A_183,D_185,B_184,C_186,F_182] :
      ( r1_tmap_1(D_185,A_183,k2_tmap_1(B_184,A_183,C_186,D_185),F_182)
      | ~ r1_tmap_1(B_184,A_183,C_186,F_182)
      | ~ m1_subset_1(F_182,u1_struct_0(D_185))
      | ~ m1_subset_1(F_182,u1_struct_0(B_184))
      | ~ m1_pre_topc(D_185,B_184)
      | v2_struct_0(D_185)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_184),u1_struct_0(A_183))))
      | ~ v1_funct_2(C_186,u1_struct_0(B_184),u1_struct_0(A_183))
      | ~ v1_funct_1(C_186)
      | ~ l1_pre_topc(B_184)
      | ~ v2_pre_topc(B_184)
      | v2_struct_0(B_184)
      | ~ l1_pre_topc(A_183)
      | ~ v2_pre_topc(A_183)
      | v2_struct_0(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_280,plain,(
    ! [D_187,A_188,B_189,F_190] :
      ( r1_tmap_1(D_187,k6_tmap_1(A_188,B_189),k2_tmap_1(A_188,k6_tmap_1(A_188,B_189),k7_tmap_1(A_188,B_189),D_187),F_190)
      | ~ r1_tmap_1(A_188,k6_tmap_1(A_188,B_189),k7_tmap_1(A_188,B_189),F_190)
      | ~ m1_subset_1(F_190,u1_struct_0(D_187))
      | ~ m1_subset_1(F_190,u1_struct_0(A_188))
      | ~ m1_pre_topc(D_187,A_188)
      | v2_struct_0(D_187)
      | ~ v1_funct_2(k7_tmap_1(A_188,B_189),u1_struct_0(A_188),u1_struct_0(k6_tmap_1(A_188,B_189)))
      | ~ v1_funct_1(k7_tmap_1(A_188,B_189))
      | ~ l1_pre_topc(k6_tmap_1(A_188,B_189))
      | ~ v2_pre_topc(k6_tmap_1(A_188,B_189))
      | v2_struct_0(k6_tmap_1(A_188,B_189))
      | ~ m1_subset_1(B_189,k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ l1_pre_topc(A_188)
      | ~ v2_pre_topc(A_188)
      | v2_struct_0(A_188) ) ),
    inference(resolution,[status(thm)],[c_28,c_276])).

tff(c_44,plain,(
    ~ r1_tmap_1('#skF_4',k6_tmap_1('#skF_2','#skF_3'),k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_283,plain,
    ( ~ r1_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_4')
    | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | ~ v2_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0(k6_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_280,c_44])).

tff(c_286,plain,
    ( ~ r1_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_4')
    | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
    | v2_struct_0(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_172,c_163,c_180,c_50,c_46,c_283])).

tff(c_287,plain,
    ( ~ r1_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
    | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_155,c_52,c_286])).

tff(c_288,plain,(
    ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_287])).

tff(c_291,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_288])).

tff(c_294,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_291])).

tff(c_296,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_294])).

tff(c_297,plain,
    ( ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
    | ~ r1_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_287])).

tff(c_299,plain,(
    ~ r1_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_297])).

tff(c_302,plain,
    ( r2_hidden('#skF_5','#skF_3')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_299])).

tff(c_305,plain,
    ( r2_hidden('#skF_5','#skF_3')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_302])).

tff(c_306,plain,(
    ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_119,c_305])).

tff(c_309,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_211,c_306])).

tff(c_312,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_50,c_309])).

tff(c_314,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_312])).

tff(c_315,plain,(
    ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_297])).

tff(c_319,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_211,c_315])).

tff(c_322,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_50,c_319])).

tff(c_324,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_322])).

tff(c_325,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_20,plain,(
    ! [B_28,A_26] :
      ( r2_hidden(B_28,k1_connsp_2(A_26,B_28))
      | ~ m1_subset_1(B_28,u1_struct_0(A_26))
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_392,plain,(
    ! [A_208,B_209] :
      ( m1_subset_1(k1_connsp_2(A_208,B_209),k1_zfmisc_1(u1_struct_0(A_208)))
      | ~ m1_subset_1(B_209,u1_struct_0(A_208))
      | ~ l1_pre_topc(A_208)
      | ~ v2_pre_topc(A_208)
      | v2_struct_0(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_10,plain,(
    ! [C_10,B_9,A_8] :
      ( ~ v1_xboole_0(C_10)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(C_10))
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_430,plain,(
    ! [A_224,A_225,B_226] :
      ( ~ v1_xboole_0(u1_struct_0(A_224))
      | ~ r2_hidden(A_225,k1_connsp_2(A_224,B_226))
      | ~ m1_subset_1(B_226,u1_struct_0(A_224))
      | ~ l1_pre_topc(A_224)
      | ~ v2_pre_topc(A_224)
      | v2_struct_0(A_224) ) ),
    inference(resolution,[status(thm)],[c_392,c_10])).

tff(c_450,plain,(
    ! [A_227,B_228] :
      ( ~ v1_xboole_0(u1_struct_0(A_227))
      | ~ m1_subset_1(B_228,u1_struct_0(A_227))
      | ~ l1_pre_topc(A_227)
      | ~ v2_pre_topc(A_227)
      | v2_struct_0(A_227) ) ),
    inference(resolution,[status(thm)],[c_20,c_430])).

tff(c_456,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_450])).

tff(c_460,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_67,c_325,c_456])).

tff(c_462,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_460])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:20:36 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.38/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.47  
% 3.43/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.48  %$ r1_tmap_1 > v1_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k7_tmap_1 > k6_tmap_1 > k2_zfmisc_1 > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.43/1.48  
% 3.43/1.48  %Foreground sorts:
% 3.43/1.48  
% 3.43/1.48  
% 3.43/1.48  %Background operators:
% 3.43/1.48  
% 3.43/1.48  
% 3.43/1.48  %Foreground operators:
% 3.43/1.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.43/1.48  tff(k7_tmap_1, type, k7_tmap_1: ($i * $i) > $i).
% 3.43/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.43/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.43/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.43/1.48  tff(k1_connsp_2, type, k1_connsp_2: ($i * $i) > $i).
% 3.43/1.48  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.43/1.48  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.43/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.43/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.43/1.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.43/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.43/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.43/1.48  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.43/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.43/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.43/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.43/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.43/1.48  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 3.43/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.43/1.48  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.43/1.48  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.43/1.48  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.43/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.43/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.43/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.43/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.43/1.48  
% 3.43/1.50  tff(f_239, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (r1_xboole_0(u1_struct_0(C), B) => (![D]: (m1_subset_1(D, u1_struct_0(C)) => r1_tmap_1(C, k6_tmap_1(A, B), k2_tmap_1(A, k6_tmap_1(A, B), k7_tmap_1(A, B), C), D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_tmap_1)).
% 3.43/1.50  tff(f_65, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.43/1.50  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.43/1.50  tff(f_88, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 3.43/1.50  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.43/1.50  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.43/1.50  tff(f_175, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (~r2_hidden(C, B) => r1_tmap_1(A, k6_tmap_1(A, B), k7_tmap_1(A, B), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_tmap_1)).
% 3.43/1.50  tff(f_141, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_funct_1(k7_tmap_1(A, B)) & v1_funct_2(k7_tmap_1(A, B), u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))) & m1_subset_1(k7_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 3.43/1.50  tff(f_157, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((~v2_struct_0(k6_tmap_1(A, B)) & v1_pre_topc(k6_tmap_1(A, B))) & v2_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_tmap_1)).
% 3.43/1.50  tff(f_126, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 3.43/1.50  tff(f_215, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tmap_1)).
% 3.43/1.50  tff(f_111, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r2_hidden(B, k1_connsp_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_connsp_2)).
% 3.43/1.50  tff(f_99, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k1_connsp_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_connsp_2)).
% 3.43/1.50  tff(f_56, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.43/1.50  tff(c_52, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_239])).
% 3.43/1.50  tff(c_58, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_239])).
% 3.43/1.50  tff(c_56, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_239])).
% 3.43/1.50  tff(c_50, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_239])).
% 3.43/1.50  tff(c_107, plain, (![B_132, A_133]: (v2_pre_topc(B_132) | ~m1_pre_topc(B_132, A_133) | ~l1_pre_topc(A_133) | ~v2_pre_topc(A_133))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.43/1.50  tff(c_110, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_107])).
% 3.43/1.50  tff(c_113, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_110])).
% 3.43/1.50  tff(c_61, plain, (![B_116, A_117]: (l1_pre_topc(B_116) | ~m1_pre_topc(B_116, A_117) | ~l1_pre_topc(A_117))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.43/1.50  tff(c_64, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_61])).
% 3.43/1.50  tff(c_67, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_64])).
% 3.43/1.50  tff(c_60, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_239])).
% 3.43/1.50  tff(c_46, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_239])).
% 3.43/1.50  tff(c_206, plain, (![C_152, A_153, B_154]: (m1_subset_1(C_152, u1_struct_0(A_153)) | ~m1_subset_1(C_152, u1_struct_0(B_154)) | ~m1_pre_topc(B_154, A_153) | v2_struct_0(B_154) | ~l1_pre_topc(A_153) | v2_struct_0(A_153))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.43/1.50  tff(c_208, plain, (![A_153]: (m1_subset_1('#skF_5', u1_struct_0(A_153)) | ~m1_pre_topc('#skF_4', A_153) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_153) | v2_struct_0(A_153))), inference(resolution, [status(thm)], [c_46, c_206])).
% 3.43/1.50  tff(c_211, plain, (![A_153]: (m1_subset_1('#skF_5', u1_struct_0(A_153)) | ~m1_pre_topc('#skF_4', A_153) | ~l1_pre_topc(A_153) | v2_struct_0(A_153))), inference(negUnitSimplification, [status(thm)], [c_52, c_208])).
% 3.43/1.50  tff(c_8, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | v1_xboole_0(B_7) | ~m1_subset_1(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.43/1.50  tff(c_48, plain, (r1_xboole_0(u1_struct_0('#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_239])).
% 3.43/1.50  tff(c_71, plain, (![A_124, B_125, C_126]: (~r1_xboole_0(A_124, B_125) | ~r2_hidden(C_126, B_125) | ~r2_hidden(C_126, A_124))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.43/1.50  tff(c_80, plain, (![C_130]: (~r2_hidden(C_130, '#skF_3') | ~r2_hidden(C_130, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_48, c_71])).
% 3.43/1.50  tff(c_94, plain, (![A_6]: (~r2_hidden(A_6, '#skF_3') | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(A_6, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_8, c_80])).
% 3.43/1.50  tff(c_115, plain, (![A_134]: (~r2_hidden(A_134, '#skF_3') | ~m1_subset_1(A_134, u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_94])).
% 3.43/1.50  tff(c_119, plain, (~r2_hidden('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_115])).
% 3.43/1.50  tff(c_54, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_239])).
% 3.43/1.50  tff(c_40, plain, (![A_35, B_39, C_41]: (r1_tmap_1(A_35, k6_tmap_1(A_35, B_39), k7_tmap_1(A_35, B_39), C_41) | r2_hidden(C_41, B_39) | ~m1_subset_1(C_41, u1_struct_0(A_35)) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35) | ~v2_pre_topc(A_35) | v2_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.43/1.50  tff(c_30, plain, (![A_31, B_32]: (v1_funct_2(k7_tmap_1(A_31, B_32), u1_struct_0(A_31), u1_struct_0(k6_tmap_1(A_31, B_32))) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31) | ~v2_pre_topc(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.43/1.50  tff(c_148, plain, (![A_138, B_139]: (~v2_struct_0(k6_tmap_1(A_138, B_139)) | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0(A_138))) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.43/1.50  tff(c_151, plain, (~v2_struct_0(k6_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_148])).
% 3.43/1.50  tff(c_154, plain, (~v2_struct_0(k6_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_151])).
% 3.43/1.50  tff(c_155, plain, (~v2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_154])).
% 3.43/1.50  tff(c_165, plain, (![A_144, B_145]: (v2_pre_topc(k6_tmap_1(A_144, B_145)) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0(A_144))) | ~l1_pre_topc(A_144) | ~v2_pre_topc(A_144) | v2_struct_0(A_144))), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.43/1.50  tff(c_168, plain, (v2_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_165])).
% 3.43/1.50  tff(c_171, plain, (v2_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_168])).
% 3.43/1.50  tff(c_172, plain, (v2_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_171])).
% 3.43/1.50  tff(c_156, plain, (![A_140, B_141]: (l1_pre_topc(k6_tmap_1(A_140, B_141)) | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0(A_140))) | ~l1_pre_topc(A_140) | ~v2_pre_topc(A_140) | v2_struct_0(A_140))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.43/1.50  tff(c_159, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_156])).
% 3.43/1.50  tff(c_162, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_159])).
% 3.43/1.50  tff(c_163, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_162])).
% 3.43/1.50  tff(c_173, plain, (![A_146, B_147]: (v1_funct_1(k7_tmap_1(A_146, B_147)) | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0(A_146))) | ~l1_pre_topc(A_146) | ~v2_pre_topc(A_146) | v2_struct_0(A_146))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.43/1.50  tff(c_176, plain, (v1_funct_1(k7_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_173])).
% 3.43/1.50  tff(c_179, plain, (v1_funct_1(k7_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_176])).
% 3.43/1.50  tff(c_180, plain, (v1_funct_1(k7_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_179])).
% 3.43/1.50  tff(c_28, plain, (![A_31, B_32]: (m1_subset_1(k7_tmap_1(A_31, B_32), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_31), u1_struct_0(k6_tmap_1(A_31, B_32))))) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31) | ~v2_pre_topc(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.43/1.50  tff(c_276, plain, (![A_183, D_185, B_184, C_186, F_182]: (r1_tmap_1(D_185, A_183, k2_tmap_1(B_184, A_183, C_186, D_185), F_182) | ~r1_tmap_1(B_184, A_183, C_186, F_182) | ~m1_subset_1(F_182, u1_struct_0(D_185)) | ~m1_subset_1(F_182, u1_struct_0(B_184)) | ~m1_pre_topc(D_185, B_184) | v2_struct_0(D_185) | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_184), u1_struct_0(A_183)))) | ~v1_funct_2(C_186, u1_struct_0(B_184), u1_struct_0(A_183)) | ~v1_funct_1(C_186) | ~l1_pre_topc(B_184) | ~v2_pre_topc(B_184) | v2_struct_0(B_184) | ~l1_pre_topc(A_183) | ~v2_pre_topc(A_183) | v2_struct_0(A_183))), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.43/1.50  tff(c_280, plain, (![D_187, A_188, B_189, F_190]: (r1_tmap_1(D_187, k6_tmap_1(A_188, B_189), k2_tmap_1(A_188, k6_tmap_1(A_188, B_189), k7_tmap_1(A_188, B_189), D_187), F_190) | ~r1_tmap_1(A_188, k6_tmap_1(A_188, B_189), k7_tmap_1(A_188, B_189), F_190) | ~m1_subset_1(F_190, u1_struct_0(D_187)) | ~m1_subset_1(F_190, u1_struct_0(A_188)) | ~m1_pre_topc(D_187, A_188) | v2_struct_0(D_187) | ~v1_funct_2(k7_tmap_1(A_188, B_189), u1_struct_0(A_188), u1_struct_0(k6_tmap_1(A_188, B_189))) | ~v1_funct_1(k7_tmap_1(A_188, B_189)) | ~l1_pre_topc(k6_tmap_1(A_188, B_189)) | ~v2_pre_topc(k6_tmap_1(A_188, B_189)) | v2_struct_0(k6_tmap_1(A_188, B_189)) | ~m1_subset_1(B_189, k1_zfmisc_1(u1_struct_0(A_188))) | ~l1_pre_topc(A_188) | ~v2_pre_topc(A_188) | v2_struct_0(A_188))), inference(resolution, [status(thm)], [c_28, c_276])).
% 3.43/1.50  tff(c_44, plain, (~r1_tmap_1('#skF_4', k6_tmap_1('#skF_2', '#skF_3'), k2_tmap_1('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3'), '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_239])).
% 3.43/1.50  tff(c_283, plain, (~r1_tmap_1('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3'), '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k7_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | ~v2_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | v2_struct_0(k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_280, c_44])).
% 3.43/1.50  tff(c_286, plain, (~r1_tmap_1('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3'), '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | v2_struct_0('#skF_4') | ~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))) | v2_struct_0(k6_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_172, c_163, c_180, c_50, c_46, c_283])).
% 3.43/1.50  tff(c_287, plain, (~r1_tmap_1('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3'), '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | ~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_60, c_155, c_52, c_286])).
% 3.43/1.50  tff(c_288, plain, (~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_287])).
% 3.43/1.50  tff(c_291, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_288])).
% 3.43/1.50  tff(c_294, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_291])).
% 3.43/1.50  tff(c_296, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_294])).
% 3.43/1.50  tff(c_297, plain, (~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | ~r1_tmap_1('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3'), '#skF_5')), inference(splitRight, [status(thm)], [c_287])).
% 3.43/1.50  tff(c_299, plain, (~r1_tmap_1('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3'), '#skF_5')), inference(splitLeft, [status(thm)], [c_297])).
% 3.43/1.50  tff(c_302, plain, (r2_hidden('#skF_5', '#skF_3') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_299])).
% 3.43/1.50  tff(c_305, plain, (r2_hidden('#skF_5', '#skF_3') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_302])).
% 3.43/1.50  tff(c_306, plain, (~m1_subset_1('#skF_5', u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_119, c_305])).
% 3.43/1.50  tff(c_309, plain, (~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_211, c_306])).
% 3.43/1.50  tff(c_312, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_50, c_309])).
% 3.43/1.50  tff(c_314, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_312])).
% 3.43/1.50  tff(c_315, plain, (~m1_subset_1('#skF_5', u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_297])).
% 3.43/1.50  tff(c_319, plain, (~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_211, c_315])).
% 3.43/1.50  tff(c_322, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_50, c_319])).
% 3.43/1.50  tff(c_324, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_322])).
% 3.43/1.50  tff(c_325, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_94])).
% 3.43/1.50  tff(c_20, plain, (![B_28, A_26]: (r2_hidden(B_28, k1_connsp_2(A_26, B_28)) | ~m1_subset_1(B_28, u1_struct_0(A_26)) | ~l1_pre_topc(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.43/1.50  tff(c_392, plain, (![A_208, B_209]: (m1_subset_1(k1_connsp_2(A_208, B_209), k1_zfmisc_1(u1_struct_0(A_208))) | ~m1_subset_1(B_209, u1_struct_0(A_208)) | ~l1_pre_topc(A_208) | ~v2_pre_topc(A_208) | v2_struct_0(A_208))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.43/1.50  tff(c_10, plain, (![C_10, B_9, A_8]: (~v1_xboole_0(C_10) | ~m1_subset_1(B_9, k1_zfmisc_1(C_10)) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.43/1.50  tff(c_430, plain, (![A_224, A_225, B_226]: (~v1_xboole_0(u1_struct_0(A_224)) | ~r2_hidden(A_225, k1_connsp_2(A_224, B_226)) | ~m1_subset_1(B_226, u1_struct_0(A_224)) | ~l1_pre_topc(A_224) | ~v2_pre_topc(A_224) | v2_struct_0(A_224))), inference(resolution, [status(thm)], [c_392, c_10])).
% 3.43/1.50  tff(c_450, plain, (![A_227, B_228]: (~v1_xboole_0(u1_struct_0(A_227)) | ~m1_subset_1(B_228, u1_struct_0(A_227)) | ~l1_pre_topc(A_227) | ~v2_pre_topc(A_227) | v2_struct_0(A_227))), inference(resolution, [status(thm)], [c_20, c_430])).
% 3.43/1.50  tff(c_456, plain, (~v1_xboole_0(u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_46, c_450])).
% 3.43/1.50  tff(c_460, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_67, c_325, c_456])).
% 3.43/1.50  tff(c_462, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_460])).
% 3.43/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.50  
% 3.43/1.50  Inference rules
% 3.43/1.50  ----------------------
% 3.43/1.50  #Ref     : 0
% 3.43/1.50  #Sup     : 65
% 3.43/1.50  #Fact    : 0
% 3.43/1.50  #Define  : 0
% 3.43/1.50  #Split   : 9
% 3.43/1.50  #Chain   : 0
% 3.43/1.50  #Close   : 0
% 3.43/1.50  
% 3.43/1.50  Ordering : KBO
% 3.43/1.50  
% 3.43/1.50  Simplification rules
% 3.43/1.50  ----------------------
% 3.43/1.50  #Subsume      : 10
% 3.43/1.50  #Demod        : 54
% 3.43/1.50  #Tautology    : 3
% 3.43/1.50  #SimpNegUnit  : 22
% 3.43/1.50  #BackRed      : 0
% 3.43/1.50  
% 3.43/1.50  #Partial instantiations: 0
% 3.43/1.50  #Strategies tried      : 1
% 3.43/1.50  
% 3.43/1.50  Timing (in seconds)
% 3.43/1.50  ----------------------
% 3.61/1.51  Preprocessing        : 0.37
% 3.61/1.51  Parsing              : 0.20
% 3.61/1.51  CNF conversion       : 0.04
% 3.61/1.51  Main loop            : 0.35
% 3.61/1.51  Inferencing          : 0.14
% 3.61/1.51  Reduction            : 0.10
% 3.61/1.51  Demodulation         : 0.06
% 3.61/1.51  BG Simplification    : 0.02
% 3.61/1.51  Subsumption          : 0.07
% 3.61/1.51  Abstraction          : 0.01
% 3.61/1.51  MUC search           : 0.00
% 3.61/1.51  Cooper               : 0.00
% 3.61/1.51  Total                : 0.77
% 3.61/1.51  Index Insertion      : 0.00
% 3.61/1.51  Index Deletion       : 0.00
% 3.61/1.51  Index Matching       : 0.00
% 3.61/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
