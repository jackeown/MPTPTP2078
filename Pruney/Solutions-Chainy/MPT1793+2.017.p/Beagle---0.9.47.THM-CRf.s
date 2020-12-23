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
% DateTime   : Thu Dec  3 10:27:56 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 359 expanded)
%              Number of leaves         :   39 ( 152 expanded)
%              Depth                    :   14
%              Number of atoms          :  280 (1600 expanded)
%              Number of equality atoms :    1 (   3 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k7_tmap_1 > k6_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(f_212,negated_conjecture,(
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

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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

tff(f_148,axiom,(
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

tff(f_114,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_funct_1(k7_tmap_1(A,B))
        & v1_funct_2(k7_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B)))
        & m1_subset_1(k7_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B))))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).

tff(f_130,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( ~ v2_struct_0(k6_tmap_1(A,B))
        & v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_tmap_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_188,axiom,(
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

tff(f_68,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_46,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_58,plain,(
    ! [B_108,A_109] :
      ( l1_pre_topc(B_108)
      | ~ m1_pre_topc(B_108,A_109)
      | ~ l1_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_61,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_58])).

tff(c_64,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_61])).

tff(c_10,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_167,plain,(
    ! [C_134,A_135,B_136] :
      ( m1_subset_1(C_134,u1_struct_0(A_135))
      | ~ m1_subset_1(C_134,u1_struct_0(B_136))
      | ~ m1_pre_topc(B_136,A_135)
      | v2_struct_0(B_136)
      | ~ l1_pre_topc(A_135)
      | v2_struct_0(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_169,plain,(
    ! [A_135] :
      ( m1_subset_1('#skF_5',u1_struct_0(A_135))
      | ~ m1_pre_topc('#skF_4',A_135)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_135)
      | v2_struct_0(A_135) ) ),
    inference(resolution,[status(thm)],[c_42,c_167])).

tff(c_172,plain,(
    ! [A_135] :
      ( m1_subset_1('#skF_5',u1_struct_0(A_135))
      | ~ m1_pre_topc('#skF_4',A_135)
      | ~ l1_pre_topc(A_135)
      | v2_struct_0(A_135) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_169])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | v1_xboole_0(B_7)
      | ~ m1_subset_1(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_44,plain,(
    r1_xboole_0(u1_struct_0('#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_69,plain,(
    ! [A_117,B_118,C_119] :
      ( ~ r1_xboole_0(A_117,B_118)
      | ~ r2_hidden(C_119,B_118)
      | ~ r2_hidden(C_119,A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_73,plain,(
    ! [C_120] :
      ( ~ r2_hidden(C_120,'#skF_3')
      | ~ r2_hidden(C_120,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_44,c_69])).

tff(c_86,plain,(
    ! [A_6] :
      ( ~ r2_hidden(A_6,'#skF_3')
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_6,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_8,c_73])).

tff(c_103,plain,(
    ! [A_122] :
      ( ~ r2_hidden(A_122,'#skF_3')
      | ~ m1_subset_1(A_122,u1_struct_0('#skF_4')) ) ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_107,plain,(
    ~ r2_hidden('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_103])).

tff(c_54,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_36,plain,(
    ! [A_26,B_30,C_32] :
      ( r1_tmap_1(A_26,k6_tmap_1(A_26,B_30),k7_tmap_1(A_26,B_30),C_32)
      | r2_hidden(C_32,B_30)
      | ~ m1_subset_1(C_32,u1_struct_0(A_26))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_26,plain,(
    ! [A_22,B_23] :
      ( v1_funct_2(k7_tmap_1(A_22,B_23),u1_struct_0(A_22),u1_struct_0(k6_tmap_1(A_22,B_23)))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_113,plain,(
    ! [A_123,B_124] :
      ( ~ v2_struct_0(k6_tmap_1(A_123,B_124))
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123)
      | ~ v2_pre_topc(A_123)
      | v2_struct_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_116,plain,
    ( ~ v2_struct_0(k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_113])).

tff(c_119,plain,
    ( ~ v2_struct_0(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_116])).

tff(c_120,plain,(
    ~ v2_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_119])).

tff(c_143,plain,(
    ! [A_128,B_129] :
      ( v2_pre_topc(k6_tmap_1(A_128,B_129))
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128)
      | ~ v2_pre_topc(A_128)
      | v2_struct_0(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_146,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_143])).

tff(c_149,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_146])).

tff(c_150,plain,(
    v2_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_149])).

tff(c_159,plain,(
    ! [A_132,B_133] :
      ( l1_pre_topc(k6_tmap_1(A_132,B_133))
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132)
      | v2_struct_0(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_162,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_159])).

tff(c_165,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_162])).

tff(c_166,plain,(
    l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_165])).

tff(c_135,plain,(
    ! [A_126,B_127] :
      ( v1_funct_1(k7_tmap_1(A_126,B_127))
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_pre_topc(A_126)
      | ~ v2_pre_topc(A_126)
      | v2_struct_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_138,plain,
    ( v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_135])).

tff(c_141,plain,
    ( v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_138])).

tff(c_142,plain,(
    v1_funct_1(k7_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_141])).

tff(c_24,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(k7_tmap_1(A_22,B_23),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_22),u1_struct_0(k6_tmap_1(A_22,B_23)))))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_196,plain,(
    ! [C_151,B_148,D_150,F_149,A_147] :
      ( r1_tmap_1(D_150,A_147,k2_tmap_1(B_148,A_147,C_151,D_150),F_149)
      | ~ r1_tmap_1(B_148,A_147,C_151,F_149)
      | ~ m1_subset_1(F_149,u1_struct_0(D_150))
      | ~ m1_subset_1(F_149,u1_struct_0(B_148))
      | ~ m1_pre_topc(D_150,B_148)
      | v2_struct_0(D_150)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_148),u1_struct_0(A_147))))
      | ~ v1_funct_2(C_151,u1_struct_0(B_148),u1_struct_0(A_147))
      | ~ v1_funct_1(C_151)
      | ~ l1_pre_topc(B_148)
      | ~ v2_pre_topc(B_148)
      | v2_struct_0(B_148)
      | ~ l1_pre_topc(A_147)
      | ~ v2_pre_topc(A_147)
      | v2_struct_0(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_200,plain,(
    ! [D_152,A_153,B_154,F_155] :
      ( r1_tmap_1(D_152,k6_tmap_1(A_153,B_154),k2_tmap_1(A_153,k6_tmap_1(A_153,B_154),k7_tmap_1(A_153,B_154),D_152),F_155)
      | ~ r1_tmap_1(A_153,k6_tmap_1(A_153,B_154),k7_tmap_1(A_153,B_154),F_155)
      | ~ m1_subset_1(F_155,u1_struct_0(D_152))
      | ~ m1_subset_1(F_155,u1_struct_0(A_153))
      | ~ m1_pre_topc(D_152,A_153)
      | v2_struct_0(D_152)
      | ~ v1_funct_2(k7_tmap_1(A_153,B_154),u1_struct_0(A_153),u1_struct_0(k6_tmap_1(A_153,B_154)))
      | ~ v1_funct_1(k7_tmap_1(A_153,B_154))
      | ~ l1_pre_topc(k6_tmap_1(A_153,B_154))
      | ~ v2_pre_topc(k6_tmap_1(A_153,B_154))
      | v2_struct_0(k6_tmap_1(A_153,B_154))
      | ~ m1_subset_1(B_154,k1_zfmisc_1(u1_struct_0(A_153)))
      | ~ l1_pre_topc(A_153)
      | ~ v2_pre_topc(A_153)
      | v2_struct_0(A_153) ) ),
    inference(resolution,[status(thm)],[c_24,c_196])).

tff(c_40,plain,(
    ~ r1_tmap_1('#skF_4',k6_tmap_1('#skF_2','#skF_3'),k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_203,plain,
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
    inference(resolution,[status(thm)],[c_200,c_40])).

tff(c_206,plain,
    ( ~ r1_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_4')
    | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
    | v2_struct_0(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_150,c_166,c_142,c_46,c_42,c_203])).

tff(c_207,plain,
    ( ~ r1_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
    | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_120,c_48,c_206])).

tff(c_208,plain,(
    ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_207])).

tff(c_211,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_208])).

tff(c_214,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_211])).

tff(c_216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_214])).

tff(c_217,plain,
    ( ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
    | ~ r1_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_207])).

tff(c_219,plain,(
    ~ r1_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_217])).

tff(c_222,plain,
    ( r2_hidden('#skF_5','#skF_3')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_219])).

tff(c_225,plain,
    ( r2_hidden('#skF_5','#skF_3')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_222])).

tff(c_226,plain,(
    ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_107,c_225])).

tff(c_229,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_172,c_226])).

tff(c_232,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_229])).

tff(c_234,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_232])).

tff(c_235,plain,(
    ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_239,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_172,c_235])).

tff(c_242,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_239])).

tff(c_244,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_242])).

tff(c_245,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_14,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(u1_struct_0(A_12))
      | ~ l1_struct_0(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_248,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_245,c_14])).

tff(c_251,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_248])).

tff(c_254,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_251])).

tff(c_258,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_254])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:21:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.64/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.37  
% 2.64/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.37  %$ r1_tmap_1 > v1_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k7_tmap_1 > k6_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.64/1.37  
% 2.64/1.37  %Foreground sorts:
% 2.64/1.37  
% 2.64/1.37  
% 2.64/1.37  %Background operators:
% 2.64/1.37  
% 2.64/1.37  
% 2.64/1.37  %Foreground operators:
% 2.64/1.37  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.64/1.37  tff(k7_tmap_1, type, k7_tmap_1: ($i * $i) > $i).
% 2.64/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.64/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.64/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.64/1.37  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 2.64/1.37  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.64/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.64/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.64/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.64/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.64/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.64/1.37  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.64/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.64/1.37  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.64/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.64/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.64/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.64/1.37  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 2.64/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.64/1.37  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.64/1.37  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.64/1.37  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 2.64/1.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.64/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.64/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.64/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.64/1.37  
% 2.64/1.40  tff(f_212, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (r1_xboole_0(u1_struct_0(C), B) => (![D]: (m1_subset_1(D, u1_struct_0(C)) => r1_tmap_1(C, k6_tmap_1(A, B), k2_tmap_1(A, k6_tmap_1(A, B), k7_tmap_1(A, B), C), D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_tmap_1)).
% 2.64/1.40  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.64/1.40  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.64/1.40  tff(f_84, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 2.64/1.40  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.64/1.40  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.64/1.40  tff(f_148, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (~r2_hidden(C, B) => r1_tmap_1(A, k6_tmap_1(A, B), k7_tmap_1(A, B), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_tmap_1)).
% 2.64/1.40  tff(f_114, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_funct_1(k7_tmap_1(A, B)) & v1_funct_2(k7_tmap_1(A, B), u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))) & m1_subset_1(k7_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 2.64/1.40  tff(f_130, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((~v2_struct_0(k6_tmap_1(A, B)) & v1_pre_topc(k6_tmap_1(A, B))) & v2_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_tmap_1)).
% 2.64/1.40  tff(f_99, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 2.64/1.40  tff(f_188, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tmap_1)).
% 2.64/1.40  tff(f_68, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.64/1.40  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_212])).
% 2.64/1.40  tff(c_46, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_212])).
% 2.64/1.40  tff(c_58, plain, (![B_108, A_109]: (l1_pre_topc(B_108) | ~m1_pre_topc(B_108, A_109) | ~l1_pre_topc(A_109))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.64/1.40  tff(c_61, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_46, c_58])).
% 2.64/1.40  tff(c_64, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_61])).
% 2.64/1.40  tff(c_10, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.64/1.40  tff(c_48, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_212])).
% 2.64/1.40  tff(c_56, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_212])).
% 2.64/1.40  tff(c_42, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_212])).
% 2.64/1.40  tff(c_167, plain, (![C_134, A_135, B_136]: (m1_subset_1(C_134, u1_struct_0(A_135)) | ~m1_subset_1(C_134, u1_struct_0(B_136)) | ~m1_pre_topc(B_136, A_135) | v2_struct_0(B_136) | ~l1_pre_topc(A_135) | v2_struct_0(A_135))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.64/1.40  tff(c_169, plain, (![A_135]: (m1_subset_1('#skF_5', u1_struct_0(A_135)) | ~m1_pre_topc('#skF_4', A_135) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_135) | v2_struct_0(A_135))), inference(resolution, [status(thm)], [c_42, c_167])).
% 2.64/1.40  tff(c_172, plain, (![A_135]: (m1_subset_1('#skF_5', u1_struct_0(A_135)) | ~m1_pre_topc('#skF_4', A_135) | ~l1_pre_topc(A_135) | v2_struct_0(A_135))), inference(negUnitSimplification, [status(thm)], [c_48, c_169])).
% 2.64/1.40  tff(c_8, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | v1_xboole_0(B_7) | ~m1_subset_1(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.64/1.40  tff(c_44, plain, (r1_xboole_0(u1_struct_0('#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_212])).
% 2.64/1.40  tff(c_69, plain, (![A_117, B_118, C_119]: (~r1_xboole_0(A_117, B_118) | ~r2_hidden(C_119, B_118) | ~r2_hidden(C_119, A_117))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.64/1.40  tff(c_73, plain, (![C_120]: (~r2_hidden(C_120, '#skF_3') | ~r2_hidden(C_120, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_44, c_69])).
% 2.64/1.40  tff(c_86, plain, (![A_6]: (~r2_hidden(A_6, '#skF_3') | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(A_6, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_8, c_73])).
% 2.64/1.40  tff(c_103, plain, (![A_122]: (~r2_hidden(A_122, '#skF_3') | ~m1_subset_1(A_122, u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_86])).
% 2.64/1.40  tff(c_107, plain, (~r2_hidden('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_103])).
% 2.64/1.40  tff(c_54, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_212])).
% 2.64/1.40  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_212])).
% 2.64/1.40  tff(c_36, plain, (![A_26, B_30, C_32]: (r1_tmap_1(A_26, k6_tmap_1(A_26, B_30), k7_tmap_1(A_26, B_30), C_32) | r2_hidden(C_32, B_30) | ~m1_subset_1(C_32, u1_struct_0(A_26)) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_148])).
% 2.64/1.40  tff(c_26, plain, (![A_22, B_23]: (v1_funct_2(k7_tmap_1(A_22, B_23), u1_struct_0(A_22), u1_struct_0(k6_tmap_1(A_22, B_23))) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.64/1.40  tff(c_113, plain, (![A_123, B_124]: (~v2_struct_0(k6_tmap_1(A_123, B_124)) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123) | ~v2_pre_topc(A_123) | v2_struct_0(A_123))), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.64/1.40  tff(c_116, plain, (~v2_struct_0(k6_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_113])).
% 2.64/1.40  tff(c_119, plain, (~v2_struct_0(k6_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_116])).
% 2.64/1.40  tff(c_120, plain, (~v2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_56, c_119])).
% 2.64/1.40  tff(c_143, plain, (![A_128, B_129]: (v2_pre_topc(k6_tmap_1(A_128, B_129)) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc(A_128) | ~v2_pre_topc(A_128) | v2_struct_0(A_128))), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.64/1.40  tff(c_146, plain, (v2_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_143])).
% 2.64/1.40  tff(c_149, plain, (v2_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_146])).
% 2.64/1.40  tff(c_150, plain, (v2_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_56, c_149])).
% 2.64/1.40  tff(c_159, plain, (![A_132, B_133]: (l1_pre_topc(k6_tmap_1(A_132, B_133)) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132) | v2_struct_0(A_132))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.64/1.40  tff(c_162, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_159])).
% 2.64/1.40  tff(c_165, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_162])).
% 2.64/1.40  tff(c_166, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_56, c_165])).
% 2.64/1.40  tff(c_135, plain, (![A_126, B_127]: (v1_funct_1(k7_tmap_1(A_126, B_127)) | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_pre_topc(A_126) | ~v2_pre_topc(A_126) | v2_struct_0(A_126))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.64/1.40  tff(c_138, plain, (v1_funct_1(k7_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_135])).
% 2.64/1.40  tff(c_141, plain, (v1_funct_1(k7_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_138])).
% 2.64/1.40  tff(c_142, plain, (v1_funct_1(k7_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_56, c_141])).
% 2.64/1.40  tff(c_24, plain, (![A_22, B_23]: (m1_subset_1(k7_tmap_1(A_22, B_23), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_22), u1_struct_0(k6_tmap_1(A_22, B_23))))) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.64/1.40  tff(c_196, plain, (![C_151, B_148, D_150, F_149, A_147]: (r1_tmap_1(D_150, A_147, k2_tmap_1(B_148, A_147, C_151, D_150), F_149) | ~r1_tmap_1(B_148, A_147, C_151, F_149) | ~m1_subset_1(F_149, u1_struct_0(D_150)) | ~m1_subset_1(F_149, u1_struct_0(B_148)) | ~m1_pre_topc(D_150, B_148) | v2_struct_0(D_150) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_148), u1_struct_0(A_147)))) | ~v1_funct_2(C_151, u1_struct_0(B_148), u1_struct_0(A_147)) | ~v1_funct_1(C_151) | ~l1_pre_topc(B_148) | ~v2_pre_topc(B_148) | v2_struct_0(B_148) | ~l1_pre_topc(A_147) | ~v2_pre_topc(A_147) | v2_struct_0(A_147))), inference(cnfTransformation, [status(thm)], [f_188])).
% 2.64/1.40  tff(c_200, plain, (![D_152, A_153, B_154, F_155]: (r1_tmap_1(D_152, k6_tmap_1(A_153, B_154), k2_tmap_1(A_153, k6_tmap_1(A_153, B_154), k7_tmap_1(A_153, B_154), D_152), F_155) | ~r1_tmap_1(A_153, k6_tmap_1(A_153, B_154), k7_tmap_1(A_153, B_154), F_155) | ~m1_subset_1(F_155, u1_struct_0(D_152)) | ~m1_subset_1(F_155, u1_struct_0(A_153)) | ~m1_pre_topc(D_152, A_153) | v2_struct_0(D_152) | ~v1_funct_2(k7_tmap_1(A_153, B_154), u1_struct_0(A_153), u1_struct_0(k6_tmap_1(A_153, B_154))) | ~v1_funct_1(k7_tmap_1(A_153, B_154)) | ~l1_pre_topc(k6_tmap_1(A_153, B_154)) | ~v2_pre_topc(k6_tmap_1(A_153, B_154)) | v2_struct_0(k6_tmap_1(A_153, B_154)) | ~m1_subset_1(B_154, k1_zfmisc_1(u1_struct_0(A_153))) | ~l1_pre_topc(A_153) | ~v2_pre_topc(A_153) | v2_struct_0(A_153))), inference(resolution, [status(thm)], [c_24, c_196])).
% 2.64/1.40  tff(c_40, plain, (~r1_tmap_1('#skF_4', k6_tmap_1('#skF_2', '#skF_3'), k2_tmap_1('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3'), '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_212])).
% 2.64/1.40  tff(c_203, plain, (~r1_tmap_1('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3'), '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k7_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | ~v2_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | v2_struct_0(k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_200, c_40])).
% 2.64/1.40  tff(c_206, plain, (~r1_tmap_1('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3'), '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | v2_struct_0('#skF_4') | ~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))) | v2_struct_0(k6_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_150, c_166, c_142, c_46, c_42, c_203])).
% 2.64/1.40  tff(c_207, plain, (~r1_tmap_1('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3'), '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | ~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_56, c_120, c_48, c_206])).
% 2.64/1.40  tff(c_208, plain, (~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_207])).
% 2.64/1.40  tff(c_211, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_208])).
% 2.64/1.40  tff(c_214, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_211])).
% 2.64/1.40  tff(c_216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_214])).
% 2.64/1.40  tff(c_217, plain, (~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | ~r1_tmap_1('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3'), '#skF_5')), inference(splitRight, [status(thm)], [c_207])).
% 2.64/1.40  tff(c_219, plain, (~r1_tmap_1('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3'), '#skF_5')), inference(splitLeft, [status(thm)], [c_217])).
% 2.64/1.40  tff(c_222, plain, (r2_hidden('#skF_5', '#skF_3') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_36, c_219])).
% 2.64/1.40  tff(c_225, plain, (r2_hidden('#skF_5', '#skF_3') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_222])).
% 2.64/1.40  tff(c_226, plain, (~m1_subset_1('#skF_5', u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_107, c_225])).
% 2.64/1.40  tff(c_229, plain, (~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_172, c_226])).
% 2.64/1.40  tff(c_232, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_229])).
% 2.64/1.40  tff(c_234, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_232])).
% 2.64/1.40  tff(c_235, plain, (~m1_subset_1('#skF_5', u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_217])).
% 2.64/1.40  tff(c_239, plain, (~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_172, c_235])).
% 2.64/1.40  tff(c_242, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_239])).
% 2.64/1.40  tff(c_244, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_242])).
% 2.64/1.40  tff(c_245, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_86])).
% 2.64/1.40  tff(c_14, plain, (![A_12]: (~v1_xboole_0(u1_struct_0(A_12)) | ~l1_struct_0(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.64/1.40  tff(c_248, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_245, c_14])).
% 2.64/1.40  tff(c_251, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_48, c_248])).
% 2.64/1.40  tff(c_254, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_10, c_251])).
% 2.64/1.40  tff(c_258, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_254])).
% 2.64/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.40  
% 2.64/1.40  Inference rules
% 2.64/1.40  ----------------------
% 2.64/1.40  #Ref     : 0
% 2.64/1.40  #Sup     : 29
% 2.64/1.40  #Fact    : 0
% 2.64/1.40  #Define  : 0
% 2.64/1.40  #Split   : 7
% 2.64/1.40  #Chain   : 0
% 2.64/1.40  #Close   : 0
% 2.64/1.40  
% 2.64/1.40  Ordering : KBO
% 2.64/1.40  
% 2.64/1.40  Simplification rules
% 2.64/1.40  ----------------------
% 2.64/1.40  #Subsume      : 4
% 2.64/1.40  #Demod        : 35
% 2.64/1.40  #Tautology    : 2
% 2.64/1.40  #SimpNegUnit  : 14
% 2.64/1.40  #BackRed      : 0
% 2.64/1.40  
% 2.64/1.40  #Partial instantiations: 0
% 2.64/1.40  #Strategies tried      : 1
% 2.64/1.40  
% 2.64/1.40  Timing (in seconds)
% 2.64/1.40  ----------------------
% 2.64/1.40  Preprocessing        : 0.38
% 2.64/1.40  Parsing              : 0.22
% 2.64/1.40  CNF conversion       : 0.04
% 2.64/1.40  Main loop            : 0.23
% 2.64/1.40  Inferencing          : 0.09
% 2.64/1.40  Reduction            : 0.06
% 2.64/1.40  Demodulation         : 0.04
% 2.64/1.40  BG Simplification    : 0.02
% 2.64/1.40  Subsumption          : 0.05
% 2.64/1.40  Abstraction          : 0.01
% 2.64/1.40  MUC search           : 0.00
% 2.64/1.40  Cooper               : 0.00
% 2.64/1.40  Total                : 0.66
% 2.64/1.40  Index Insertion      : 0.00
% 2.64/1.40  Index Deletion       : 0.00
% 2.64/1.40  Index Matching       : 0.00
% 2.64/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
