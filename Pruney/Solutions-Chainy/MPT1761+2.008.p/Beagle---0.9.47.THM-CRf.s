%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:09 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 133 expanded)
%              Number of leaves         :   39 (  66 expanded)
%              Depth                    :   12
%              Number of atoms          :  194 ( 665 expanded)
%              Number of equality atoms :   26 (  55 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_164,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(D),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                       => ( m1_pre_topc(C,D)
                         => ! [F] :
                              ( m1_subset_1(F,u1_struct_0(D))
                             => ( r2_hidden(F,u1_struct_0(C))
                               => k3_funct_2(u1_struct_0(D),u1_struct_0(B),E,F) = k1_funct_1(k3_tmap_1(A,B,D,C,E),F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tmap_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_120,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_113,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ( m1_pre_topc(D,C)
                       => k3_tmap_1(A,B,C,D,E) = k2_partfun1(u1_struct_0(C),u1_struct_0(B),E,u1_struct_0(D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,B)
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_funct_1)).

tff(c_36,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_34,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_32,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_30,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_38,plain,(
    m1_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_68,plain,(
    ! [B_123,A_124] :
      ( l1_pre_topc(B_123)
      | ~ m1_pre_topc(B_123,A_124)
      | ~ l1_pre_topc(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_71,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_68])).

tff(c_80,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_71])).

tff(c_28,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_126,plain,(
    ! [A_142,B_143,C_144,D_145] :
      ( k3_funct_2(A_142,B_143,C_144,D_145) = k1_funct_1(C_144,D_145)
      | ~ m1_subset_1(D_145,A_142)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143)))
      | ~ v1_funct_2(C_144,A_142,B_143)
      | ~ v1_funct_1(C_144)
      | v1_xboole_0(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_135,plain,(
    ! [B_143,C_144] :
      ( k3_funct_2(u1_struct_0('#skF_5'),B_143,C_144,'#skF_7') = k1_funct_1(C_144,'#skF_7')
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),B_143)))
      | ~ v1_funct_2(C_144,u1_struct_0('#skF_5'),B_143)
      | ~ v1_funct_1(C_144)
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_28,c_126])).

tff(c_145,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_100,plain,(
    ! [B_129,A_130] :
      ( m1_subset_1(u1_struct_0(B_129),k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ m1_pre_topc(B_129,A_130)
      | ~ l1_pre_topc(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_6,plain,(
    ! [B_7,A_5] :
      ( v1_xboole_0(B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_5))
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_108,plain,(
    ! [B_129,A_130] :
      ( v1_xboole_0(u1_struct_0(B_129))
      | ~ v1_xboole_0(u1_struct_0(A_130))
      | ~ m1_pre_topc(B_129,A_130)
      | ~ l1_pre_topc(A_130) ) ),
    inference(resolution,[status(thm)],[c_100,c_6])).

tff(c_147,plain,(
    ! [B_129] :
      ( v1_xboole_0(u1_struct_0(B_129))
      | ~ m1_pre_topc(B_129,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_145,c_108])).

tff(c_152,plain,(
    ! [B_147] :
      ( v1_xboole_0(u1_struct_0(B_147))
      | ~ m1_pre_topc(B_147,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_147])).

tff(c_26,plain,(
    r2_hidden('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_58,plain,(
    ! [B_120,A_121] :
      ( ~ r2_hidden(B_120,A_121)
      | ~ v1_xboole_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_26,c_58])).

tff(c_157,plain,(
    ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_152,c_62])).

tff(c_162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_157])).

tff(c_165,plain,(
    ! [B_148,C_149] :
      ( k3_funct_2(u1_struct_0('#skF_5'),B_148,C_149,'#skF_7') = k1_funct_1(C_149,'#skF_7')
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),B_148)))
      | ~ v1_funct_2(C_149,u1_struct_0('#skF_5'),B_148)
      | ~ v1_funct_1(C_149) ) ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_168,plain,
    ( k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_7') = k1_funct_1('#skF_6','#skF_7')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_32,c_165])).

tff(c_171,plain,(
    k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_7') = k1_funct_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_168])).

tff(c_24,plain,(
    k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_7') != k1_funct_1(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_172,plain,(
    k1_funct_1(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_7') != k1_funct_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_24])).

tff(c_10,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_92,plain,(
    ! [B_127,A_128] :
      ( v1_relat_1(B_127)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(A_128))
      | ~ v1_relat_1(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_95,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_32,c_92])).

tff(c_98,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_95])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_54,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_42,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_48,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_46,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_120,plain,(
    ! [A_138,B_139,C_140,D_141] :
      ( k2_partfun1(A_138,B_139,C_140,D_141) = k7_relat_1(C_140,D_141)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139)))
      | ~ v1_funct_1(C_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_122,plain,(
    ! [D_141] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',D_141) = k7_relat_1('#skF_6',D_141)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_32,c_120])).

tff(c_125,plain,(
    ! [D_141] : k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',D_141) = k7_relat_1('#skF_6',D_141) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_122])).

tff(c_177,plain,(
    ! [E_152,A_154,D_153,B_151,C_150] :
      ( k3_tmap_1(A_154,B_151,C_150,D_153,E_152) = k2_partfun1(u1_struct_0(C_150),u1_struct_0(B_151),E_152,u1_struct_0(D_153))
      | ~ m1_pre_topc(D_153,C_150)
      | ~ m1_subset_1(E_152,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_150),u1_struct_0(B_151))))
      | ~ v1_funct_2(E_152,u1_struct_0(C_150),u1_struct_0(B_151))
      | ~ v1_funct_1(E_152)
      | ~ m1_pre_topc(D_153,A_154)
      | ~ m1_pre_topc(C_150,A_154)
      | ~ l1_pre_topc(B_151)
      | ~ v2_pre_topc(B_151)
      | v2_struct_0(B_151)
      | ~ l1_pre_topc(A_154)
      | ~ v2_pre_topc(A_154)
      | v2_struct_0(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_179,plain,(
    ! [A_154,D_153] :
      ( k3_tmap_1(A_154,'#skF_3','#skF_5',D_153,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_153))
      | ~ m1_pre_topc(D_153,'#skF_5')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_153,A_154)
      | ~ m1_pre_topc('#skF_5',A_154)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_154)
      | ~ v2_pre_topc(A_154)
      | v2_struct_0(A_154) ) ),
    inference(resolution,[status(thm)],[c_32,c_177])).

tff(c_182,plain,(
    ! [D_153,A_154] :
      ( k7_relat_1('#skF_6',u1_struct_0(D_153)) = k3_tmap_1(A_154,'#skF_3','#skF_5',D_153,'#skF_6')
      | ~ m1_pre_topc(D_153,'#skF_5')
      | ~ m1_pre_topc(D_153,A_154)
      | ~ m1_pre_topc('#skF_5',A_154)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_154)
      | ~ v2_pre_topc(A_154)
      | v2_struct_0(A_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_36,c_34,c_125,c_179])).

tff(c_184,plain,(
    ! [D_155,A_156] :
      ( k7_relat_1('#skF_6',u1_struct_0(D_155)) = k3_tmap_1(A_156,'#skF_3','#skF_5',D_155,'#skF_6')
      | ~ m1_pre_topc(D_155,'#skF_5')
      | ~ m1_pre_topc(D_155,A_156)
      | ~ m1_pre_topc('#skF_5',A_156)
      | ~ l1_pre_topc(A_156)
      | ~ v2_pre_topc(A_156)
      | v2_struct_0(A_156) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_182])).

tff(c_190,plain,
    ( k7_relat_1('#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_184])).

tff(c_201,plain,
    ( k7_relat_1('#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_38,c_30,c_190])).

tff(c_202,plain,(
    k7_relat_1('#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_201])).

tff(c_12,plain,(
    ! [C_15,B_14,A_13] :
      ( k1_funct_1(k7_relat_1(C_15,B_14),A_13) = k1_funct_1(C_15,A_13)
      | ~ r2_hidden(A_13,B_14)
      | ~ v1_funct_1(C_15)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_206,plain,(
    ! [A_13] :
      ( k1_funct_1(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),A_13) = k1_funct_1('#skF_6',A_13)
      | ~ r2_hidden(A_13,u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_12])).

tff(c_215,plain,(
    ! [A_157] :
      ( k1_funct_1(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),A_157) = k1_funct_1('#skF_6',A_157)
      | ~ r2_hidden(A_157,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_36,c_206])).

tff(c_222,plain,(
    k1_funct_1(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_7') = k1_funct_1('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_26,c_215])).

tff(c_229,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_222])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:56:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.32  
% 2.53/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.33  %$ v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 2.53/1.33  
% 2.53/1.33  %Foreground sorts:
% 2.53/1.33  
% 2.53/1.33  
% 2.53/1.33  %Background operators:
% 2.53/1.33  
% 2.53/1.33  
% 2.53/1.33  %Foreground operators:
% 2.53/1.33  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.53/1.33  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 2.53/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.53/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.53/1.33  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.53/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.53/1.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.53/1.33  tff('#skF_7', type, '#skF_7': $i).
% 2.53/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.53/1.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.53/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.53/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.53/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.53/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.53/1.33  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.53/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.53/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.53/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.53/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.33  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.53/1.33  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.53/1.33  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.53/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.53/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.53/1.33  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.53/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.53/1.33  
% 2.53/1.34  tff(f_164, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (r2_hidden(F, u1_struct_0(C)) => (k3_funct_2(u1_struct_0(D), u1_struct_0(B), E, F) = k1_funct_1(k3_tmap_1(A, B, D, C, E), F)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_tmap_1)).
% 2.53/1.34  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.53/1.34  tff(f_74, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.53/1.34  tff(f_120, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.53/1.34  tff(f_38, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.53/1.34  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.53/1.34  tff(f_47, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.53/1.34  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.53/1.34  tff(f_61, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.53/1.34  tff(f_113, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 2.53/1.34  tff(f_55, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, B) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_funct_1)).
% 2.53/1.34  tff(c_36, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.53/1.34  tff(c_34, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.53/1.34  tff(c_32, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.53/1.34  tff(c_30, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.53/1.34  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.53/1.34  tff(c_38, plain, (m1_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.53/1.34  tff(c_68, plain, (![B_123, A_124]: (l1_pre_topc(B_123) | ~m1_pre_topc(B_123, A_124) | ~l1_pre_topc(A_124))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.53/1.34  tff(c_71, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_68])).
% 2.53/1.34  tff(c_80, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_71])).
% 2.53/1.34  tff(c_28, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.53/1.34  tff(c_126, plain, (![A_142, B_143, C_144, D_145]: (k3_funct_2(A_142, B_143, C_144, D_145)=k1_funct_1(C_144, D_145) | ~m1_subset_1(D_145, A_142) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))) | ~v1_funct_2(C_144, A_142, B_143) | ~v1_funct_1(C_144) | v1_xboole_0(A_142))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.53/1.34  tff(c_135, plain, (![B_143, C_144]: (k3_funct_2(u1_struct_0('#skF_5'), B_143, C_144, '#skF_7')=k1_funct_1(C_144, '#skF_7') | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), B_143))) | ~v1_funct_2(C_144, u1_struct_0('#skF_5'), B_143) | ~v1_funct_1(C_144) | v1_xboole_0(u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_28, c_126])).
% 2.53/1.34  tff(c_145, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_135])).
% 2.53/1.34  tff(c_100, plain, (![B_129, A_130]: (m1_subset_1(u1_struct_0(B_129), k1_zfmisc_1(u1_struct_0(A_130))) | ~m1_pre_topc(B_129, A_130) | ~l1_pre_topc(A_130))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.53/1.34  tff(c_6, plain, (![B_7, A_5]: (v1_xboole_0(B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_5)) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.53/1.34  tff(c_108, plain, (![B_129, A_130]: (v1_xboole_0(u1_struct_0(B_129)) | ~v1_xboole_0(u1_struct_0(A_130)) | ~m1_pre_topc(B_129, A_130) | ~l1_pre_topc(A_130))), inference(resolution, [status(thm)], [c_100, c_6])).
% 2.53/1.34  tff(c_147, plain, (![B_129]: (v1_xboole_0(u1_struct_0(B_129)) | ~m1_pre_topc(B_129, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_145, c_108])).
% 2.53/1.34  tff(c_152, plain, (![B_147]: (v1_xboole_0(u1_struct_0(B_147)) | ~m1_pre_topc(B_147, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_147])).
% 2.53/1.34  tff(c_26, plain, (r2_hidden('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.53/1.34  tff(c_58, plain, (![B_120, A_121]: (~r2_hidden(B_120, A_121) | ~v1_xboole_0(A_121))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.53/1.34  tff(c_62, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_58])).
% 2.53/1.34  tff(c_157, plain, (~m1_pre_topc('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_152, c_62])).
% 2.53/1.34  tff(c_162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_157])).
% 2.53/1.34  tff(c_165, plain, (![B_148, C_149]: (k3_funct_2(u1_struct_0('#skF_5'), B_148, C_149, '#skF_7')=k1_funct_1(C_149, '#skF_7') | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), B_148))) | ~v1_funct_2(C_149, u1_struct_0('#skF_5'), B_148) | ~v1_funct_1(C_149))), inference(splitRight, [status(thm)], [c_135])).
% 2.53/1.34  tff(c_168, plain, (k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_7')=k1_funct_1('#skF_6', '#skF_7') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_32, c_165])).
% 2.53/1.34  tff(c_171, plain, (k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_7')=k1_funct_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_168])).
% 2.53/1.34  tff(c_24, plain, (k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_7')!=k1_funct_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.53/1.34  tff(c_172, plain, (k1_funct_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_171, c_24])).
% 2.53/1.34  tff(c_10, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.53/1.34  tff(c_92, plain, (![B_127, A_128]: (v1_relat_1(B_127) | ~m1_subset_1(B_127, k1_zfmisc_1(A_128)) | ~v1_relat_1(A_128))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.53/1.34  tff(c_95, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_32, c_92])).
% 2.53/1.34  tff(c_98, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_95])).
% 2.53/1.34  tff(c_56, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.53/1.34  tff(c_54, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.53/1.34  tff(c_42, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.53/1.34  tff(c_50, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.53/1.34  tff(c_48, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.53/1.34  tff(c_46, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.53/1.34  tff(c_120, plain, (![A_138, B_139, C_140, D_141]: (k2_partfun1(A_138, B_139, C_140, D_141)=k7_relat_1(C_140, D_141) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))) | ~v1_funct_1(C_140))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.53/1.34  tff(c_122, plain, (![D_141]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', D_141)=k7_relat_1('#skF_6', D_141) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_32, c_120])).
% 2.53/1.34  tff(c_125, plain, (![D_141]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', D_141)=k7_relat_1('#skF_6', D_141))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_122])).
% 2.53/1.34  tff(c_177, plain, (![E_152, A_154, D_153, B_151, C_150]: (k3_tmap_1(A_154, B_151, C_150, D_153, E_152)=k2_partfun1(u1_struct_0(C_150), u1_struct_0(B_151), E_152, u1_struct_0(D_153)) | ~m1_pre_topc(D_153, C_150) | ~m1_subset_1(E_152, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_150), u1_struct_0(B_151)))) | ~v1_funct_2(E_152, u1_struct_0(C_150), u1_struct_0(B_151)) | ~v1_funct_1(E_152) | ~m1_pre_topc(D_153, A_154) | ~m1_pre_topc(C_150, A_154) | ~l1_pre_topc(B_151) | ~v2_pre_topc(B_151) | v2_struct_0(B_151) | ~l1_pre_topc(A_154) | ~v2_pre_topc(A_154) | v2_struct_0(A_154))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.53/1.34  tff(c_179, plain, (![A_154, D_153]: (k3_tmap_1(A_154, '#skF_3', '#skF_5', D_153, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_153)) | ~m1_pre_topc(D_153, '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_153, A_154) | ~m1_pre_topc('#skF_5', A_154) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_154) | ~v2_pre_topc(A_154) | v2_struct_0(A_154))), inference(resolution, [status(thm)], [c_32, c_177])).
% 2.53/1.34  tff(c_182, plain, (![D_153, A_154]: (k7_relat_1('#skF_6', u1_struct_0(D_153))=k3_tmap_1(A_154, '#skF_3', '#skF_5', D_153, '#skF_6') | ~m1_pre_topc(D_153, '#skF_5') | ~m1_pre_topc(D_153, A_154) | ~m1_pre_topc('#skF_5', A_154) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_154) | ~v2_pre_topc(A_154) | v2_struct_0(A_154))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_36, c_34, c_125, c_179])).
% 2.53/1.34  tff(c_184, plain, (![D_155, A_156]: (k7_relat_1('#skF_6', u1_struct_0(D_155))=k3_tmap_1(A_156, '#skF_3', '#skF_5', D_155, '#skF_6') | ~m1_pre_topc(D_155, '#skF_5') | ~m1_pre_topc(D_155, A_156) | ~m1_pre_topc('#skF_5', A_156) | ~l1_pre_topc(A_156) | ~v2_pre_topc(A_156) | v2_struct_0(A_156))), inference(negUnitSimplification, [status(thm)], [c_50, c_182])).
% 2.53/1.34  tff(c_190, plain, (k7_relat_1('#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6') | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_184])).
% 2.53/1.34  tff(c_201, plain, (k7_relat_1('#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_38, c_30, c_190])).
% 2.53/1.34  tff(c_202, plain, (k7_relat_1('#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_56, c_201])).
% 2.53/1.34  tff(c_12, plain, (![C_15, B_14, A_13]: (k1_funct_1(k7_relat_1(C_15, B_14), A_13)=k1_funct_1(C_15, A_13) | ~r2_hidden(A_13, B_14) | ~v1_funct_1(C_15) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.53/1.34  tff(c_206, plain, (![A_13]: (k1_funct_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), A_13)=k1_funct_1('#skF_6', A_13) | ~r2_hidden(A_13, u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_202, c_12])).
% 2.53/1.34  tff(c_215, plain, (![A_157]: (k1_funct_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), A_157)=k1_funct_1('#skF_6', A_157) | ~r2_hidden(A_157, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_36, c_206])).
% 2.53/1.34  tff(c_222, plain, (k1_funct_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_7')=k1_funct_1('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_26, c_215])).
% 2.53/1.34  tff(c_229, plain, $false, inference(negUnitSimplification, [status(thm)], [c_172, c_222])).
% 2.53/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.34  
% 2.53/1.34  Inference rules
% 2.53/1.34  ----------------------
% 2.53/1.34  #Ref     : 0
% 2.53/1.34  #Sup     : 32
% 2.53/1.34  #Fact    : 0
% 2.53/1.34  #Define  : 0
% 2.53/1.34  #Split   : 5
% 2.53/1.34  #Chain   : 0
% 2.53/1.34  #Close   : 0
% 2.53/1.34  
% 2.53/1.34  Ordering : KBO
% 2.53/1.34  
% 2.53/1.34  Simplification rules
% 2.53/1.34  ----------------------
% 2.53/1.34  #Subsume      : 0
% 2.53/1.34  #Demod        : 28
% 2.53/1.34  #Tautology    : 10
% 2.53/1.34  #SimpNegUnit  : 6
% 2.53/1.34  #BackRed      : 1
% 2.53/1.34  
% 2.53/1.34  #Partial instantiations: 0
% 2.53/1.34  #Strategies tried      : 1
% 2.53/1.34  
% 2.53/1.34  Timing (in seconds)
% 2.53/1.34  ----------------------
% 2.53/1.35  Preprocessing        : 0.36
% 2.53/1.35  Parsing              : 0.19
% 2.53/1.35  CNF conversion       : 0.03
% 2.53/1.35  Main loop            : 0.20
% 2.53/1.35  Inferencing          : 0.07
% 2.53/1.35  Reduction            : 0.07
% 2.53/1.35  Demodulation         : 0.05
% 2.53/1.35  BG Simplification    : 0.02
% 2.53/1.35  Subsumption          : 0.03
% 2.53/1.35  Abstraction          : 0.01
% 2.53/1.35  MUC search           : 0.00
% 2.53/1.35  Cooper               : 0.00
% 2.53/1.35  Total                : 0.60
% 2.53/1.35  Index Insertion      : 0.00
% 2.53/1.35  Index Deletion       : 0.00
% 2.53/1.35  Index Matching       : 0.00
% 2.53/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
