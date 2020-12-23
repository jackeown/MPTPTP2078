%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:08 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 130 expanded)
%              Number of leaves         :   38 (  65 expanded)
%              Depth                    :   13
%              Number of atoms          :  188 ( 659 expanded)
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

tff(f_159,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_tmap_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_108,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,B)
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_funct_1)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_115,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_24,plain,(
    r2_hidden('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_30,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_89,plain,(
    ! [C_123,A_124,B_125] :
      ( v1_relat_1(C_123)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_93,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_30,c_89])).

tff(c_34,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_52,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_36,plain,(
    m1_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_28,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_40,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_46,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_32,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_110,plain,(
    ! [A_133,B_134,C_135,D_136] :
      ( k2_partfun1(A_133,B_134,C_135,D_136) = k7_relat_1(C_135,D_136)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134)))
      | ~ v1_funct_1(C_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_112,plain,(
    ! [D_136] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',D_136) = k7_relat_1('#skF_6',D_136)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_30,c_110])).

tff(c_115,plain,(
    ! [D_136] : k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',D_136) = k7_relat_1('#skF_6',D_136) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_112])).

tff(c_135,plain,(
    ! [E_143,D_144,A_142,C_145,B_146] :
      ( k3_tmap_1(A_142,B_146,C_145,D_144,E_143) = k2_partfun1(u1_struct_0(C_145),u1_struct_0(B_146),E_143,u1_struct_0(D_144))
      | ~ m1_pre_topc(D_144,C_145)
      | ~ m1_subset_1(E_143,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_145),u1_struct_0(B_146))))
      | ~ v1_funct_2(E_143,u1_struct_0(C_145),u1_struct_0(B_146))
      | ~ v1_funct_1(E_143)
      | ~ m1_pre_topc(D_144,A_142)
      | ~ m1_pre_topc(C_145,A_142)
      | ~ l1_pre_topc(B_146)
      | ~ v2_pre_topc(B_146)
      | v2_struct_0(B_146)
      | ~ l1_pre_topc(A_142)
      | ~ v2_pre_topc(A_142)
      | v2_struct_0(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_137,plain,(
    ! [A_142,D_144] :
      ( k3_tmap_1(A_142,'#skF_3','#skF_5',D_144,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_144))
      | ~ m1_pre_topc(D_144,'#skF_5')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_144,A_142)
      | ~ m1_pre_topc('#skF_5',A_142)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_142)
      | ~ v2_pre_topc(A_142)
      | v2_struct_0(A_142) ) ),
    inference(resolution,[status(thm)],[c_30,c_135])).

tff(c_140,plain,(
    ! [D_144,A_142] :
      ( k7_relat_1('#skF_6',u1_struct_0(D_144)) = k3_tmap_1(A_142,'#skF_3','#skF_5',D_144,'#skF_6')
      | ~ m1_pre_topc(D_144,'#skF_5')
      | ~ m1_pre_topc(D_144,A_142)
      | ~ m1_pre_topc('#skF_5',A_142)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_142)
      | ~ v2_pre_topc(A_142)
      | v2_struct_0(A_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_34,c_32,c_115,c_137])).

tff(c_142,plain,(
    ! [D_147,A_148] :
      ( k7_relat_1('#skF_6',u1_struct_0(D_147)) = k3_tmap_1(A_148,'#skF_3','#skF_5',D_147,'#skF_6')
      | ~ m1_pre_topc(D_147,'#skF_5')
      | ~ m1_pre_topc(D_147,A_148)
      | ~ m1_pre_topc('#skF_5',A_148)
      | ~ l1_pre_topc(A_148)
      | ~ v2_pre_topc(A_148)
      | v2_struct_0(A_148) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_140])).

tff(c_144,plain,
    ( k7_relat_1('#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_142])).

tff(c_151,plain,
    ( k7_relat_1('#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_36,c_28,c_144])).

tff(c_152,plain,(
    k7_relat_1('#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_151])).

tff(c_8,plain,(
    ! [C_10,B_9,A_8] :
      ( k1_funct_1(k7_relat_1(C_10,B_9),A_8) = k1_funct_1(C_10,A_8)
      | ~ r2_hidden(A_8,B_9)
      | ~ v1_funct_1(C_10)
      | ~ v1_relat_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_164,plain,(
    ! [A_8] :
      ( k1_funct_1(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),A_8) = k1_funct_1('#skF_6',A_8)
      | ~ r2_hidden(A_8,u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_8])).

tff(c_173,plain,(
    ! [A_149] :
      ( k1_funct_1(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),A_149) = k1_funct_1('#skF_6',A_149)
      | ~ r2_hidden(A_149,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_34,c_164])).

tff(c_184,plain,(
    k1_funct_1(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_7') = k1_funct_1('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_24,c_173])).

tff(c_22,plain,(
    k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_7') != k1_funct_1(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_185,plain,(
    k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_7') != k1_funct_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_22])).

tff(c_65,plain,(
    ! [B_119,A_120] :
      ( l1_pre_topc(B_119)
      | ~ m1_pre_topc(B_119,A_120)
      | ~ l1_pre_topc(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_74,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_65])).

tff(c_81,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_74])).

tff(c_26,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_125,plain,(
    ! [A_138,B_139,C_140,D_141] :
      ( k3_funct_2(A_138,B_139,C_140,D_141) = k1_funct_1(C_140,D_141)
      | ~ m1_subset_1(D_141,A_138)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139)))
      | ~ v1_funct_2(C_140,A_138,B_139)
      | ~ v1_funct_1(C_140)
      | v1_xboole_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_134,plain,(
    ! [B_139,C_140] :
      ( k3_funct_2(u1_struct_0('#skF_5'),B_139,C_140,'#skF_7') = k1_funct_1(C_140,'#skF_7')
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),B_139)))
      | ~ v1_funct_2(C_140,u1_struct_0('#skF_5'),B_139)
      | ~ v1_funct_1(C_140)
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_26,c_125])).

tff(c_190,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_94,plain,(
    ! [B_126,A_127] :
      ( m1_subset_1(u1_struct_0(B_126),k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ m1_pre_topc(B_126,A_127)
      | ~ l1_pre_topc(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_6,plain,(
    ! [B_7,A_5] :
      ( v1_xboole_0(B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_5))
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_98,plain,(
    ! [B_126,A_127] :
      ( v1_xboole_0(u1_struct_0(B_126))
      | ~ v1_xboole_0(u1_struct_0(A_127))
      | ~ m1_pre_topc(B_126,A_127)
      | ~ l1_pre_topc(A_127) ) ),
    inference(resolution,[status(thm)],[c_94,c_6])).

tff(c_192,plain,(
    ! [B_126] :
      ( v1_xboole_0(u1_struct_0(B_126))
      | ~ m1_pre_topc(B_126,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_190,c_98])).

tff(c_196,plain,(
    ! [B_150] :
      ( v1_xboole_0(u1_struct_0(B_150))
      | ~ m1_pre_topc(B_150,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_192])).

tff(c_55,plain,(
    ! [B_116,A_117] :
      ( ~ r2_hidden(B_116,A_117)
      | ~ v1_xboole_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_24,c_55])).

tff(c_201,plain,(
    ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_196,c_59])).

tff(c_206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_201])).

tff(c_214,plain,(
    ! [B_151,C_152] :
      ( k3_funct_2(u1_struct_0('#skF_5'),B_151,C_152,'#skF_7') = k1_funct_1(C_152,'#skF_7')
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),B_151)))
      | ~ v1_funct_2(C_152,u1_struct_0('#skF_5'),B_151)
      | ~ v1_funct_1(C_152) ) ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_217,plain,
    ( k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_7') = k1_funct_1('#skF_6','#skF_7')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_30,c_214])).

tff(c_220,plain,(
    k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_7') = k1_funct_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_217])).

tff(c_222,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_185,c_220])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:28:11 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.29  
% 2.42/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.29  %$ v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 2.42/1.29  
% 2.42/1.29  %Foreground sorts:
% 2.42/1.29  
% 2.42/1.29  
% 2.42/1.29  %Background operators:
% 2.42/1.29  
% 2.42/1.29  
% 2.42/1.29  %Foreground operators:
% 2.42/1.29  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.42/1.29  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 2.42/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.42/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.42/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.42/1.29  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.42/1.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.42/1.29  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.42/1.29  tff('#skF_7', type, '#skF_7': $i).
% 2.42/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.42/1.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.42/1.29  tff('#skF_6', type, '#skF_6': $i).
% 2.42/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.42/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.42/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.42/1.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.42/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.42/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.42/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.42/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.42/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.42/1.30  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.42/1.30  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.42/1.30  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.42/1.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.42/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.42/1.30  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.42/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.42/1.30  
% 2.42/1.31  tff(f_159, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (r2_hidden(F, u1_struct_0(C)) => (k3_funct_2(u1_struct_0(D), u1_struct_0(B), E, F) = k1_funct_1(k3_tmap_1(A, B, D, C, E), F)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_tmap_1)).
% 2.42/1.31  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.42/1.31  tff(f_56, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.42/1.31  tff(f_108, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 2.42/1.31  tff(f_46, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, B) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_funct_1)).
% 2.42/1.31  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.42/1.31  tff(f_69, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.42/1.31  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.42/1.31  tff(f_38, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.42/1.31  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.42/1.31  tff(c_24, plain, (r2_hidden('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.42/1.31  tff(c_30, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.42/1.31  tff(c_89, plain, (![C_123, A_124, B_125]: (v1_relat_1(C_123) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.42/1.31  tff(c_93, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_30, c_89])).
% 2.42/1.31  tff(c_34, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.42/1.31  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.42/1.31  tff(c_52, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.42/1.31  tff(c_50, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.42/1.31  tff(c_36, plain, (m1_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.42/1.31  tff(c_28, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.42/1.31  tff(c_40, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.42/1.31  tff(c_48, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.42/1.31  tff(c_46, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.42/1.31  tff(c_44, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.42/1.31  tff(c_32, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.42/1.31  tff(c_110, plain, (![A_133, B_134, C_135, D_136]: (k2_partfun1(A_133, B_134, C_135, D_136)=k7_relat_1(C_135, D_136) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))) | ~v1_funct_1(C_135))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.42/1.31  tff(c_112, plain, (![D_136]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', D_136)=k7_relat_1('#skF_6', D_136) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_30, c_110])).
% 2.42/1.31  tff(c_115, plain, (![D_136]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', D_136)=k7_relat_1('#skF_6', D_136))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_112])).
% 2.42/1.31  tff(c_135, plain, (![E_143, D_144, A_142, C_145, B_146]: (k3_tmap_1(A_142, B_146, C_145, D_144, E_143)=k2_partfun1(u1_struct_0(C_145), u1_struct_0(B_146), E_143, u1_struct_0(D_144)) | ~m1_pre_topc(D_144, C_145) | ~m1_subset_1(E_143, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_145), u1_struct_0(B_146)))) | ~v1_funct_2(E_143, u1_struct_0(C_145), u1_struct_0(B_146)) | ~v1_funct_1(E_143) | ~m1_pre_topc(D_144, A_142) | ~m1_pre_topc(C_145, A_142) | ~l1_pre_topc(B_146) | ~v2_pre_topc(B_146) | v2_struct_0(B_146) | ~l1_pre_topc(A_142) | ~v2_pre_topc(A_142) | v2_struct_0(A_142))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.42/1.31  tff(c_137, plain, (![A_142, D_144]: (k3_tmap_1(A_142, '#skF_3', '#skF_5', D_144, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_144)) | ~m1_pre_topc(D_144, '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_144, A_142) | ~m1_pre_topc('#skF_5', A_142) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_142) | ~v2_pre_topc(A_142) | v2_struct_0(A_142))), inference(resolution, [status(thm)], [c_30, c_135])).
% 2.42/1.31  tff(c_140, plain, (![D_144, A_142]: (k7_relat_1('#skF_6', u1_struct_0(D_144))=k3_tmap_1(A_142, '#skF_3', '#skF_5', D_144, '#skF_6') | ~m1_pre_topc(D_144, '#skF_5') | ~m1_pre_topc(D_144, A_142) | ~m1_pre_topc('#skF_5', A_142) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_142) | ~v2_pre_topc(A_142) | v2_struct_0(A_142))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_34, c_32, c_115, c_137])).
% 2.42/1.31  tff(c_142, plain, (![D_147, A_148]: (k7_relat_1('#skF_6', u1_struct_0(D_147))=k3_tmap_1(A_148, '#skF_3', '#skF_5', D_147, '#skF_6') | ~m1_pre_topc(D_147, '#skF_5') | ~m1_pre_topc(D_147, A_148) | ~m1_pre_topc('#skF_5', A_148) | ~l1_pre_topc(A_148) | ~v2_pre_topc(A_148) | v2_struct_0(A_148))), inference(negUnitSimplification, [status(thm)], [c_48, c_140])).
% 2.42/1.31  tff(c_144, plain, (k7_relat_1('#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6') | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_142])).
% 2.42/1.31  tff(c_151, plain, (k7_relat_1('#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_36, c_28, c_144])).
% 2.42/1.31  tff(c_152, plain, (k7_relat_1('#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_54, c_151])).
% 2.42/1.31  tff(c_8, plain, (![C_10, B_9, A_8]: (k1_funct_1(k7_relat_1(C_10, B_9), A_8)=k1_funct_1(C_10, A_8) | ~r2_hidden(A_8, B_9) | ~v1_funct_1(C_10) | ~v1_relat_1(C_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.42/1.31  tff(c_164, plain, (![A_8]: (k1_funct_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), A_8)=k1_funct_1('#skF_6', A_8) | ~r2_hidden(A_8, u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_152, c_8])).
% 2.42/1.31  tff(c_173, plain, (![A_149]: (k1_funct_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), A_149)=k1_funct_1('#skF_6', A_149) | ~r2_hidden(A_149, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_34, c_164])).
% 2.42/1.31  tff(c_184, plain, (k1_funct_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_7')=k1_funct_1('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_24, c_173])).
% 2.42/1.31  tff(c_22, plain, (k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_7')!=k1_funct_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.42/1.31  tff(c_185, plain, (k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_7')!=k1_funct_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_184, c_22])).
% 2.42/1.31  tff(c_65, plain, (![B_119, A_120]: (l1_pre_topc(B_119) | ~m1_pre_topc(B_119, A_120) | ~l1_pre_topc(A_120))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.42/1.31  tff(c_74, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_36, c_65])).
% 2.42/1.31  tff(c_81, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_74])).
% 2.42/1.31  tff(c_26, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.42/1.31  tff(c_125, plain, (![A_138, B_139, C_140, D_141]: (k3_funct_2(A_138, B_139, C_140, D_141)=k1_funct_1(C_140, D_141) | ~m1_subset_1(D_141, A_138) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))) | ~v1_funct_2(C_140, A_138, B_139) | ~v1_funct_1(C_140) | v1_xboole_0(A_138))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.42/1.31  tff(c_134, plain, (![B_139, C_140]: (k3_funct_2(u1_struct_0('#skF_5'), B_139, C_140, '#skF_7')=k1_funct_1(C_140, '#skF_7') | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), B_139))) | ~v1_funct_2(C_140, u1_struct_0('#skF_5'), B_139) | ~v1_funct_1(C_140) | v1_xboole_0(u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_26, c_125])).
% 2.42/1.31  tff(c_190, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_134])).
% 2.42/1.31  tff(c_94, plain, (![B_126, A_127]: (m1_subset_1(u1_struct_0(B_126), k1_zfmisc_1(u1_struct_0(A_127))) | ~m1_pre_topc(B_126, A_127) | ~l1_pre_topc(A_127))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.42/1.31  tff(c_6, plain, (![B_7, A_5]: (v1_xboole_0(B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_5)) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.42/1.31  tff(c_98, plain, (![B_126, A_127]: (v1_xboole_0(u1_struct_0(B_126)) | ~v1_xboole_0(u1_struct_0(A_127)) | ~m1_pre_topc(B_126, A_127) | ~l1_pre_topc(A_127))), inference(resolution, [status(thm)], [c_94, c_6])).
% 2.42/1.31  tff(c_192, plain, (![B_126]: (v1_xboole_0(u1_struct_0(B_126)) | ~m1_pre_topc(B_126, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_190, c_98])).
% 2.42/1.31  tff(c_196, plain, (![B_150]: (v1_xboole_0(u1_struct_0(B_150)) | ~m1_pre_topc(B_150, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_192])).
% 2.42/1.31  tff(c_55, plain, (![B_116, A_117]: (~r2_hidden(B_116, A_117) | ~v1_xboole_0(A_117))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.42/1.31  tff(c_59, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_55])).
% 2.42/1.31  tff(c_201, plain, (~m1_pre_topc('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_196, c_59])).
% 2.42/1.31  tff(c_206, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_201])).
% 2.42/1.31  tff(c_214, plain, (![B_151, C_152]: (k3_funct_2(u1_struct_0('#skF_5'), B_151, C_152, '#skF_7')=k1_funct_1(C_152, '#skF_7') | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), B_151))) | ~v1_funct_2(C_152, u1_struct_0('#skF_5'), B_151) | ~v1_funct_1(C_152))), inference(splitRight, [status(thm)], [c_134])).
% 2.42/1.31  tff(c_217, plain, (k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_7')=k1_funct_1('#skF_6', '#skF_7') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_30, c_214])).
% 2.42/1.31  tff(c_220, plain, (k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_7')=k1_funct_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_217])).
% 2.42/1.31  tff(c_222, plain, $false, inference(negUnitSimplification, [status(thm)], [c_185, c_220])).
% 2.42/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.31  
% 2.42/1.31  Inference rules
% 2.42/1.31  ----------------------
% 2.42/1.31  #Ref     : 0
% 2.42/1.31  #Sup     : 33
% 2.42/1.31  #Fact    : 0
% 2.42/1.31  #Define  : 0
% 2.42/1.31  #Split   : 5
% 2.42/1.31  #Chain   : 0
% 2.42/1.31  #Close   : 0
% 2.42/1.31  
% 2.42/1.31  Ordering : KBO
% 2.42/1.31  
% 2.42/1.31  Simplification rules
% 2.42/1.31  ----------------------
% 2.42/1.31  #Subsume      : 0
% 2.42/1.31  #Demod        : 27
% 2.42/1.31  #Tautology    : 12
% 2.42/1.31  #SimpNegUnit  : 6
% 2.42/1.31  #BackRed      : 1
% 2.42/1.31  
% 2.42/1.31  #Partial instantiations: 0
% 2.42/1.31  #Strategies tried      : 1
% 2.42/1.31  
% 2.42/1.31  Timing (in seconds)
% 2.42/1.31  ----------------------
% 2.42/1.32  Preprocessing        : 0.34
% 2.42/1.32  Parsing              : 0.18
% 2.42/1.32  CNF conversion       : 0.03
% 2.42/1.32  Main loop            : 0.21
% 2.42/1.32  Inferencing          : 0.08
% 2.42/1.32  Reduction            : 0.06
% 2.42/1.32  Demodulation         : 0.05
% 2.42/1.32  BG Simplification    : 0.02
% 2.42/1.32  Subsumption          : 0.03
% 2.42/1.32  Abstraction          : 0.01
% 2.42/1.32  MUC search           : 0.00
% 2.42/1.32  Cooper               : 0.00
% 2.42/1.32  Total                : 0.59
% 2.42/1.32  Index Insertion      : 0.00
% 2.42/1.32  Index Deletion       : 0.00
% 2.42/1.32  Index Matching       : 0.00
% 2.42/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
