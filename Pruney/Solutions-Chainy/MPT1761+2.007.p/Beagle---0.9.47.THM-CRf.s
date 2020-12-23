%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:09 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 124 expanded)
%              Number of leaves         :   37 (  64 expanded)
%              Depth                    :   12
%              Number of atoms          :  189 ( 661 expanded)
%              Number of equality atoms :   26 (  53 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_157,negated_conjecture,(
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

tff(f_113,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_99,axiom,(
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

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,B)
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_funct_1)).

tff(c_34,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_32,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_40,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_28,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_52,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_36,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_128,plain,(
    ! [B_144,C_145,A_146] :
      ( r1_tarski(u1_struct_0(B_144),u1_struct_0(C_145))
      | ~ m1_pre_topc(B_144,C_145)
      | ~ m1_pre_topc(C_145,A_146)
      | ~ m1_pre_topc(B_144,A_146)
      | ~ l1_pre_topc(A_146)
      | ~ v2_pre_topc(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_134,plain,(
    ! [B_144] :
      ( r1_tarski(u1_struct_0(B_144),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_144,'#skF_4')
      | ~ m1_pre_topc(B_144,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_128])).

tff(c_155,plain,(
    ! [B_151] :
      ( r1_tarski(u1_struct_0(B_151),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_151,'#skF_4')
      | ~ m1_pre_topc(B_151,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_134])).

tff(c_24,plain,(
    r2_hidden('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_81,plain,(
    ! [C_125,B_126,A_127] :
      ( ~ v1_xboole_0(C_125)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(C_125))
      | ~ r2_hidden(A_127,B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_88,plain,(
    ! [B_128,A_129,A_130] :
      ( ~ v1_xboole_0(B_128)
      | ~ r2_hidden(A_129,A_130)
      | ~ r1_tarski(A_130,B_128) ) ),
    inference(resolution,[status(thm)],[c_4,c_81])).

tff(c_91,plain,(
    ! [B_128] :
      ( ~ v1_xboole_0(B_128)
      | ~ r1_tarski(u1_struct_0('#skF_3'),B_128) ) ),
    inference(resolution,[status(thm)],[c_24,c_88])).

tff(c_161,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_155,c_91])).

tff(c_165,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_28,c_161])).

tff(c_26,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_167,plain,(
    ! [A_152,B_153,C_154,D_155] :
      ( k3_funct_2(A_152,B_153,C_154,D_155) = k1_funct_1(C_154,D_155)
      | ~ m1_subset_1(D_155,A_152)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153)))
      | ~ v1_funct_2(C_154,A_152,B_153)
      | ~ v1_funct_1(C_154)
      | v1_xboole_0(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_173,plain,(
    ! [B_153,C_154] :
      ( k3_funct_2(u1_struct_0('#skF_4'),B_153,C_154,'#skF_6') = k1_funct_1(C_154,'#skF_6')
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),B_153)))
      | ~ v1_funct_2(C_154,u1_struct_0('#skF_4'),B_153)
      | ~ v1_funct_1(C_154)
      | v1_xboole_0(u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_26,c_167])).

tff(c_179,plain,(
    ! [B_156,C_157] :
      ( k3_funct_2(u1_struct_0('#skF_4'),B_156,C_157,'#skF_6') = k1_funct_1(C_157,'#skF_6')
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),B_156)))
      | ~ v1_funct_2(C_157,u1_struct_0('#skF_4'),B_156)
      | ~ v1_funct_1(C_157) ) ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_173])).

tff(c_182,plain,
    ( k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6') = k1_funct_1('#skF_5','#skF_6')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_179])).

tff(c_189,plain,(
    k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6') = k1_funct_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_182])).

tff(c_22,plain,(
    k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6') != k1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_191,plain,(
    k1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') != k1_funct_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_22])).

tff(c_10,plain,(
    ! [C_11,A_9,B_10] :
      ( v1_relat_1(C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_74,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_10])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_46,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_44,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_103,plain,(
    ! [A_135,B_136,C_137,D_138] :
      ( k2_partfun1(A_135,B_136,C_137,D_138) = k7_relat_1(C_137,D_138)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136)))
      | ~ v1_funct_1(C_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_105,plain,(
    ! [D_138] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_138) = k7_relat_1('#skF_5',D_138)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30,c_103])).

tff(c_111,plain,(
    ! [D_138] : k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_138) = k7_relat_1('#skF_5',D_138) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_105])).

tff(c_196,plain,(
    ! [B_161,C_162,A_160,D_159,E_158] :
      ( k3_tmap_1(A_160,B_161,C_162,D_159,E_158) = k2_partfun1(u1_struct_0(C_162),u1_struct_0(B_161),E_158,u1_struct_0(D_159))
      | ~ m1_pre_topc(D_159,C_162)
      | ~ m1_subset_1(E_158,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_162),u1_struct_0(B_161))))
      | ~ v1_funct_2(E_158,u1_struct_0(C_162),u1_struct_0(B_161))
      | ~ v1_funct_1(E_158)
      | ~ m1_pre_topc(D_159,A_160)
      | ~ m1_pre_topc(C_162,A_160)
      | ~ l1_pre_topc(B_161)
      | ~ v2_pre_topc(B_161)
      | v2_struct_0(B_161)
      | ~ l1_pre_topc(A_160)
      | ~ v2_pre_topc(A_160)
      | v2_struct_0(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_198,plain,(
    ! [A_160,D_159] :
      ( k3_tmap_1(A_160,'#skF_2','#skF_4',D_159,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_159))
      | ~ m1_pre_topc(D_159,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_159,A_160)
      | ~ m1_pre_topc('#skF_4',A_160)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_160)
      | ~ v2_pre_topc(A_160)
      | v2_struct_0(A_160) ) ),
    inference(resolution,[status(thm)],[c_30,c_196])).

tff(c_204,plain,(
    ! [D_159,A_160] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_159)) = k3_tmap_1(A_160,'#skF_2','#skF_4',D_159,'#skF_5')
      | ~ m1_pre_topc(D_159,'#skF_4')
      | ~ m1_pre_topc(D_159,A_160)
      | ~ m1_pre_topc('#skF_4',A_160)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_160)
      | ~ v2_pre_topc(A_160)
      | v2_struct_0(A_160) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_34,c_32,c_111,c_198])).

tff(c_214,plain,(
    ! [D_165,A_166] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_165)) = k3_tmap_1(A_166,'#skF_2','#skF_4',D_165,'#skF_5')
      | ~ m1_pre_topc(D_165,'#skF_4')
      | ~ m1_pre_topc(D_165,A_166)
      | ~ m1_pre_topc('#skF_4',A_166)
      | ~ l1_pre_topc(A_166)
      | ~ v2_pre_topc(A_166)
      | v2_struct_0(A_166) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_204])).

tff(c_216,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_214])).

tff(c_223,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_36,c_28,c_216])).

tff(c_224,plain,(
    k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_223])).

tff(c_8,plain,(
    ! [C_8,B_7,A_6] :
      ( k1_funct_1(k7_relat_1(C_8,B_7),A_6) = k1_funct_1(C_8,A_6)
      | ~ r2_hidden(A_6,B_7)
      | ~ v1_funct_1(C_8)
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_236,plain,(
    ! [A_6] :
      ( k1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),A_6) = k1_funct_1('#skF_5',A_6)
      | ~ r2_hidden(A_6,u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_8])).

tff(c_243,plain,(
    ! [A_167] :
      ( k1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),A_167) = k1_funct_1('#skF_5',A_167)
      | ~ r2_hidden(A_167,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_34,c_236])).

tff(c_246,plain,(
    k1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') = k1_funct_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_243])).

tff(c_250,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_191,c_246])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:47:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.55/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.34  
% 2.55/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.35  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.55/1.35  
% 2.55/1.35  %Foreground sorts:
% 2.55/1.35  
% 2.55/1.35  
% 2.55/1.35  %Background operators:
% 2.55/1.35  
% 2.55/1.35  
% 2.55/1.35  %Foreground operators:
% 2.55/1.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.55/1.35  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 2.55/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.55/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.55/1.35  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.55/1.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.55/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.55/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.55/1.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.55/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.55/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.55/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.55/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.55/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.55/1.35  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.55/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.55/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.55/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.55/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.35  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.55/1.35  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.55/1.35  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.55/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.55/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.55/1.35  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.55/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.55/1.35  
% 2.55/1.37  tff(f_157, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (r2_hidden(F, u1_struct_0(C)) => (k3_funct_2(u1_struct_0(D), u1_struct_0(B), E, F) = k1_funct_1(k3_tmap_1(A, B, D, C, E), F)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_tmap_1)).
% 2.55/1.37  tff(f_113, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 2.55/1.37  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.55/1.37  tff(f_36, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.55/1.37  tff(f_67, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.55/1.37  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.55/1.37  tff(f_54, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.55/1.37  tff(f_99, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 2.55/1.37  tff(f_44, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, B) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_funct_1)).
% 2.55/1.37  tff(c_34, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.55/1.37  tff(c_32, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.55/1.37  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.55/1.37  tff(c_40, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.55/1.37  tff(c_28, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.55/1.37  tff(c_52, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.55/1.37  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.55/1.37  tff(c_36, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.55/1.37  tff(c_128, plain, (![B_144, C_145, A_146]: (r1_tarski(u1_struct_0(B_144), u1_struct_0(C_145)) | ~m1_pre_topc(B_144, C_145) | ~m1_pre_topc(C_145, A_146) | ~m1_pre_topc(B_144, A_146) | ~l1_pre_topc(A_146) | ~v2_pre_topc(A_146))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.55/1.37  tff(c_134, plain, (![B_144]: (r1_tarski(u1_struct_0(B_144), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_144, '#skF_4') | ~m1_pre_topc(B_144, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_128])).
% 2.55/1.37  tff(c_155, plain, (![B_151]: (r1_tarski(u1_struct_0(B_151), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_151, '#skF_4') | ~m1_pre_topc(B_151, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_134])).
% 2.55/1.37  tff(c_24, plain, (r2_hidden('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.55/1.37  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.55/1.37  tff(c_81, plain, (![C_125, B_126, A_127]: (~v1_xboole_0(C_125) | ~m1_subset_1(B_126, k1_zfmisc_1(C_125)) | ~r2_hidden(A_127, B_126))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.55/1.37  tff(c_88, plain, (![B_128, A_129, A_130]: (~v1_xboole_0(B_128) | ~r2_hidden(A_129, A_130) | ~r1_tarski(A_130, B_128))), inference(resolution, [status(thm)], [c_4, c_81])).
% 2.55/1.37  tff(c_91, plain, (![B_128]: (~v1_xboole_0(B_128) | ~r1_tarski(u1_struct_0('#skF_3'), B_128))), inference(resolution, [status(thm)], [c_24, c_88])).
% 2.55/1.37  tff(c_161, plain, (~v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_155, c_91])).
% 2.55/1.37  tff(c_165, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_28, c_161])).
% 2.55/1.37  tff(c_26, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.55/1.37  tff(c_167, plain, (![A_152, B_153, C_154, D_155]: (k3_funct_2(A_152, B_153, C_154, D_155)=k1_funct_1(C_154, D_155) | ~m1_subset_1(D_155, A_152) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))) | ~v1_funct_2(C_154, A_152, B_153) | ~v1_funct_1(C_154) | v1_xboole_0(A_152))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.55/1.37  tff(c_173, plain, (![B_153, C_154]: (k3_funct_2(u1_struct_0('#skF_4'), B_153, C_154, '#skF_6')=k1_funct_1(C_154, '#skF_6') | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), B_153))) | ~v1_funct_2(C_154, u1_struct_0('#skF_4'), B_153) | ~v1_funct_1(C_154) | v1_xboole_0(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_26, c_167])).
% 2.55/1.37  tff(c_179, plain, (![B_156, C_157]: (k3_funct_2(u1_struct_0('#skF_4'), B_156, C_157, '#skF_6')=k1_funct_1(C_157, '#skF_6') | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), B_156))) | ~v1_funct_2(C_157, u1_struct_0('#skF_4'), B_156) | ~v1_funct_1(C_157))), inference(negUnitSimplification, [status(thm)], [c_165, c_173])).
% 2.55/1.37  tff(c_182, plain, (k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6')=k1_funct_1('#skF_5', '#skF_6') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_179])).
% 2.55/1.37  tff(c_189, plain, (k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6')=k1_funct_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_182])).
% 2.55/1.37  tff(c_22, plain, (k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6')!=k1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.55/1.37  tff(c_191, plain, (k1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_189, c_22])).
% 2.55/1.37  tff(c_10, plain, (![C_11, A_9, B_10]: (v1_relat_1(C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.55/1.37  tff(c_74, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_10])).
% 2.55/1.37  tff(c_54, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.55/1.37  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.55/1.37  tff(c_46, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.55/1.37  tff(c_44, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.55/1.37  tff(c_103, plain, (![A_135, B_136, C_137, D_138]: (k2_partfun1(A_135, B_136, C_137, D_138)=k7_relat_1(C_137, D_138) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))) | ~v1_funct_1(C_137))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.55/1.37  tff(c_105, plain, (![D_138]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_138)=k7_relat_1('#skF_5', D_138) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_30, c_103])).
% 2.55/1.37  tff(c_111, plain, (![D_138]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_138)=k7_relat_1('#skF_5', D_138))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_105])).
% 2.55/1.37  tff(c_196, plain, (![B_161, C_162, A_160, D_159, E_158]: (k3_tmap_1(A_160, B_161, C_162, D_159, E_158)=k2_partfun1(u1_struct_0(C_162), u1_struct_0(B_161), E_158, u1_struct_0(D_159)) | ~m1_pre_topc(D_159, C_162) | ~m1_subset_1(E_158, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_162), u1_struct_0(B_161)))) | ~v1_funct_2(E_158, u1_struct_0(C_162), u1_struct_0(B_161)) | ~v1_funct_1(E_158) | ~m1_pre_topc(D_159, A_160) | ~m1_pre_topc(C_162, A_160) | ~l1_pre_topc(B_161) | ~v2_pre_topc(B_161) | v2_struct_0(B_161) | ~l1_pre_topc(A_160) | ~v2_pre_topc(A_160) | v2_struct_0(A_160))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.55/1.37  tff(c_198, plain, (![A_160, D_159]: (k3_tmap_1(A_160, '#skF_2', '#skF_4', D_159, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_159)) | ~m1_pre_topc(D_159, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_159, A_160) | ~m1_pre_topc('#skF_4', A_160) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_160) | ~v2_pre_topc(A_160) | v2_struct_0(A_160))), inference(resolution, [status(thm)], [c_30, c_196])).
% 2.55/1.37  tff(c_204, plain, (![D_159, A_160]: (k7_relat_1('#skF_5', u1_struct_0(D_159))=k3_tmap_1(A_160, '#skF_2', '#skF_4', D_159, '#skF_5') | ~m1_pre_topc(D_159, '#skF_4') | ~m1_pre_topc(D_159, A_160) | ~m1_pre_topc('#skF_4', A_160) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_160) | ~v2_pre_topc(A_160) | v2_struct_0(A_160))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_34, c_32, c_111, c_198])).
% 2.55/1.37  tff(c_214, plain, (![D_165, A_166]: (k7_relat_1('#skF_5', u1_struct_0(D_165))=k3_tmap_1(A_166, '#skF_2', '#skF_4', D_165, '#skF_5') | ~m1_pre_topc(D_165, '#skF_4') | ~m1_pre_topc(D_165, A_166) | ~m1_pre_topc('#skF_4', A_166) | ~l1_pre_topc(A_166) | ~v2_pre_topc(A_166) | v2_struct_0(A_166))), inference(negUnitSimplification, [status(thm)], [c_48, c_204])).
% 2.55/1.37  tff(c_216, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_214])).
% 2.55/1.37  tff(c_223, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_36, c_28, c_216])).
% 2.55/1.37  tff(c_224, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_54, c_223])).
% 2.55/1.37  tff(c_8, plain, (![C_8, B_7, A_6]: (k1_funct_1(k7_relat_1(C_8, B_7), A_6)=k1_funct_1(C_8, A_6) | ~r2_hidden(A_6, B_7) | ~v1_funct_1(C_8) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.55/1.37  tff(c_236, plain, (![A_6]: (k1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), A_6)=k1_funct_1('#skF_5', A_6) | ~r2_hidden(A_6, u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_224, c_8])).
% 2.55/1.37  tff(c_243, plain, (![A_167]: (k1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), A_167)=k1_funct_1('#skF_5', A_167) | ~r2_hidden(A_167, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_34, c_236])).
% 2.55/1.37  tff(c_246, plain, (k1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')=k1_funct_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_24, c_243])).
% 2.55/1.37  tff(c_250, plain, $false, inference(negUnitSimplification, [status(thm)], [c_191, c_246])).
% 2.55/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.37  
% 2.55/1.37  Inference rules
% 2.55/1.37  ----------------------
% 2.55/1.37  #Ref     : 0
% 2.55/1.37  #Sup     : 39
% 2.55/1.37  #Fact    : 0
% 2.55/1.37  #Define  : 0
% 2.55/1.37  #Split   : 4
% 2.55/1.37  #Chain   : 0
% 2.55/1.37  #Close   : 0
% 2.55/1.37  
% 2.55/1.37  Ordering : KBO
% 2.55/1.37  
% 2.55/1.37  Simplification rules
% 2.55/1.37  ----------------------
% 2.55/1.37  #Subsume      : 1
% 2.55/1.37  #Demod        : 32
% 2.55/1.37  #Tautology    : 14
% 2.55/1.37  #SimpNegUnit  : 6
% 2.55/1.37  #BackRed      : 1
% 2.55/1.37  
% 2.55/1.37  #Partial instantiations: 0
% 2.55/1.37  #Strategies tried      : 1
% 2.55/1.37  
% 2.55/1.37  Timing (in seconds)
% 2.55/1.37  ----------------------
% 2.55/1.37  Preprocessing        : 0.37
% 2.55/1.37  Parsing              : 0.19
% 2.55/1.37  CNF conversion       : 0.04
% 2.55/1.37  Main loop            : 0.23
% 2.55/1.37  Inferencing          : 0.09
% 2.55/1.37  Reduction            : 0.07
% 2.55/1.37  Demodulation         : 0.05
% 2.55/1.37  BG Simplification    : 0.02
% 2.55/1.37  Subsumption          : 0.03
% 2.55/1.37  Abstraction          : 0.02
% 2.55/1.37  MUC search           : 0.00
% 2.55/1.37  Cooper               : 0.00
% 2.55/1.37  Total                : 0.64
% 2.55/1.37  Index Insertion      : 0.00
% 2.55/1.37  Index Deletion       : 0.00
% 2.55/1.37  Index Matching       : 0.00
% 2.55/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
