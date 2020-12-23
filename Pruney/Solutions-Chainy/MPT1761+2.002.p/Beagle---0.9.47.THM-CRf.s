%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:08 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 146 expanded)
%              Number of leaves         :   39 (  72 expanded)
%              Depth                    :   12
%              Number of atoms          :  199 ( 762 expanded)
%              Number of equality atoms :   26 (  56 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff(f_163,negated_conjecture,(
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

tff(f_119,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_105,axiom,(
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

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,B)
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_funct_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_44,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_32,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_38,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_36,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_34,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_56,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_54,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_40,plain,(
    m1_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_144,plain,(
    ! [B_148,C_149,A_150] :
      ( r1_tarski(u1_struct_0(B_148),u1_struct_0(C_149))
      | ~ m1_pre_topc(B_148,C_149)
      | ~ m1_pre_topc(C_149,A_150)
      | ~ m1_pre_topc(B_148,A_150)
      | ~ l1_pre_topc(A_150)
      | ~ v2_pre_topc(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_150,plain,(
    ! [B_148] :
      ( r1_tarski(u1_struct_0(B_148),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_148,'#skF_5')
      | ~ m1_pre_topc(B_148,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_144])).

tff(c_163,plain,(
    ! [B_152] :
      ( r1_tarski(u1_struct_0(B_152),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_152,'#skF_5')
      | ~ m1_pre_topc(B_152,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_150])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_95,plain,(
    ! [B_132,A_133] :
      ( v1_xboole_0(B_132)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(A_133))
      | ~ v1_xboole_0(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_103,plain,(
    ! [A_8,B_9] :
      ( v1_xboole_0(A_8)
      | ~ v1_xboole_0(B_9)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(resolution,[status(thm)],[c_10,c_95])).

tff(c_167,plain,(
    ! [B_152] :
      ( v1_xboole_0(u1_struct_0(B_152))
      | ~ v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_152,'#skF_5')
      | ~ m1_pre_topc(B_152,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_163,c_103])).

tff(c_168,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_167])).

tff(c_30,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_177,plain,(
    ! [A_156,B_157,C_158,D_159] :
      ( k3_funct_2(A_156,B_157,C_158,D_159) = k1_funct_1(C_158,D_159)
      | ~ m1_subset_1(D_159,A_156)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157)))
      | ~ v1_funct_2(C_158,A_156,B_157)
      | ~ v1_funct_1(C_158)
      | v1_xboole_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_183,plain,(
    ! [B_157,C_158] :
      ( k3_funct_2(u1_struct_0('#skF_5'),B_157,C_158,'#skF_7') = k1_funct_1(C_158,'#skF_7')
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),B_157)))
      | ~ v1_funct_2(C_158,u1_struct_0('#skF_5'),B_157)
      | ~ v1_funct_1(C_158)
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_30,c_177])).

tff(c_189,plain,(
    ! [B_160,C_161] :
      ( k3_funct_2(u1_struct_0('#skF_5'),B_160,C_161,'#skF_7') = k1_funct_1(C_161,'#skF_7')
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),B_160)))
      | ~ v1_funct_2(C_161,u1_struct_0('#skF_5'),B_160)
      | ~ v1_funct_1(C_161) ) ),
    inference(negUnitSimplification,[status(thm)],[c_168,c_183])).

tff(c_192,plain,
    ( k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_7') = k1_funct_1('#skF_6','#skF_7')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_189])).

tff(c_199,plain,(
    k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_7') = k1_funct_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_192])).

tff(c_26,plain,(
    k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_7') != k1_funct_1(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_212,plain,(
    k1_funct_1(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_7') != k1_funct_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_26])).

tff(c_28,plain,(
    r2_hidden('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_79,plain,(
    ! [C_126,A_127,B_128] :
      ( v1_relat_1(C_126)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_87,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_79])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_50,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_48,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_119,plain,(
    ! [A_139,B_140,C_141,D_142] :
      ( k2_partfun1(A_139,B_140,C_141,D_142) = k7_relat_1(C_141,D_142)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140)))
      | ~ v1_funct_1(C_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_121,plain,(
    ! [D_142] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',D_142) = k7_relat_1('#skF_6',D_142)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_34,c_119])).

tff(c_127,plain,(
    ! [D_142] : k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',D_142) = k7_relat_1('#skF_6',D_142) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_121])).

tff(c_201,plain,(
    ! [C_165,E_162,D_166,B_163,A_164] :
      ( k3_tmap_1(A_164,B_163,C_165,D_166,E_162) = k2_partfun1(u1_struct_0(C_165),u1_struct_0(B_163),E_162,u1_struct_0(D_166))
      | ~ m1_pre_topc(D_166,C_165)
      | ~ m1_subset_1(E_162,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_165),u1_struct_0(B_163))))
      | ~ v1_funct_2(E_162,u1_struct_0(C_165),u1_struct_0(B_163))
      | ~ v1_funct_1(E_162)
      | ~ m1_pre_topc(D_166,A_164)
      | ~ m1_pre_topc(C_165,A_164)
      | ~ l1_pre_topc(B_163)
      | ~ v2_pre_topc(B_163)
      | v2_struct_0(B_163)
      | ~ l1_pre_topc(A_164)
      | ~ v2_pre_topc(A_164)
      | v2_struct_0(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_203,plain,(
    ! [A_164,D_166] :
      ( k3_tmap_1(A_164,'#skF_3','#skF_5',D_166,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_166))
      | ~ m1_pre_topc(D_166,'#skF_5')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_166,A_164)
      | ~ m1_pre_topc('#skF_5',A_164)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_164)
      | ~ v2_pre_topc(A_164)
      | v2_struct_0(A_164) ) ),
    inference(resolution,[status(thm)],[c_34,c_201])).

tff(c_209,plain,(
    ! [D_166,A_164] :
      ( k7_relat_1('#skF_6',u1_struct_0(D_166)) = k3_tmap_1(A_164,'#skF_3','#skF_5',D_166,'#skF_6')
      | ~ m1_pre_topc(D_166,'#skF_5')
      | ~ m1_pre_topc(D_166,A_164)
      | ~ m1_pre_topc('#skF_5',A_164)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_164)
      | ~ v2_pre_topc(A_164)
      | v2_struct_0(A_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_38,c_36,c_127,c_203])).

tff(c_224,plain,(
    ! [D_169,A_170] :
      ( k7_relat_1('#skF_6',u1_struct_0(D_169)) = k3_tmap_1(A_170,'#skF_3','#skF_5',D_169,'#skF_6')
      | ~ m1_pre_topc(D_169,'#skF_5')
      | ~ m1_pre_topc(D_169,A_170)
      | ~ m1_pre_topc('#skF_5',A_170)
      | ~ l1_pre_topc(A_170)
      | ~ v2_pre_topc(A_170)
      | v2_struct_0(A_170) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_209])).

tff(c_226,plain,
    ( k7_relat_1('#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_224])).

tff(c_233,plain,
    ( k7_relat_1('#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_40,c_32,c_226])).

tff(c_234,plain,(
    k7_relat_1('#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_233])).

tff(c_12,plain,(
    ! [C_12,B_11,A_10] :
      ( k1_funct_1(k7_relat_1(C_12,B_11),A_10) = k1_funct_1(C_12,A_10)
      | ~ r2_hidden(A_10,B_11)
      | ~ v1_funct_1(C_12)
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_246,plain,(
    ! [A_10] :
      ( k1_funct_1(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),A_10) = k1_funct_1('#skF_6',A_10)
      | ~ r2_hidden(A_10,u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_12])).

tff(c_253,plain,(
    ! [A_171] :
      ( k1_funct_1(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),A_171) = k1_funct_1('#skF_6',A_171)
      | ~ r2_hidden(A_171,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_38,c_246])).

tff(c_260,plain,(
    k1_funct_1(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_7') = k1_funct_1('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_28,c_253])).

tff(c_267,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_212,c_260])).

tff(c_277,plain,(
    ! [B_175] :
      ( v1_xboole_0(u1_struct_0(B_175))
      | ~ m1_pre_topc(B_175,'#skF_5')
      | ~ m1_pre_topc(B_175,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_59,plain,(
    ! [B_119,A_120] :
      ( ~ r2_hidden(B_119,A_120)
      | ~ v1_xboole_0(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_63,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_28,c_59])).

tff(c_280,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_277,c_63])).

tff(c_284,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_32,c_280])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:23:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.38  
% 2.51/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.38  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 2.51/1.38  
% 2.51/1.38  %Foreground sorts:
% 2.51/1.38  
% 2.51/1.38  
% 2.51/1.38  %Background operators:
% 2.51/1.38  
% 2.51/1.38  
% 2.51/1.38  %Foreground operators:
% 2.51/1.38  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.51/1.38  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 2.51/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.51/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.51/1.38  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.51/1.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.51/1.38  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.51/1.38  tff('#skF_7', type, '#skF_7': $i).
% 2.51/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.51/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.51/1.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.51/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.51/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.51/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.51/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.51/1.38  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.51/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.51/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.51/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.51/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.38  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.51/1.38  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.51/1.38  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.51/1.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.51/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.51/1.38  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.51/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.51/1.38  
% 2.70/1.40  tff(f_163, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (r2_hidden(F, u1_struct_0(C)) => (k3_funct_2(u1_struct_0(D), u1_struct_0(B), E, F) = k1_funct_1(k3_tmap_1(A, B, D, C, E), F)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_tmap_1)).
% 2.70/1.40  tff(f_119, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 2.70/1.40  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.70/1.40  tff(f_38, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.70/1.40  tff(f_73, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.70/1.40  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.70/1.40  tff(f_60, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.70/1.40  tff(f_105, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 2.70/1.40  tff(f_50, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, B) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_funct_1)).
% 2.70/1.40  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.70/1.40  tff(c_44, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.70/1.40  tff(c_32, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.70/1.40  tff(c_38, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.70/1.40  tff(c_36, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.70/1.40  tff(c_34, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.70/1.40  tff(c_56, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.70/1.40  tff(c_54, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.70/1.40  tff(c_40, plain, (m1_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.70/1.40  tff(c_144, plain, (![B_148, C_149, A_150]: (r1_tarski(u1_struct_0(B_148), u1_struct_0(C_149)) | ~m1_pre_topc(B_148, C_149) | ~m1_pre_topc(C_149, A_150) | ~m1_pre_topc(B_148, A_150) | ~l1_pre_topc(A_150) | ~v2_pre_topc(A_150))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.70/1.40  tff(c_150, plain, (![B_148]: (r1_tarski(u1_struct_0(B_148), u1_struct_0('#skF_5')) | ~m1_pre_topc(B_148, '#skF_5') | ~m1_pre_topc(B_148, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_144])).
% 2.70/1.40  tff(c_163, plain, (![B_152]: (r1_tarski(u1_struct_0(B_152), u1_struct_0('#skF_5')) | ~m1_pre_topc(B_152, '#skF_5') | ~m1_pre_topc(B_152, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_150])).
% 2.70/1.40  tff(c_10, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.70/1.40  tff(c_95, plain, (![B_132, A_133]: (v1_xboole_0(B_132) | ~m1_subset_1(B_132, k1_zfmisc_1(A_133)) | ~v1_xboole_0(A_133))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.70/1.40  tff(c_103, plain, (![A_8, B_9]: (v1_xboole_0(A_8) | ~v1_xboole_0(B_9) | ~r1_tarski(A_8, B_9))), inference(resolution, [status(thm)], [c_10, c_95])).
% 2.70/1.40  tff(c_167, plain, (![B_152]: (v1_xboole_0(u1_struct_0(B_152)) | ~v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_pre_topc(B_152, '#skF_5') | ~m1_pre_topc(B_152, '#skF_2'))), inference(resolution, [status(thm)], [c_163, c_103])).
% 2.70/1.40  tff(c_168, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_167])).
% 2.70/1.40  tff(c_30, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.70/1.40  tff(c_177, plain, (![A_156, B_157, C_158, D_159]: (k3_funct_2(A_156, B_157, C_158, D_159)=k1_funct_1(C_158, D_159) | ~m1_subset_1(D_159, A_156) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))) | ~v1_funct_2(C_158, A_156, B_157) | ~v1_funct_1(C_158) | v1_xboole_0(A_156))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.70/1.40  tff(c_183, plain, (![B_157, C_158]: (k3_funct_2(u1_struct_0('#skF_5'), B_157, C_158, '#skF_7')=k1_funct_1(C_158, '#skF_7') | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), B_157))) | ~v1_funct_2(C_158, u1_struct_0('#skF_5'), B_157) | ~v1_funct_1(C_158) | v1_xboole_0(u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_30, c_177])).
% 2.70/1.40  tff(c_189, plain, (![B_160, C_161]: (k3_funct_2(u1_struct_0('#skF_5'), B_160, C_161, '#skF_7')=k1_funct_1(C_161, '#skF_7') | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), B_160))) | ~v1_funct_2(C_161, u1_struct_0('#skF_5'), B_160) | ~v1_funct_1(C_161))), inference(negUnitSimplification, [status(thm)], [c_168, c_183])).
% 2.70/1.40  tff(c_192, plain, (k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_7')=k1_funct_1('#skF_6', '#skF_7') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_34, c_189])).
% 2.70/1.40  tff(c_199, plain, (k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_7')=k1_funct_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_192])).
% 2.70/1.40  tff(c_26, plain, (k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_7')!=k1_funct_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.70/1.40  tff(c_212, plain, (k1_funct_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_199, c_26])).
% 2.70/1.40  tff(c_28, plain, (r2_hidden('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.70/1.40  tff(c_79, plain, (![C_126, A_127, B_128]: (v1_relat_1(C_126) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.70/1.40  tff(c_87, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_34, c_79])).
% 2.70/1.40  tff(c_58, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.70/1.40  tff(c_52, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.70/1.40  tff(c_50, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.70/1.40  tff(c_48, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 2.70/1.40  tff(c_119, plain, (![A_139, B_140, C_141, D_142]: (k2_partfun1(A_139, B_140, C_141, D_142)=k7_relat_1(C_141, D_142) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))) | ~v1_funct_1(C_141))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.70/1.40  tff(c_121, plain, (![D_142]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', D_142)=k7_relat_1('#skF_6', D_142) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_34, c_119])).
% 2.70/1.40  tff(c_127, plain, (![D_142]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', D_142)=k7_relat_1('#skF_6', D_142))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_121])).
% 2.70/1.40  tff(c_201, plain, (![C_165, E_162, D_166, B_163, A_164]: (k3_tmap_1(A_164, B_163, C_165, D_166, E_162)=k2_partfun1(u1_struct_0(C_165), u1_struct_0(B_163), E_162, u1_struct_0(D_166)) | ~m1_pre_topc(D_166, C_165) | ~m1_subset_1(E_162, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_165), u1_struct_0(B_163)))) | ~v1_funct_2(E_162, u1_struct_0(C_165), u1_struct_0(B_163)) | ~v1_funct_1(E_162) | ~m1_pre_topc(D_166, A_164) | ~m1_pre_topc(C_165, A_164) | ~l1_pre_topc(B_163) | ~v2_pre_topc(B_163) | v2_struct_0(B_163) | ~l1_pre_topc(A_164) | ~v2_pre_topc(A_164) | v2_struct_0(A_164))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.70/1.40  tff(c_203, plain, (![A_164, D_166]: (k3_tmap_1(A_164, '#skF_3', '#skF_5', D_166, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_166)) | ~m1_pre_topc(D_166, '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_166, A_164) | ~m1_pre_topc('#skF_5', A_164) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_164) | ~v2_pre_topc(A_164) | v2_struct_0(A_164))), inference(resolution, [status(thm)], [c_34, c_201])).
% 2.70/1.40  tff(c_209, plain, (![D_166, A_164]: (k7_relat_1('#skF_6', u1_struct_0(D_166))=k3_tmap_1(A_164, '#skF_3', '#skF_5', D_166, '#skF_6') | ~m1_pre_topc(D_166, '#skF_5') | ~m1_pre_topc(D_166, A_164) | ~m1_pre_topc('#skF_5', A_164) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_164) | ~v2_pre_topc(A_164) | v2_struct_0(A_164))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_38, c_36, c_127, c_203])).
% 2.70/1.40  tff(c_224, plain, (![D_169, A_170]: (k7_relat_1('#skF_6', u1_struct_0(D_169))=k3_tmap_1(A_170, '#skF_3', '#skF_5', D_169, '#skF_6') | ~m1_pre_topc(D_169, '#skF_5') | ~m1_pre_topc(D_169, A_170) | ~m1_pre_topc('#skF_5', A_170) | ~l1_pre_topc(A_170) | ~v2_pre_topc(A_170) | v2_struct_0(A_170))), inference(negUnitSimplification, [status(thm)], [c_52, c_209])).
% 2.70/1.40  tff(c_226, plain, (k7_relat_1('#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6') | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_224])).
% 2.70/1.40  tff(c_233, plain, (k7_relat_1('#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_40, c_32, c_226])).
% 2.70/1.40  tff(c_234, plain, (k7_relat_1('#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_58, c_233])).
% 2.70/1.40  tff(c_12, plain, (![C_12, B_11, A_10]: (k1_funct_1(k7_relat_1(C_12, B_11), A_10)=k1_funct_1(C_12, A_10) | ~r2_hidden(A_10, B_11) | ~v1_funct_1(C_12) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.70/1.40  tff(c_246, plain, (![A_10]: (k1_funct_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), A_10)=k1_funct_1('#skF_6', A_10) | ~r2_hidden(A_10, u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_234, c_12])).
% 2.70/1.40  tff(c_253, plain, (![A_171]: (k1_funct_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), A_171)=k1_funct_1('#skF_6', A_171) | ~r2_hidden(A_171, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_38, c_246])).
% 2.70/1.40  tff(c_260, plain, (k1_funct_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_7')=k1_funct_1('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_28, c_253])).
% 2.70/1.40  tff(c_267, plain, $false, inference(negUnitSimplification, [status(thm)], [c_212, c_260])).
% 2.70/1.40  tff(c_277, plain, (![B_175]: (v1_xboole_0(u1_struct_0(B_175)) | ~m1_pre_topc(B_175, '#skF_5') | ~m1_pre_topc(B_175, '#skF_2'))), inference(splitRight, [status(thm)], [c_167])).
% 2.70/1.40  tff(c_59, plain, (![B_119, A_120]: (~r2_hidden(B_119, A_120) | ~v1_xboole_0(A_120))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.70/1.40  tff(c_63, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_28, c_59])).
% 2.70/1.40  tff(c_280, plain, (~m1_pre_topc('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_277, c_63])).
% 2.70/1.40  tff(c_284, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_32, c_280])).
% 2.70/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.40  
% 2.70/1.40  Inference rules
% 2.70/1.40  ----------------------
% 2.70/1.40  #Ref     : 0
% 2.70/1.40  #Sup     : 45
% 2.70/1.40  #Fact    : 0
% 2.70/1.40  #Define  : 0
% 2.70/1.40  #Split   : 4
% 2.70/1.40  #Chain   : 0
% 2.70/1.40  #Close   : 0
% 2.70/1.40  
% 2.70/1.40  Ordering : KBO
% 2.70/1.40  
% 2.70/1.40  Simplification rules
% 2.70/1.40  ----------------------
% 2.70/1.40  #Subsume      : 3
% 2.70/1.40  #Demod        : 31
% 2.70/1.40  #Tautology    : 17
% 2.70/1.40  #SimpNegUnit  : 7
% 2.70/1.40  #BackRed      : 1
% 2.70/1.40  
% 2.70/1.40  #Partial instantiations: 0
% 2.70/1.40  #Strategies tried      : 1
% 2.70/1.40  
% 2.70/1.40  Timing (in seconds)
% 2.70/1.40  ----------------------
% 2.70/1.40  Preprocessing        : 0.38
% 2.70/1.40  Parsing              : 0.19
% 2.70/1.40  CNF conversion       : 0.04
% 2.70/1.40  Main loop            : 0.24
% 2.70/1.40  Inferencing          : 0.09
% 2.70/1.40  Reduction            : 0.08
% 2.70/1.40  Demodulation         : 0.06
% 2.70/1.40  BG Simplification    : 0.02
% 2.70/1.40  Subsumption          : 0.04
% 2.70/1.40  Abstraction          : 0.02
% 2.70/1.40  MUC search           : 0.00
% 2.70/1.40  Cooper               : 0.00
% 2.70/1.40  Total                : 0.66
% 2.70/1.40  Index Insertion      : 0.00
% 2.70/1.40  Index Deletion       : 0.00
% 2.70/1.40  Index Matching       : 0.00
% 2.70/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
