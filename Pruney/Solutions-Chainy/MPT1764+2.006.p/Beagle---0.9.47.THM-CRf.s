%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:14 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 119 expanded)
%              Number of leaves         :   33 (  62 expanded)
%              Depth                    :   13
%              Number of atoms          :  197 ( 690 expanded)
%              Number of equality atoms :   29 (  58 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k7_relset_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_152,negated_conjecture,(
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
                              ( m1_subset_1(F,k1_zfmisc_1(u1_struct_0(D)))
                             => ( r1_tarski(F,u1_struct_0(C))
                               => k7_relset_1(u1_struct_0(D),u1_struct_0(B),E,F) = k7_relset_1(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,D,C,E),F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_tmap_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_78,axiom,(
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

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_108,axiom,(
    ! [A,B,C,D,E] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v2_pre_topc(B)
        & l1_pre_topc(B)
        & m1_pre_topc(C,A)
        & m1_pre_topc(D,A)
        & v1_funct_1(E)
        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
     => ( v1_funct_1(k3_tmap_1(A,B,C,D,E))
        & v1_funct_2(k3_tmap_1(A,B,C,D,E),u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(k3_tmap_1(A,B,C,D,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_48,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_32,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_36,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_20,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_26,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_4,plain,(
    ! [C_8,A_6,B_7] :
      ( v1_relat_1(C_8)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_55,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_4])).

tff(c_24,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_42,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_30,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_28,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_79,plain,(
    ! [A_121,B_122,C_123,D_124] :
      ( k2_partfun1(A_121,B_122,C_123,D_124) = k7_relat_1(C_123,D_124)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122)))
      | ~ v1_funct_1(C_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_81,plain,(
    ! [D_124] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_124) = k7_relat_1('#skF_5',D_124)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_26,c_79])).

tff(c_84,plain,(
    ! [D_124] : k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_124) = k7_relat_1('#skF_5',D_124) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_81])).

tff(c_138,plain,(
    ! [C_155,A_154,E_156,B_153,D_152] :
      ( k3_tmap_1(A_154,B_153,C_155,D_152,E_156) = k2_partfun1(u1_struct_0(C_155),u1_struct_0(B_153),E_156,u1_struct_0(D_152))
      | ~ m1_pre_topc(D_152,C_155)
      | ~ m1_subset_1(E_156,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_155),u1_struct_0(B_153))))
      | ~ v1_funct_2(E_156,u1_struct_0(C_155),u1_struct_0(B_153))
      | ~ v1_funct_1(E_156)
      | ~ m1_pre_topc(D_152,A_154)
      | ~ m1_pre_topc(C_155,A_154)
      | ~ l1_pre_topc(B_153)
      | ~ v2_pre_topc(B_153)
      | v2_struct_0(B_153)
      | ~ l1_pre_topc(A_154)
      | ~ v2_pre_topc(A_154)
      | v2_struct_0(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_142,plain,(
    ! [A_154,D_152] :
      ( k3_tmap_1(A_154,'#skF_2','#skF_4',D_152,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_152))
      | ~ m1_pre_topc(D_152,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_152,A_154)
      | ~ m1_pre_topc('#skF_4',A_154)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_154)
      | ~ v2_pre_topc(A_154)
      | v2_struct_0(A_154) ) ),
    inference(resolution,[status(thm)],[c_26,c_138])).

tff(c_146,plain,(
    ! [D_152,A_154] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_152)) = k3_tmap_1(A_154,'#skF_2','#skF_4',D_152,'#skF_5')
      | ~ m1_pre_topc(D_152,'#skF_4')
      | ~ m1_pre_topc(D_152,A_154)
      | ~ m1_pre_topc('#skF_4',A_154)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_154)
      | ~ v2_pre_topc(A_154)
      | v2_struct_0(A_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_30,c_28,c_84,c_142])).

tff(c_148,plain,(
    ! [D_157,A_158] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_157)) = k3_tmap_1(A_158,'#skF_2','#skF_4',D_157,'#skF_5')
      | ~ m1_pre_topc(D_157,'#skF_4')
      | ~ m1_pre_topc(D_157,A_158)
      | ~ m1_pre_topc('#skF_4',A_158)
      | ~ l1_pre_topc(A_158)
      | ~ v2_pre_topc(A_158)
      | v2_struct_0(A_158) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_146])).

tff(c_154,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_148])).

tff(c_165,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_32,c_24,c_154])).

tff(c_166,plain,(
    k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_165])).

tff(c_2,plain,(
    ! [A_1,C_5,B_4] :
      ( k9_relat_1(k7_relat_1(A_1,C_5),B_4) = k9_relat_1(A_1,B_4)
      | ~ r1_tarski(B_4,C_5)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_170,plain,(
    ! [B_4] :
      ( k9_relat_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),B_4) = k9_relat_1('#skF_5',B_4)
      | ~ r1_tarski(B_4,u1_struct_0('#skF_3'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_2])).

tff(c_187,plain,(
    ! [B_165] :
      ( k9_relat_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),B_165) = k9_relat_1('#skF_5',B_165)
      | ~ r1_tarski(B_165,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_170])).

tff(c_191,plain,(
    k9_relat_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') = k9_relat_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_187])).

tff(c_110,plain,(
    ! [C_143,E_144,A_142,B_141,D_140] :
      ( m1_subset_1(k3_tmap_1(A_142,B_141,C_143,D_140,E_144),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_140),u1_struct_0(B_141))))
      | ~ m1_subset_1(E_144,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_143),u1_struct_0(B_141))))
      | ~ v1_funct_2(E_144,u1_struct_0(C_143),u1_struct_0(B_141))
      | ~ v1_funct_1(E_144)
      | ~ m1_pre_topc(D_140,A_142)
      | ~ m1_pre_topc(C_143,A_142)
      | ~ l1_pre_topc(B_141)
      | ~ v2_pre_topc(B_141)
      | v2_struct_0(B_141)
      | ~ l1_pre_topc(A_142)
      | ~ v2_pre_topc(A_142)
      | v2_struct_0(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_6,plain,(
    ! [A_9,B_10,C_11,D_12] :
      ( k7_relset_1(A_9,B_10,C_11,D_12) = k9_relat_1(C_11,D_12)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_176,plain,(
    ! [A_163,E_162,C_159,D_161,D_160,B_164] :
      ( k7_relset_1(u1_struct_0(D_160),u1_struct_0(B_164),k3_tmap_1(A_163,B_164,C_159,D_160,E_162),D_161) = k9_relat_1(k3_tmap_1(A_163,B_164,C_159,D_160,E_162),D_161)
      | ~ m1_subset_1(E_162,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_159),u1_struct_0(B_164))))
      | ~ v1_funct_2(E_162,u1_struct_0(C_159),u1_struct_0(B_164))
      | ~ v1_funct_1(E_162)
      | ~ m1_pre_topc(D_160,A_163)
      | ~ m1_pre_topc(C_159,A_163)
      | ~ l1_pre_topc(B_164)
      | ~ v2_pre_topc(B_164)
      | v2_struct_0(B_164)
      | ~ l1_pre_topc(A_163)
      | ~ v2_pre_topc(A_163)
      | v2_struct_0(A_163) ) ),
    inference(resolution,[status(thm)],[c_110,c_6])).

tff(c_180,plain,(
    ! [D_160,A_163,D_161] :
      ( k7_relset_1(u1_struct_0(D_160),u1_struct_0('#skF_2'),k3_tmap_1(A_163,'#skF_2','#skF_4',D_160,'#skF_5'),D_161) = k9_relat_1(k3_tmap_1(A_163,'#skF_2','#skF_4',D_160,'#skF_5'),D_161)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_160,A_163)
      | ~ m1_pre_topc('#skF_4',A_163)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_163)
      | ~ v2_pre_topc(A_163)
      | v2_struct_0(A_163) ) ),
    inference(resolution,[status(thm)],[c_26,c_176])).

tff(c_184,plain,(
    ! [D_160,A_163,D_161] :
      ( k7_relset_1(u1_struct_0(D_160),u1_struct_0('#skF_2'),k3_tmap_1(A_163,'#skF_2','#skF_4',D_160,'#skF_5'),D_161) = k9_relat_1(k3_tmap_1(A_163,'#skF_2','#skF_4',D_160,'#skF_5'),D_161)
      | ~ m1_pre_topc(D_160,A_163)
      | ~ m1_pre_topc('#skF_4',A_163)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_163)
      | ~ v2_pre_topc(A_163)
      | v2_struct_0(A_163) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_30,c_28,c_180])).

tff(c_197,plain,(
    ! [D_166,A_167,D_168] :
      ( k7_relset_1(u1_struct_0(D_166),u1_struct_0('#skF_2'),k3_tmap_1(A_167,'#skF_2','#skF_4',D_166,'#skF_5'),D_168) = k9_relat_1(k3_tmap_1(A_167,'#skF_2','#skF_4',D_166,'#skF_5'),D_168)
      | ~ m1_pre_topc(D_166,A_167)
      | ~ m1_pre_topc('#skF_4',A_167)
      | ~ l1_pre_topc(A_167)
      | ~ v2_pre_topc(A_167)
      | v2_struct_0(A_167) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_184])).

tff(c_65,plain,(
    ! [A_116,B_117,C_118,D_119] :
      ( k7_relset_1(A_116,B_117,C_118,D_119) = k9_relat_1(C_118,D_119)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_68,plain,(
    ! [D_119] : k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_119) = k9_relat_1('#skF_5',D_119) ),
    inference(resolution,[status(thm)],[c_26,c_65])).

tff(c_18,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') != k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_69,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') != k9_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_18])).

tff(c_203,plain,
    ( k9_relat_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') != k9_relat_1('#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_69])).

tff(c_209,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_32,c_36,c_191,c_203])).

tff(c_211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_209])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:38:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.37  
% 2.49/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.37  %$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k7_relset_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.49/1.37  
% 2.49/1.37  %Foreground sorts:
% 2.49/1.37  
% 2.49/1.37  
% 2.49/1.37  %Background operators:
% 2.49/1.37  
% 2.49/1.37  
% 2.49/1.37  %Foreground operators:
% 2.49/1.37  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.49/1.37  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 2.49/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.49/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.37  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.49/1.37  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.49/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.37  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.49/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.49/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.49/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.49/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.49/1.37  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.49/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.49/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.49/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.49/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.49/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.49/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.49/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.37  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.49/1.37  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.49/1.37  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.49/1.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.49/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.49/1.37  
% 2.75/1.39  tff(f_152, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (r1_tarski(F, u1_struct_0(C)) => (k7_relset_1(u1_struct_0(D), u1_struct_0(B), E, F) = k7_relset_1(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, E), F)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_tmap_1)).
% 2.75/1.39  tff(f_36, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.75/1.39  tff(f_46, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.75/1.39  tff(f_78, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 2.75/1.39  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 2.75/1.39  tff(f_108, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 2.75/1.39  tff(f_40, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.75/1.39  tff(c_50, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.75/1.39  tff(c_48, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.75/1.39  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.75/1.39  tff(c_32, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.75/1.39  tff(c_36, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.75/1.39  tff(c_20, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.75/1.39  tff(c_26, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.75/1.39  tff(c_4, plain, (![C_8, A_6, B_7]: (v1_relat_1(C_8) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.75/1.39  tff(c_55, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_26, c_4])).
% 2.75/1.39  tff(c_24, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.75/1.39  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.75/1.39  tff(c_42, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.75/1.39  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.75/1.39  tff(c_30, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.75/1.39  tff(c_28, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.75/1.39  tff(c_79, plain, (![A_121, B_122, C_123, D_124]: (k2_partfun1(A_121, B_122, C_123, D_124)=k7_relat_1(C_123, D_124) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))) | ~v1_funct_1(C_123))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.75/1.39  tff(c_81, plain, (![D_124]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_124)=k7_relat_1('#skF_5', D_124) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_26, c_79])).
% 2.75/1.39  tff(c_84, plain, (![D_124]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_124)=k7_relat_1('#skF_5', D_124))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_81])).
% 2.75/1.39  tff(c_138, plain, (![C_155, A_154, E_156, B_153, D_152]: (k3_tmap_1(A_154, B_153, C_155, D_152, E_156)=k2_partfun1(u1_struct_0(C_155), u1_struct_0(B_153), E_156, u1_struct_0(D_152)) | ~m1_pre_topc(D_152, C_155) | ~m1_subset_1(E_156, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_155), u1_struct_0(B_153)))) | ~v1_funct_2(E_156, u1_struct_0(C_155), u1_struct_0(B_153)) | ~v1_funct_1(E_156) | ~m1_pre_topc(D_152, A_154) | ~m1_pre_topc(C_155, A_154) | ~l1_pre_topc(B_153) | ~v2_pre_topc(B_153) | v2_struct_0(B_153) | ~l1_pre_topc(A_154) | ~v2_pre_topc(A_154) | v2_struct_0(A_154))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.75/1.39  tff(c_142, plain, (![A_154, D_152]: (k3_tmap_1(A_154, '#skF_2', '#skF_4', D_152, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_152)) | ~m1_pre_topc(D_152, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_152, A_154) | ~m1_pre_topc('#skF_4', A_154) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_154) | ~v2_pre_topc(A_154) | v2_struct_0(A_154))), inference(resolution, [status(thm)], [c_26, c_138])).
% 2.75/1.39  tff(c_146, plain, (![D_152, A_154]: (k7_relat_1('#skF_5', u1_struct_0(D_152))=k3_tmap_1(A_154, '#skF_2', '#skF_4', D_152, '#skF_5') | ~m1_pre_topc(D_152, '#skF_4') | ~m1_pre_topc(D_152, A_154) | ~m1_pre_topc('#skF_4', A_154) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_154) | ~v2_pre_topc(A_154) | v2_struct_0(A_154))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_30, c_28, c_84, c_142])).
% 2.75/1.39  tff(c_148, plain, (![D_157, A_158]: (k7_relat_1('#skF_5', u1_struct_0(D_157))=k3_tmap_1(A_158, '#skF_2', '#skF_4', D_157, '#skF_5') | ~m1_pre_topc(D_157, '#skF_4') | ~m1_pre_topc(D_157, A_158) | ~m1_pre_topc('#skF_4', A_158) | ~l1_pre_topc(A_158) | ~v2_pre_topc(A_158) | v2_struct_0(A_158))), inference(negUnitSimplification, [status(thm)], [c_44, c_146])).
% 2.75/1.39  tff(c_154, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_148])).
% 2.75/1.39  tff(c_165, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_32, c_24, c_154])).
% 2.75/1.39  tff(c_166, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_50, c_165])).
% 2.75/1.39  tff(c_2, plain, (![A_1, C_5, B_4]: (k9_relat_1(k7_relat_1(A_1, C_5), B_4)=k9_relat_1(A_1, B_4) | ~r1_tarski(B_4, C_5) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.75/1.39  tff(c_170, plain, (![B_4]: (k9_relat_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), B_4)=k9_relat_1('#skF_5', B_4) | ~r1_tarski(B_4, u1_struct_0('#skF_3')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_166, c_2])).
% 2.75/1.39  tff(c_187, plain, (![B_165]: (k9_relat_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), B_165)=k9_relat_1('#skF_5', B_165) | ~r1_tarski(B_165, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_170])).
% 2.75/1.39  tff(c_191, plain, (k9_relat_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')=k9_relat_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_20, c_187])).
% 2.75/1.39  tff(c_110, plain, (![C_143, E_144, A_142, B_141, D_140]: (m1_subset_1(k3_tmap_1(A_142, B_141, C_143, D_140, E_144), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_140), u1_struct_0(B_141)))) | ~m1_subset_1(E_144, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_143), u1_struct_0(B_141)))) | ~v1_funct_2(E_144, u1_struct_0(C_143), u1_struct_0(B_141)) | ~v1_funct_1(E_144) | ~m1_pre_topc(D_140, A_142) | ~m1_pre_topc(C_143, A_142) | ~l1_pre_topc(B_141) | ~v2_pre_topc(B_141) | v2_struct_0(B_141) | ~l1_pre_topc(A_142) | ~v2_pre_topc(A_142) | v2_struct_0(A_142))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.75/1.39  tff(c_6, plain, (![A_9, B_10, C_11, D_12]: (k7_relset_1(A_9, B_10, C_11, D_12)=k9_relat_1(C_11, D_12) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.75/1.39  tff(c_176, plain, (![A_163, E_162, C_159, D_161, D_160, B_164]: (k7_relset_1(u1_struct_0(D_160), u1_struct_0(B_164), k3_tmap_1(A_163, B_164, C_159, D_160, E_162), D_161)=k9_relat_1(k3_tmap_1(A_163, B_164, C_159, D_160, E_162), D_161) | ~m1_subset_1(E_162, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_159), u1_struct_0(B_164)))) | ~v1_funct_2(E_162, u1_struct_0(C_159), u1_struct_0(B_164)) | ~v1_funct_1(E_162) | ~m1_pre_topc(D_160, A_163) | ~m1_pre_topc(C_159, A_163) | ~l1_pre_topc(B_164) | ~v2_pre_topc(B_164) | v2_struct_0(B_164) | ~l1_pre_topc(A_163) | ~v2_pre_topc(A_163) | v2_struct_0(A_163))), inference(resolution, [status(thm)], [c_110, c_6])).
% 2.75/1.39  tff(c_180, plain, (![D_160, A_163, D_161]: (k7_relset_1(u1_struct_0(D_160), u1_struct_0('#skF_2'), k3_tmap_1(A_163, '#skF_2', '#skF_4', D_160, '#skF_5'), D_161)=k9_relat_1(k3_tmap_1(A_163, '#skF_2', '#skF_4', D_160, '#skF_5'), D_161) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_160, A_163) | ~m1_pre_topc('#skF_4', A_163) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_163) | ~v2_pre_topc(A_163) | v2_struct_0(A_163))), inference(resolution, [status(thm)], [c_26, c_176])).
% 2.75/1.39  tff(c_184, plain, (![D_160, A_163, D_161]: (k7_relset_1(u1_struct_0(D_160), u1_struct_0('#skF_2'), k3_tmap_1(A_163, '#skF_2', '#skF_4', D_160, '#skF_5'), D_161)=k9_relat_1(k3_tmap_1(A_163, '#skF_2', '#skF_4', D_160, '#skF_5'), D_161) | ~m1_pre_topc(D_160, A_163) | ~m1_pre_topc('#skF_4', A_163) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_163) | ~v2_pre_topc(A_163) | v2_struct_0(A_163))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_30, c_28, c_180])).
% 2.75/1.39  tff(c_197, plain, (![D_166, A_167, D_168]: (k7_relset_1(u1_struct_0(D_166), u1_struct_0('#skF_2'), k3_tmap_1(A_167, '#skF_2', '#skF_4', D_166, '#skF_5'), D_168)=k9_relat_1(k3_tmap_1(A_167, '#skF_2', '#skF_4', D_166, '#skF_5'), D_168) | ~m1_pre_topc(D_166, A_167) | ~m1_pre_topc('#skF_4', A_167) | ~l1_pre_topc(A_167) | ~v2_pre_topc(A_167) | v2_struct_0(A_167))), inference(negUnitSimplification, [status(thm)], [c_44, c_184])).
% 2.75/1.39  tff(c_65, plain, (![A_116, B_117, C_118, D_119]: (k7_relset_1(A_116, B_117, C_118, D_119)=k9_relat_1(C_118, D_119) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.75/1.39  tff(c_68, plain, (![D_119]: (k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_119)=k9_relat_1('#skF_5', D_119))), inference(resolution, [status(thm)], [c_26, c_65])).
% 2.75/1.39  tff(c_18, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')!=k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.75/1.39  tff(c_69, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')!=k9_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_18])).
% 2.75/1.39  tff(c_203, plain, (k9_relat_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')!=k9_relat_1('#skF_5', '#skF_6') | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_197, c_69])).
% 2.75/1.39  tff(c_209, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_32, c_36, c_191, c_203])).
% 2.75/1.39  tff(c_211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_209])).
% 2.75/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.39  
% 2.75/1.39  Inference rules
% 2.75/1.39  ----------------------
% 2.75/1.39  #Ref     : 0
% 2.75/1.39  #Sup     : 34
% 2.75/1.39  #Fact    : 0
% 2.75/1.39  #Define  : 0
% 2.75/1.39  #Split   : 1
% 2.75/1.39  #Chain   : 0
% 2.75/1.39  #Close   : 0
% 2.75/1.39  
% 2.75/1.39  Ordering : KBO
% 2.75/1.39  
% 2.75/1.39  Simplification rules
% 2.75/1.39  ----------------------
% 2.75/1.39  #Subsume      : 1
% 2.75/1.39  #Demod        : 38
% 2.75/1.39  #Tautology    : 11
% 2.75/1.39  #SimpNegUnit  : 9
% 2.75/1.39  #BackRed      : 1
% 2.75/1.39  
% 2.75/1.39  #Partial instantiations: 0
% 2.75/1.39  #Strategies tried      : 1
% 2.75/1.39  
% 2.75/1.39  Timing (in seconds)
% 2.75/1.39  ----------------------
% 2.75/1.39  Preprocessing        : 0.37
% 2.75/1.39  Parsing              : 0.19
% 2.75/1.39  CNF conversion       : 0.04
% 2.75/1.39  Main loop            : 0.25
% 2.75/1.39  Inferencing          : 0.09
% 2.75/1.39  Reduction            : 0.07
% 2.75/1.39  Demodulation         : 0.05
% 2.75/1.39  BG Simplification    : 0.02
% 2.75/1.39  Subsumption          : 0.05
% 2.75/1.39  Abstraction          : 0.02
% 2.75/1.39  MUC search           : 0.00
% 2.75/1.39  Cooper               : 0.00
% 2.75/1.39  Total                : 0.65
% 2.75/1.39  Index Insertion      : 0.00
% 2.75/1.39  Index Deletion       : 0.00
% 2.75/1.39  Index Matching       : 0.00
% 2.75/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
