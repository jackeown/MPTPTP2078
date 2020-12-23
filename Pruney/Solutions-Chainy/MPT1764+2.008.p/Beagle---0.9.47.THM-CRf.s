%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:14 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 122 expanded)
%              Number of leaves         :   34 (  63 expanded)
%              Depth                    :   13
%              Number of atoms          :  203 ( 696 expanded)
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
                              ( m1_subset_1(F,k1_zfmisc_1(u1_struct_0(D)))
                             => ( r1_tarski(F,u1_struct_0(C))
                               => k7_relset_1(u1_struct_0(D),u1_struct_0(B),E,F) = k7_relset_1(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,D,C,E),F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_tmap_1)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_83,axiom,(
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

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_113,axiom,(
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

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_50,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_34,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_38,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_22,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_28,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_54,plain,(
    ! [B_114,A_115] :
      ( v1_relat_1(B_114)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(A_115))
      | ~ v1_relat_1(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_57,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_28,c_54])).

tff(c_63,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_57])).

tff(c_26,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_44,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_42,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_32,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_30,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_89,plain,(
    ! [A_124,B_125,C_126,D_127] :
      ( k2_partfun1(A_124,B_125,C_126,D_127) = k7_relat_1(C_126,D_127)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125)))
      | ~ v1_funct_1(C_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_91,plain,(
    ! [D_127] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_127) = k7_relat_1('#skF_5',D_127)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_89])).

tff(c_94,plain,(
    ! [D_127] : k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_127) = k7_relat_1('#skF_5',D_127) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_91])).

tff(c_150,plain,(
    ! [C_155,E_159,D_156,A_157,B_158] :
      ( k3_tmap_1(A_157,B_158,C_155,D_156,E_159) = k2_partfun1(u1_struct_0(C_155),u1_struct_0(B_158),E_159,u1_struct_0(D_156))
      | ~ m1_pre_topc(D_156,C_155)
      | ~ m1_subset_1(E_159,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_155),u1_struct_0(B_158))))
      | ~ v1_funct_2(E_159,u1_struct_0(C_155),u1_struct_0(B_158))
      | ~ v1_funct_1(E_159)
      | ~ m1_pre_topc(D_156,A_157)
      | ~ m1_pre_topc(C_155,A_157)
      | ~ l1_pre_topc(B_158)
      | ~ v2_pre_topc(B_158)
      | v2_struct_0(B_158)
      | ~ l1_pre_topc(A_157)
      | ~ v2_pre_topc(A_157)
      | v2_struct_0(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_154,plain,(
    ! [A_157,D_156] :
      ( k3_tmap_1(A_157,'#skF_2','#skF_4',D_156,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_156))
      | ~ m1_pre_topc(D_156,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_156,A_157)
      | ~ m1_pre_topc('#skF_4',A_157)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_157)
      | ~ v2_pre_topc(A_157)
      | v2_struct_0(A_157) ) ),
    inference(resolution,[status(thm)],[c_28,c_150])).

tff(c_158,plain,(
    ! [D_156,A_157] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_156)) = k3_tmap_1(A_157,'#skF_2','#skF_4',D_156,'#skF_5')
      | ~ m1_pre_topc(D_156,'#skF_4')
      | ~ m1_pre_topc(D_156,A_157)
      | ~ m1_pre_topc('#skF_4',A_157)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_157)
      | ~ v2_pre_topc(A_157)
      | v2_struct_0(A_157) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_32,c_30,c_94,c_154])).

tff(c_160,plain,(
    ! [D_160,A_161] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_160)) = k3_tmap_1(A_161,'#skF_2','#skF_4',D_160,'#skF_5')
      | ~ m1_pre_topc(D_160,'#skF_4')
      | ~ m1_pre_topc(D_160,A_161)
      | ~ m1_pre_topc('#skF_4',A_161)
      | ~ l1_pre_topc(A_161)
      | ~ v2_pre_topc(A_161)
      | v2_struct_0(A_161) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_158])).

tff(c_166,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_160])).

tff(c_177,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_34,c_26,c_166])).

tff(c_178,plain,(
    k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_177])).

tff(c_6,plain,(
    ! [A_6,C_10,B_9] :
      ( k9_relat_1(k7_relat_1(A_6,C_10),B_9) = k9_relat_1(A_6,B_9)
      | ~ r1_tarski(B_9,C_10)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_182,plain,(
    ! [B_9] :
      ( k9_relat_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),B_9) = k9_relat_1('#skF_5',B_9)
      | ~ r1_tarski(B_9,u1_struct_0('#skF_3'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_6])).

tff(c_191,plain,(
    ! [B_162] :
      ( k9_relat_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),B_162) = k9_relat_1('#skF_5',B_162)
      | ~ r1_tarski(B_162,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_182])).

tff(c_195,plain,(
    k9_relat_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') = k9_relat_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_22,c_191])).

tff(c_120,plain,(
    ! [E_143,A_144,D_147,C_145,B_146] :
      ( m1_subset_1(k3_tmap_1(A_144,B_146,C_145,D_147,E_143),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_147),u1_struct_0(B_146))))
      | ~ m1_subset_1(E_143,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_145),u1_struct_0(B_146))))
      | ~ v1_funct_2(E_143,u1_struct_0(C_145),u1_struct_0(B_146))
      | ~ v1_funct_1(E_143)
      | ~ m1_pre_topc(D_147,A_144)
      | ~ m1_pre_topc(C_145,A_144)
      | ~ l1_pre_topc(B_146)
      | ~ v2_pre_topc(B_146)
      | v2_struct_0(B_146)
      | ~ l1_pre_topc(A_144)
      | ~ v2_pre_topc(A_144)
      | v2_struct_0(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_8,plain,(
    ! [A_11,B_12,C_13,D_14] :
      ( k7_relset_1(A_11,B_12,C_13,D_14) = k9_relat_1(C_13,D_14)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_200,plain,(
    ! [A_163,E_166,D_167,B_165,C_168,D_164] :
      ( k7_relset_1(u1_struct_0(D_164),u1_struct_0(B_165),k3_tmap_1(A_163,B_165,C_168,D_164,E_166),D_167) = k9_relat_1(k3_tmap_1(A_163,B_165,C_168,D_164,E_166),D_167)
      | ~ m1_subset_1(E_166,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_168),u1_struct_0(B_165))))
      | ~ v1_funct_2(E_166,u1_struct_0(C_168),u1_struct_0(B_165))
      | ~ v1_funct_1(E_166)
      | ~ m1_pre_topc(D_164,A_163)
      | ~ m1_pre_topc(C_168,A_163)
      | ~ l1_pre_topc(B_165)
      | ~ v2_pre_topc(B_165)
      | v2_struct_0(B_165)
      | ~ l1_pre_topc(A_163)
      | ~ v2_pre_topc(A_163)
      | v2_struct_0(A_163) ) ),
    inference(resolution,[status(thm)],[c_120,c_8])).

tff(c_204,plain,(
    ! [D_164,A_163,D_167] :
      ( k7_relset_1(u1_struct_0(D_164),u1_struct_0('#skF_2'),k3_tmap_1(A_163,'#skF_2','#skF_4',D_164,'#skF_5'),D_167) = k9_relat_1(k3_tmap_1(A_163,'#skF_2','#skF_4',D_164,'#skF_5'),D_167)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_164,A_163)
      | ~ m1_pre_topc('#skF_4',A_163)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_163)
      | ~ v2_pre_topc(A_163)
      | v2_struct_0(A_163) ) ),
    inference(resolution,[status(thm)],[c_28,c_200])).

tff(c_208,plain,(
    ! [D_164,A_163,D_167] :
      ( k7_relset_1(u1_struct_0(D_164),u1_struct_0('#skF_2'),k3_tmap_1(A_163,'#skF_2','#skF_4',D_164,'#skF_5'),D_167) = k9_relat_1(k3_tmap_1(A_163,'#skF_2','#skF_4',D_164,'#skF_5'),D_167)
      | ~ m1_pre_topc(D_164,A_163)
      | ~ m1_pre_topc('#skF_4',A_163)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_163)
      | ~ v2_pre_topc(A_163)
      | v2_struct_0(A_163) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_32,c_30,c_204])).

tff(c_220,plain,(
    ! [D_175,A_176,D_177] :
      ( k7_relset_1(u1_struct_0(D_175),u1_struct_0('#skF_2'),k3_tmap_1(A_176,'#skF_2','#skF_4',D_175,'#skF_5'),D_177) = k9_relat_1(k3_tmap_1(A_176,'#skF_2','#skF_4',D_175,'#skF_5'),D_177)
      | ~ m1_pre_topc(D_175,A_176)
      | ~ m1_pre_topc('#skF_4',A_176)
      | ~ l1_pre_topc(A_176)
      | ~ v2_pre_topc(A_176)
      | v2_struct_0(A_176) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_208])).

tff(c_75,plain,(
    ! [A_119,B_120,C_121,D_122] :
      ( k7_relset_1(A_119,B_120,C_121,D_122) = k9_relat_1(C_121,D_122)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_78,plain,(
    ! [D_122] : k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_122) = k9_relat_1('#skF_5',D_122) ),
    inference(resolution,[status(thm)],[c_28,c_75])).

tff(c_20,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') != k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_79,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') != k9_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_20])).

tff(c_226,plain,
    ( k9_relat_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') != k9_relat_1('#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_79])).

tff(c_232,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_34,c_38,c_195,c_226])).

tff(c_234,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_232])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.16/0.36  % Computer   : n024.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 16:58:21 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.28  
% 2.50/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.28  %$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k7_relset_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.50/1.28  
% 2.50/1.28  %Foreground sorts:
% 2.50/1.28  
% 2.50/1.28  
% 2.50/1.28  %Background operators:
% 2.50/1.28  
% 2.50/1.28  
% 2.50/1.28  %Foreground operators:
% 2.50/1.28  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.50/1.28  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 2.50/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.50/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.28  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.50/1.28  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.50/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.50/1.28  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.50/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.50/1.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.50/1.28  tff('#skF_6', type, '#skF_6': $i).
% 2.50/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.50/1.28  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.50/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.50/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.50/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.50/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.50/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.50/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.50/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.28  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.50/1.28  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.50/1.28  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.50/1.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.50/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.50/1.28  
% 2.79/1.30  tff(f_157, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (r1_tarski(F, u1_struct_0(C)) => (k7_relset_1(u1_struct_0(D), u1_struct_0(B), E, F) = k7_relset_1(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, E), F)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_tmap_1)).
% 2.79/1.30  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.79/1.30  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.79/1.30  tff(f_51, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.79/1.30  tff(f_83, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 2.79/1.30  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 2.79/1.30  tff(f_113, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 2.79/1.30  tff(f_45, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.79/1.30  tff(c_52, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.79/1.30  tff(c_50, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.79/1.30  tff(c_48, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.79/1.30  tff(c_34, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.79/1.30  tff(c_38, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.79/1.30  tff(c_22, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.79/1.30  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.79/1.30  tff(c_28, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.79/1.30  tff(c_54, plain, (![B_114, A_115]: (v1_relat_1(B_114) | ~m1_subset_1(B_114, k1_zfmisc_1(A_115)) | ~v1_relat_1(A_115))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.79/1.30  tff(c_57, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_28, c_54])).
% 2.79/1.30  tff(c_63, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_57])).
% 2.79/1.30  tff(c_26, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.79/1.30  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.79/1.30  tff(c_44, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.79/1.30  tff(c_42, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.79/1.30  tff(c_32, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.79/1.30  tff(c_30, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.79/1.30  tff(c_89, plain, (![A_124, B_125, C_126, D_127]: (k2_partfun1(A_124, B_125, C_126, D_127)=k7_relat_1(C_126, D_127) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))) | ~v1_funct_1(C_126))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.79/1.30  tff(c_91, plain, (![D_127]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_127)=k7_relat_1('#skF_5', D_127) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_28, c_89])).
% 2.79/1.30  tff(c_94, plain, (![D_127]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_127)=k7_relat_1('#skF_5', D_127))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_91])).
% 2.79/1.30  tff(c_150, plain, (![C_155, E_159, D_156, A_157, B_158]: (k3_tmap_1(A_157, B_158, C_155, D_156, E_159)=k2_partfun1(u1_struct_0(C_155), u1_struct_0(B_158), E_159, u1_struct_0(D_156)) | ~m1_pre_topc(D_156, C_155) | ~m1_subset_1(E_159, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_155), u1_struct_0(B_158)))) | ~v1_funct_2(E_159, u1_struct_0(C_155), u1_struct_0(B_158)) | ~v1_funct_1(E_159) | ~m1_pre_topc(D_156, A_157) | ~m1_pre_topc(C_155, A_157) | ~l1_pre_topc(B_158) | ~v2_pre_topc(B_158) | v2_struct_0(B_158) | ~l1_pre_topc(A_157) | ~v2_pre_topc(A_157) | v2_struct_0(A_157))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.79/1.30  tff(c_154, plain, (![A_157, D_156]: (k3_tmap_1(A_157, '#skF_2', '#skF_4', D_156, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_156)) | ~m1_pre_topc(D_156, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_156, A_157) | ~m1_pre_topc('#skF_4', A_157) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_157) | ~v2_pre_topc(A_157) | v2_struct_0(A_157))), inference(resolution, [status(thm)], [c_28, c_150])).
% 2.79/1.30  tff(c_158, plain, (![D_156, A_157]: (k7_relat_1('#skF_5', u1_struct_0(D_156))=k3_tmap_1(A_157, '#skF_2', '#skF_4', D_156, '#skF_5') | ~m1_pre_topc(D_156, '#skF_4') | ~m1_pre_topc(D_156, A_157) | ~m1_pre_topc('#skF_4', A_157) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_157) | ~v2_pre_topc(A_157) | v2_struct_0(A_157))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_32, c_30, c_94, c_154])).
% 2.79/1.30  tff(c_160, plain, (![D_160, A_161]: (k7_relat_1('#skF_5', u1_struct_0(D_160))=k3_tmap_1(A_161, '#skF_2', '#skF_4', D_160, '#skF_5') | ~m1_pre_topc(D_160, '#skF_4') | ~m1_pre_topc(D_160, A_161) | ~m1_pre_topc('#skF_4', A_161) | ~l1_pre_topc(A_161) | ~v2_pre_topc(A_161) | v2_struct_0(A_161))), inference(negUnitSimplification, [status(thm)], [c_46, c_158])).
% 2.79/1.30  tff(c_166, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_160])).
% 2.79/1.30  tff(c_177, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_34, c_26, c_166])).
% 2.79/1.30  tff(c_178, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_52, c_177])).
% 2.79/1.30  tff(c_6, plain, (![A_6, C_10, B_9]: (k9_relat_1(k7_relat_1(A_6, C_10), B_9)=k9_relat_1(A_6, B_9) | ~r1_tarski(B_9, C_10) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.79/1.30  tff(c_182, plain, (![B_9]: (k9_relat_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), B_9)=k9_relat_1('#skF_5', B_9) | ~r1_tarski(B_9, u1_struct_0('#skF_3')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_178, c_6])).
% 2.79/1.30  tff(c_191, plain, (![B_162]: (k9_relat_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), B_162)=k9_relat_1('#skF_5', B_162) | ~r1_tarski(B_162, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_182])).
% 2.79/1.30  tff(c_195, plain, (k9_relat_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')=k9_relat_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_22, c_191])).
% 2.79/1.30  tff(c_120, plain, (![E_143, A_144, D_147, C_145, B_146]: (m1_subset_1(k3_tmap_1(A_144, B_146, C_145, D_147, E_143), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_147), u1_struct_0(B_146)))) | ~m1_subset_1(E_143, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_145), u1_struct_0(B_146)))) | ~v1_funct_2(E_143, u1_struct_0(C_145), u1_struct_0(B_146)) | ~v1_funct_1(E_143) | ~m1_pre_topc(D_147, A_144) | ~m1_pre_topc(C_145, A_144) | ~l1_pre_topc(B_146) | ~v2_pre_topc(B_146) | v2_struct_0(B_146) | ~l1_pre_topc(A_144) | ~v2_pre_topc(A_144) | v2_struct_0(A_144))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.79/1.30  tff(c_8, plain, (![A_11, B_12, C_13, D_14]: (k7_relset_1(A_11, B_12, C_13, D_14)=k9_relat_1(C_13, D_14) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.79/1.30  tff(c_200, plain, (![A_163, E_166, D_167, B_165, C_168, D_164]: (k7_relset_1(u1_struct_0(D_164), u1_struct_0(B_165), k3_tmap_1(A_163, B_165, C_168, D_164, E_166), D_167)=k9_relat_1(k3_tmap_1(A_163, B_165, C_168, D_164, E_166), D_167) | ~m1_subset_1(E_166, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_168), u1_struct_0(B_165)))) | ~v1_funct_2(E_166, u1_struct_0(C_168), u1_struct_0(B_165)) | ~v1_funct_1(E_166) | ~m1_pre_topc(D_164, A_163) | ~m1_pre_topc(C_168, A_163) | ~l1_pre_topc(B_165) | ~v2_pre_topc(B_165) | v2_struct_0(B_165) | ~l1_pre_topc(A_163) | ~v2_pre_topc(A_163) | v2_struct_0(A_163))), inference(resolution, [status(thm)], [c_120, c_8])).
% 2.79/1.30  tff(c_204, plain, (![D_164, A_163, D_167]: (k7_relset_1(u1_struct_0(D_164), u1_struct_0('#skF_2'), k3_tmap_1(A_163, '#skF_2', '#skF_4', D_164, '#skF_5'), D_167)=k9_relat_1(k3_tmap_1(A_163, '#skF_2', '#skF_4', D_164, '#skF_5'), D_167) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_164, A_163) | ~m1_pre_topc('#skF_4', A_163) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_163) | ~v2_pre_topc(A_163) | v2_struct_0(A_163))), inference(resolution, [status(thm)], [c_28, c_200])).
% 2.79/1.30  tff(c_208, plain, (![D_164, A_163, D_167]: (k7_relset_1(u1_struct_0(D_164), u1_struct_0('#skF_2'), k3_tmap_1(A_163, '#skF_2', '#skF_4', D_164, '#skF_5'), D_167)=k9_relat_1(k3_tmap_1(A_163, '#skF_2', '#skF_4', D_164, '#skF_5'), D_167) | ~m1_pre_topc(D_164, A_163) | ~m1_pre_topc('#skF_4', A_163) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_163) | ~v2_pre_topc(A_163) | v2_struct_0(A_163))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_32, c_30, c_204])).
% 2.79/1.30  tff(c_220, plain, (![D_175, A_176, D_177]: (k7_relset_1(u1_struct_0(D_175), u1_struct_0('#skF_2'), k3_tmap_1(A_176, '#skF_2', '#skF_4', D_175, '#skF_5'), D_177)=k9_relat_1(k3_tmap_1(A_176, '#skF_2', '#skF_4', D_175, '#skF_5'), D_177) | ~m1_pre_topc(D_175, A_176) | ~m1_pre_topc('#skF_4', A_176) | ~l1_pre_topc(A_176) | ~v2_pre_topc(A_176) | v2_struct_0(A_176))), inference(negUnitSimplification, [status(thm)], [c_46, c_208])).
% 2.79/1.30  tff(c_75, plain, (![A_119, B_120, C_121, D_122]: (k7_relset_1(A_119, B_120, C_121, D_122)=k9_relat_1(C_121, D_122) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.79/1.30  tff(c_78, plain, (![D_122]: (k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_122)=k9_relat_1('#skF_5', D_122))), inference(resolution, [status(thm)], [c_28, c_75])).
% 2.79/1.30  tff(c_20, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')!=k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.79/1.30  tff(c_79, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')!=k9_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_20])).
% 2.79/1.30  tff(c_226, plain, (k9_relat_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')!=k9_relat_1('#skF_5', '#skF_6') | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_220, c_79])).
% 2.79/1.30  tff(c_232, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_34, c_38, c_195, c_226])).
% 2.79/1.30  tff(c_234, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_232])).
% 2.79/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.30  
% 2.79/1.30  Inference rules
% 2.79/1.30  ----------------------
% 2.79/1.30  #Ref     : 0
% 2.79/1.30  #Sup     : 37
% 2.79/1.30  #Fact    : 0
% 2.79/1.30  #Define  : 0
% 2.79/1.30  #Split   : 3
% 2.79/1.30  #Chain   : 0
% 2.79/1.30  #Close   : 0
% 2.79/1.30  
% 2.79/1.30  Ordering : KBO
% 2.79/1.30  
% 2.79/1.30  Simplification rules
% 2.79/1.30  ----------------------
% 2.79/1.30  #Subsume      : 0
% 2.79/1.30  #Demod        : 44
% 2.79/1.30  #Tautology    : 11
% 2.79/1.30  #SimpNegUnit  : 10
% 2.79/1.30  #BackRed      : 1
% 2.79/1.30  
% 2.79/1.30  #Partial instantiations: 0
% 2.79/1.30  #Strategies tried      : 1
% 2.79/1.30  
% 2.79/1.30  Timing (in seconds)
% 2.79/1.30  ----------------------
% 2.79/1.30  Preprocessing        : 0.34
% 2.79/1.30  Parsing              : 0.18
% 2.79/1.30  CNF conversion       : 0.03
% 2.79/1.30  Main loop            : 0.25
% 2.79/1.30  Inferencing          : 0.09
% 2.79/1.30  Reduction            : 0.07
% 2.79/1.30  Demodulation         : 0.05
% 2.79/1.30  BG Simplification    : 0.02
% 2.79/1.30  Subsumption          : 0.04
% 2.79/1.30  Abstraction          : 0.02
% 2.79/1.30  MUC search           : 0.00
% 2.79/1.30  Cooper               : 0.00
% 2.79/1.30  Total                : 0.62
% 2.79/1.30  Index Insertion      : 0.00
% 2.79/1.30  Index Deletion       : 0.00
% 2.79/1.30  Index Matching       : 0.00
% 2.79/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
