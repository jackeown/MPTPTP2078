%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:14 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 124 expanded)
%              Number of leaves         :   34 (  64 expanded)
%              Depth                    :   13
%              Number of atoms          :  206 ( 717 expanded)
%              Number of equality atoms :   29 (  59 expanded)
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
                              ( m1_subset_1(F,k1_zfmisc_1(u1_struct_0(D)))
                             => ( r1_tarski(F,u1_struct_0(C))
                               => k7_relset_1(u1_struct_0(D),u1_struct_0(B),E,F) = k7_relset_1(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,D,C,E),F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_tmap_1)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_85,axiom,(
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

tff(f_53,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( r1_tarski(C,B)
         => k9_relat_1(A,C) = k9_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_2)).

tff(f_115,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).

tff(f_38,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_50,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_34,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_38,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_22,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_28,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

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

tff(c_32,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_26,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_44,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_42,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_30,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_89,plain,(
    ! [A_124,B_125,C_126,D_127] :
      ( k2_partfun1(A_124,B_125,C_126,D_127) = k7_relat_1(C_126,D_127)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125)))
      | ~ v1_funct_1(C_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

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
    inference(cnfTransformation,[status(thm)],[f_85])).

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

tff(c_10,plain,(
    ! [A_14,B_17,C_18] :
      ( k9_relat_1(k7_relat_1(A_14,B_17),C_18) = k9_relat_1(A_14,C_18)
      | ~ r1_tarski(C_18,B_17)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_182,plain,(
    ! [C_18] :
      ( k9_relat_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),C_18) = k9_relat_1('#skF_5',C_18)
      | ~ r1_tarski(C_18,u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_10])).

tff(c_191,plain,(
    ! [C_162] :
      ( k9_relat_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),C_162) = k9_relat_1('#skF_5',C_162)
      | ~ r1_tarski(C_162,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_32,c_182])).

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
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8,D_9] :
      ( k7_relset_1(A_6,B_7,C_8,D_9) = k9_relat_1(C_8,D_9)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_200,plain,(
    ! [A_163,B_166,D_165,E_167,C_168,D_164] :
      ( k7_relset_1(u1_struct_0(D_164),u1_struct_0(B_166),k3_tmap_1(A_163,B_166,C_168,D_164,E_167),D_165) = k9_relat_1(k3_tmap_1(A_163,B_166,C_168,D_164,E_167),D_165)
      | ~ m1_subset_1(E_167,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_168),u1_struct_0(B_166))))
      | ~ v1_funct_2(E_167,u1_struct_0(C_168),u1_struct_0(B_166))
      | ~ v1_funct_1(E_167)
      | ~ m1_pre_topc(D_164,A_163)
      | ~ m1_pre_topc(C_168,A_163)
      | ~ l1_pre_topc(B_166)
      | ~ v2_pre_topc(B_166)
      | v2_struct_0(B_166)
      | ~ l1_pre_topc(A_163)
      | ~ v2_pre_topc(A_163)
      | v2_struct_0(A_163) ) ),
    inference(resolution,[status(thm)],[c_120,c_6])).

tff(c_204,plain,(
    ! [D_164,A_163,D_165] :
      ( k7_relset_1(u1_struct_0(D_164),u1_struct_0('#skF_2'),k3_tmap_1(A_163,'#skF_2','#skF_4',D_164,'#skF_5'),D_165) = k9_relat_1(k3_tmap_1(A_163,'#skF_2','#skF_4',D_164,'#skF_5'),D_165)
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
    ! [D_164,A_163,D_165] :
      ( k7_relset_1(u1_struct_0(D_164),u1_struct_0('#skF_2'),k3_tmap_1(A_163,'#skF_2','#skF_4',D_164,'#skF_5'),D_165) = k9_relat_1(k3_tmap_1(A_163,'#skF_2','#skF_4',D_164,'#skF_5'),D_165)
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

tff(c_66,plain,(
    ! [A_116,B_117,C_118,D_119] :
      ( k7_relset_1(A_116,B_117,C_118,D_119) = k9_relat_1(C_118,D_119)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_69,plain,(
    ! [D_119] : k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_119) = k9_relat_1('#skF_5',D_119) ),
    inference(resolution,[status(thm)],[c_28,c_66])).

tff(c_20,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') != k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_70,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') != k9_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_20])).

tff(c_226,plain,
    ( k9_relat_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') != k9_relat_1('#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_70])).

tff(c_232,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_34,c_38,c_195,c_226])).

tff(c_234,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_232])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:50:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.34  
% 2.50/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.34  %$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k7_relset_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.50/1.34  
% 2.50/1.34  %Foreground sorts:
% 2.50/1.34  
% 2.50/1.34  
% 2.50/1.34  %Background operators:
% 2.50/1.34  
% 2.50/1.34  
% 2.50/1.34  %Foreground operators:
% 2.50/1.34  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.50/1.34  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 2.50/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.50/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.34  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.50/1.34  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.50/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.50/1.34  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.50/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.50/1.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.50/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.50/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.50/1.34  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.50/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.50/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.50/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.50/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.50/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.50/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.50/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.34  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.50/1.34  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.50/1.34  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.50/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.50/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.50/1.34  
% 2.76/1.36  tff(f_159, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (r1_tarski(F, u1_struct_0(C)) => (k7_relset_1(u1_struct_0(D), u1_struct_0(B), E, F) = k7_relset_1(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, E), F)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_tmap_1)).
% 2.76/1.36  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.76/1.36  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.76/1.36  tff(f_44, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.76/1.36  tff(f_85, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 2.76/1.36  tff(f_53, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(C, B) => (k9_relat_1(A, C) = k9_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_funct_2)).
% 2.76/1.36  tff(f_115, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 2.76/1.36  tff(f_38, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.76/1.36  tff(c_52, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.76/1.36  tff(c_50, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.76/1.36  tff(c_48, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.76/1.36  tff(c_34, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.76/1.36  tff(c_38, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.76/1.36  tff(c_22, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.76/1.36  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.76/1.36  tff(c_28, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.76/1.36  tff(c_54, plain, (![B_114, A_115]: (v1_relat_1(B_114) | ~m1_subset_1(B_114, k1_zfmisc_1(A_115)) | ~v1_relat_1(A_115))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.76/1.36  tff(c_57, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_28, c_54])).
% 2.76/1.36  tff(c_63, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_57])).
% 2.76/1.36  tff(c_32, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.76/1.36  tff(c_26, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.76/1.36  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.76/1.36  tff(c_44, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.76/1.36  tff(c_42, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.76/1.36  tff(c_30, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.76/1.36  tff(c_89, plain, (![A_124, B_125, C_126, D_127]: (k2_partfun1(A_124, B_125, C_126, D_127)=k7_relat_1(C_126, D_127) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))) | ~v1_funct_1(C_126))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.76/1.36  tff(c_91, plain, (![D_127]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_127)=k7_relat_1('#skF_5', D_127) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_28, c_89])).
% 2.76/1.36  tff(c_94, plain, (![D_127]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_127)=k7_relat_1('#skF_5', D_127))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_91])).
% 2.76/1.36  tff(c_150, plain, (![C_155, E_159, D_156, A_157, B_158]: (k3_tmap_1(A_157, B_158, C_155, D_156, E_159)=k2_partfun1(u1_struct_0(C_155), u1_struct_0(B_158), E_159, u1_struct_0(D_156)) | ~m1_pre_topc(D_156, C_155) | ~m1_subset_1(E_159, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_155), u1_struct_0(B_158)))) | ~v1_funct_2(E_159, u1_struct_0(C_155), u1_struct_0(B_158)) | ~v1_funct_1(E_159) | ~m1_pre_topc(D_156, A_157) | ~m1_pre_topc(C_155, A_157) | ~l1_pre_topc(B_158) | ~v2_pre_topc(B_158) | v2_struct_0(B_158) | ~l1_pre_topc(A_157) | ~v2_pre_topc(A_157) | v2_struct_0(A_157))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.76/1.36  tff(c_154, plain, (![A_157, D_156]: (k3_tmap_1(A_157, '#skF_2', '#skF_4', D_156, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_156)) | ~m1_pre_topc(D_156, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_156, A_157) | ~m1_pre_topc('#skF_4', A_157) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_157) | ~v2_pre_topc(A_157) | v2_struct_0(A_157))), inference(resolution, [status(thm)], [c_28, c_150])).
% 2.76/1.36  tff(c_158, plain, (![D_156, A_157]: (k7_relat_1('#skF_5', u1_struct_0(D_156))=k3_tmap_1(A_157, '#skF_2', '#skF_4', D_156, '#skF_5') | ~m1_pre_topc(D_156, '#skF_4') | ~m1_pre_topc(D_156, A_157) | ~m1_pre_topc('#skF_4', A_157) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_157) | ~v2_pre_topc(A_157) | v2_struct_0(A_157))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_32, c_30, c_94, c_154])).
% 2.76/1.36  tff(c_160, plain, (![D_160, A_161]: (k7_relat_1('#skF_5', u1_struct_0(D_160))=k3_tmap_1(A_161, '#skF_2', '#skF_4', D_160, '#skF_5') | ~m1_pre_topc(D_160, '#skF_4') | ~m1_pre_topc(D_160, A_161) | ~m1_pre_topc('#skF_4', A_161) | ~l1_pre_topc(A_161) | ~v2_pre_topc(A_161) | v2_struct_0(A_161))), inference(negUnitSimplification, [status(thm)], [c_46, c_158])).
% 2.76/1.36  tff(c_166, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_160])).
% 2.76/1.36  tff(c_177, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_34, c_26, c_166])).
% 2.76/1.36  tff(c_178, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_52, c_177])).
% 2.76/1.36  tff(c_10, plain, (![A_14, B_17, C_18]: (k9_relat_1(k7_relat_1(A_14, B_17), C_18)=k9_relat_1(A_14, C_18) | ~r1_tarski(C_18, B_17) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.76/1.36  tff(c_182, plain, (![C_18]: (k9_relat_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), C_18)=k9_relat_1('#skF_5', C_18) | ~r1_tarski(C_18, u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_178, c_10])).
% 2.76/1.36  tff(c_191, plain, (![C_162]: (k9_relat_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), C_162)=k9_relat_1('#skF_5', C_162) | ~r1_tarski(C_162, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_32, c_182])).
% 2.76/1.36  tff(c_195, plain, (k9_relat_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')=k9_relat_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_22, c_191])).
% 2.76/1.36  tff(c_120, plain, (![E_143, A_144, D_147, C_145, B_146]: (m1_subset_1(k3_tmap_1(A_144, B_146, C_145, D_147, E_143), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_147), u1_struct_0(B_146)))) | ~m1_subset_1(E_143, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_145), u1_struct_0(B_146)))) | ~v1_funct_2(E_143, u1_struct_0(C_145), u1_struct_0(B_146)) | ~v1_funct_1(E_143) | ~m1_pre_topc(D_147, A_144) | ~m1_pre_topc(C_145, A_144) | ~l1_pre_topc(B_146) | ~v2_pre_topc(B_146) | v2_struct_0(B_146) | ~l1_pre_topc(A_144) | ~v2_pre_topc(A_144) | v2_struct_0(A_144))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.76/1.36  tff(c_6, plain, (![A_6, B_7, C_8, D_9]: (k7_relset_1(A_6, B_7, C_8, D_9)=k9_relat_1(C_8, D_9) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.76/1.36  tff(c_200, plain, (![A_163, B_166, D_165, E_167, C_168, D_164]: (k7_relset_1(u1_struct_0(D_164), u1_struct_0(B_166), k3_tmap_1(A_163, B_166, C_168, D_164, E_167), D_165)=k9_relat_1(k3_tmap_1(A_163, B_166, C_168, D_164, E_167), D_165) | ~m1_subset_1(E_167, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_168), u1_struct_0(B_166)))) | ~v1_funct_2(E_167, u1_struct_0(C_168), u1_struct_0(B_166)) | ~v1_funct_1(E_167) | ~m1_pre_topc(D_164, A_163) | ~m1_pre_topc(C_168, A_163) | ~l1_pre_topc(B_166) | ~v2_pre_topc(B_166) | v2_struct_0(B_166) | ~l1_pre_topc(A_163) | ~v2_pre_topc(A_163) | v2_struct_0(A_163))), inference(resolution, [status(thm)], [c_120, c_6])).
% 2.76/1.36  tff(c_204, plain, (![D_164, A_163, D_165]: (k7_relset_1(u1_struct_0(D_164), u1_struct_0('#skF_2'), k3_tmap_1(A_163, '#skF_2', '#skF_4', D_164, '#skF_5'), D_165)=k9_relat_1(k3_tmap_1(A_163, '#skF_2', '#skF_4', D_164, '#skF_5'), D_165) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_164, A_163) | ~m1_pre_topc('#skF_4', A_163) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_163) | ~v2_pre_topc(A_163) | v2_struct_0(A_163))), inference(resolution, [status(thm)], [c_28, c_200])).
% 2.76/1.36  tff(c_208, plain, (![D_164, A_163, D_165]: (k7_relset_1(u1_struct_0(D_164), u1_struct_0('#skF_2'), k3_tmap_1(A_163, '#skF_2', '#skF_4', D_164, '#skF_5'), D_165)=k9_relat_1(k3_tmap_1(A_163, '#skF_2', '#skF_4', D_164, '#skF_5'), D_165) | ~m1_pre_topc(D_164, A_163) | ~m1_pre_topc('#skF_4', A_163) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_163) | ~v2_pre_topc(A_163) | v2_struct_0(A_163))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_32, c_30, c_204])).
% 2.76/1.36  tff(c_220, plain, (![D_175, A_176, D_177]: (k7_relset_1(u1_struct_0(D_175), u1_struct_0('#skF_2'), k3_tmap_1(A_176, '#skF_2', '#skF_4', D_175, '#skF_5'), D_177)=k9_relat_1(k3_tmap_1(A_176, '#skF_2', '#skF_4', D_175, '#skF_5'), D_177) | ~m1_pre_topc(D_175, A_176) | ~m1_pre_topc('#skF_4', A_176) | ~l1_pre_topc(A_176) | ~v2_pre_topc(A_176) | v2_struct_0(A_176))), inference(negUnitSimplification, [status(thm)], [c_46, c_208])).
% 2.76/1.36  tff(c_66, plain, (![A_116, B_117, C_118, D_119]: (k7_relset_1(A_116, B_117, C_118, D_119)=k9_relat_1(C_118, D_119) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.76/1.36  tff(c_69, plain, (![D_119]: (k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_119)=k9_relat_1('#skF_5', D_119))), inference(resolution, [status(thm)], [c_28, c_66])).
% 2.76/1.36  tff(c_20, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')!=k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.76/1.36  tff(c_70, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')!=k9_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_20])).
% 2.76/1.36  tff(c_226, plain, (k9_relat_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')!=k9_relat_1('#skF_5', '#skF_6') | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_220, c_70])).
% 2.76/1.36  tff(c_232, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_34, c_38, c_195, c_226])).
% 2.76/1.36  tff(c_234, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_232])).
% 2.76/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.36  
% 2.76/1.36  Inference rules
% 2.76/1.36  ----------------------
% 2.76/1.36  #Ref     : 0
% 2.76/1.36  #Sup     : 37
% 2.76/1.36  #Fact    : 0
% 2.76/1.36  #Define  : 0
% 2.76/1.36  #Split   : 3
% 2.76/1.36  #Chain   : 0
% 2.76/1.36  #Close   : 0
% 2.76/1.36  
% 2.76/1.36  Ordering : KBO
% 2.76/1.36  
% 2.76/1.36  Simplification rules
% 2.76/1.36  ----------------------
% 2.76/1.36  #Subsume      : 0
% 2.76/1.36  #Demod        : 45
% 2.76/1.36  #Tautology    : 11
% 2.76/1.36  #SimpNegUnit  : 10
% 2.76/1.36  #BackRed      : 1
% 2.76/1.36  
% 2.76/1.36  #Partial instantiations: 0
% 2.76/1.36  #Strategies tried      : 1
% 2.76/1.36  
% 2.76/1.36  Timing (in seconds)
% 2.76/1.36  ----------------------
% 2.76/1.37  Preprocessing        : 0.35
% 2.76/1.37  Parsing              : 0.18
% 2.76/1.37  CNF conversion       : 0.03
% 2.76/1.37  Main loop            : 0.24
% 2.76/1.37  Inferencing          : 0.09
% 2.76/1.37  Reduction            : 0.07
% 2.76/1.37  Demodulation         : 0.05
% 2.76/1.37  BG Simplification    : 0.02
% 2.76/1.37  Subsumption          : 0.04
% 2.76/1.37  Abstraction          : 0.02
% 2.76/1.37  MUC search           : 0.00
% 2.76/1.37  Cooper               : 0.00
% 2.76/1.37  Total                : 0.64
% 2.76/1.37  Index Insertion      : 0.00
% 2.76/1.37  Index Deletion       : 0.00
% 2.76/1.37  Index Matching       : 0.00
% 2.76/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
