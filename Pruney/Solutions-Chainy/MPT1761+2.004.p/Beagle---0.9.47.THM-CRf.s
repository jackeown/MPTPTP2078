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
% DateTime   : Thu Dec  3 10:27:09 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 129 expanded)
%              Number of leaves         :   38 (  65 expanded)
%              Depth                    :   12
%              Number of atoms          :  187 ( 658 expanded)
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
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

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

tff(c_34,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_32,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_30,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_36,plain,(
    m1_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_65,plain,(
    ! [B_120,A_121] :
      ( l1_pre_topc(B_120)
      | ~ m1_pre_topc(B_120,A_121)
      | ~ l1_pre_topc(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_74,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_65])).

tff(c_81,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_74])).

tff(c_28,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_26,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_250,plain,(
    ! [A_176,B_177,C_178,D_179] :
      ( k3_funct_2(A_176,B_177,C_178,D_179) = k1_funct_1(C_178,D_179)
      | ~ m1_subset_1(D_179,A_176)
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177)))
      | ~ v1_funct_2(C_178,A_176,B_177)
      | ~ v1_funct_1(C_178)
      | v1_xboole_0(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_259,plain,(
    ! [B_177,C_178] :
      ( k3_funct_2(u1_struct_0('#skF_5'),B_177,C_178,'#skF_7') = k1_funct_1(C_178,'#skF_7')
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),B_177)))
      | ~ v1_funct_2(C_178,u1_struct_0('#skF_5'),B_177)
      | ~ v1_funct_1(C_178)
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_26,c_250])).

tff(c_269,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_259])).

tff(c_111,plain,(
    ! [B_133,A_134] :
      ( m1_subset_1(u1_struct_0(B_133),k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ m1_pre_topc(B_133,A_134)
      | ~ l1_pre_topc(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_24,plain,(
    r2_hidden('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_89,plain,(
    ! [C_125,A_126,B_127] :
      ( r2_hidden(C_125,A_126)
      | ~ r2_hidden(C_125,B_127)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(A_126)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_95,plain,(
    ! [A_126] :
      ( r2_hidden('#skF_7',A_126)
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_126)) ) ),
    inference(resolution,[status(thm)],[c_24,c_89])).

tff(c_121,plain,(
    ! [A_135] :
      ( r2_hidden('#skF_7',u1_struct_0(A_135))
      | ~ m1_pre_topc('#skF_4',A_135)
      | ~ l1_pre_topc(A_135) ) ),
    inference(resolution,[status(thm)],[c_111,c_95])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_128,plain,(
    ! [A_135] :
      ( ~ v1_xboole_0(u1_struct_0(A_135))
      | ~ m1_pre_topc('#skF_4',A_135)
      | ~ l1_pre_topc(A_135) ) ),
    inference(resolution,[status(thm)],[c_121,c_2])).

tff(c_280,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_269,c_128])).

tff(c_293,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_28,c_280])).

tff(c_412,plain,(
    ! [B_195,C_196] :
      ( k3_funct_2(u1_struct_0('#skF_5'),B_195,C_196,'#skF_7') = k1_funct_1(C_196,'#skF_7')
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),B_195)))
      | ~ v1_funct_2(C_196,u1_struct_0('#skF_5'),B_195)
      | ~ v1_funct_1(C_196) ) ),
    inference(splitRight,[status(thm)],[c_259])).

tff(c_415,plain,
    ( k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_7') = k1_funct_1('#skF_6','#skF_7')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_30,c_412])).

tff(c_418,plain,(
    k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_7') = k1_funct_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_415])).

tff(c_22,plain,(
    k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_7') != k1_funct_1(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_419,plain,(
    k1_funct_1(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_7') != k1_funct_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_22])).

tff(c_84,plain,(
    ! [C_122,A_123,B_124] :
      ( v1_relat_1(C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_88,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_30,c_84])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_52,plain,(
    v2_pre_topc('#skF_2') ),
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

tff(c_189,plain,(
    ! [A_154,B_155,C_156,D_157] :
      ( k2_partfun1(A_154,B_155,C_156,D_157) = k7_relat_1(C_156,D_157)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155)))
      | ~ v1_funct_1(C_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_191,plain,(
    ! [D_157] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',D_157) = k7_relat_1('#skF_6',D_157)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_30,c_189])).

tff(c_194,plain,(
    ! [D_157] : k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',D_157) = k7_relat_1('#skF_6',D_157) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_191])).

tff(c_312,plain,(
    ! [B_188,E_185,D_187,C_186,A_184] :
      ( k3_tmap_1(A_184,B_188,C_186,D_187,E_185) = k2_partfun1(u1_struct_0(C_186),u1_struct_0(B_188),E_185,u1_struct_0(D_187))
      | ~ m1_pre_topc(D_187,C_186)
      | ~ m1_subset_1(E_185,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_186),u1_struct_0(B_188))))
      | ~ v1_funct_2(E_185,u1_struct_0(C_186),u1_struct_0(B_188))
      | ~ v1_funct_1(E_185)
      | ~ m1_pre_topc(D_187,A_184)
      | ~ m1_pre_topc(C_186,A_184)
      | ~ l1_pre_topc(B_188)
      | ~ v2_pre_topc(B_188)
      | v2_struct_0(B_188)
      | ~ l1_pre_topc(A_184)
      | ~ v2_pre_topc(A_184)
      | v2_struct_0(A_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_314,plain,(
    ! [A_184,D_187] :
      ( k3_tmap_1(A_184,'#skF_3','#skF_5',D_187,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_187))
      | ~ m1_pre_topc(D_187,'#skF_5')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_187,A_184)
      | ~ m1_pre_topc('#skF_5',A_184)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_184)
      | ~ v2_pre_topc(A_184)
      | v2_struct_0(A_184) ) ),
    inference(resolution,[status(thm)],[c_30,c_312])).

tff(c_317,plain,(
    ! [D_187,A_184] :
      ( k7_relat_1('#skF_6',u1_struct_0(D_187)) = k3_tmap_1(A_184,'#skF_3','#skF_5',D_187,'#skF_6')
      | ~ m1_pre_topc(D_187,'#skF_5')
      | ~ m1_pre_topc(D_187,A_184)
      | ~ m1_pre_topc('#skF_5',A_184)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_184)
      | ~ v2_pre_topc(A_184)
      | v2_struct_0(A_184) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_34,c_32,c_194,c_314])).

tff(c_334,plain,(
    ! [D_192,A_193] :
      ( k7_relat_1('#skF_6',u1_struct_0(D_192)) = k3_tmap_1(A_193,'#skF_3','#skF_5',D_192,'#skF_6')
      | ~ m1_pre_topc(D_192,'#skF_5')
      | ~ m1_pre_topc(D_192,A_193)
      | ~ m1_pre_topc('#skF_5',A_193)
      | ~ l1_pre_topc(A_193)
      | ~ v2_pre_topc(A_193)
      | v2_struct_0(A_193) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_317])).

tff(c_336,plain,
    ( k7_relat_1('#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_334])).

tff(c_343,plain,
    ( k7_relat_1('#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_36,c_28,c_336])).

tff(c_344,plain,(
    k7_relat_1('#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_343])).

tff(c_8,plain,(
    ! [C_11,B_10,A_9] :
      ( k1_funct_1(k7_relat_1(C_11,B_10),A_9) = k1_funct_1(C_11,A_9)
      | ~ r2_hidden(A_9,B_10)
      | ~ v1_funct_1(C_11)
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_356,plain,(
    ! [A_9] :
      ( k1_funct_1(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),A_9) = k1_funct_1('#skF_6',A_9)
      | ~ r2_hidden(A_9,u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_344,c_8])).

tff(c_364,plain,(
    ! [A_194] :
      ( k1_funct_1(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),A_194) = k1_funct_1('#skF_6',A_194)
      | ~ r2_hidden(A_194,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_34,c_356])).

tff(c_411,plain,(
    k1_funct_1(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_7') = k1_funct_1('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_24,c_364])).

tff(c_424,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_419,c_411])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:22:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.09/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.46  
% 3.09/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.46  %$ v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 3.09/1.46  
% 3.09/1.46  %Foreground sorts:
% 3.09/1.46  
% 3.09/1.46  
% 3.09/1.46  %Background operators:
% 3.09/1.46  
% 3.09/1.46  
% 3.09/1.46  %Foreground operators:
% 3.09/1.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.09/1.46  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.09/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.09/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.09/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.09/1.46  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.09/1.46  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.09/1.46  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.09/1.46  tff('#skF_7', type, '#skF_7': $i).
% 3.09/1.46  tff('#skF_5', type, '#skF_5': $i).
% 3.09/1.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.09/1.46  tff('#skF_6', type, '#skF_6': $i).
% 3.09/1.46  tff('#skF_2', type, '#skF_2': $i).
% 3.09/1.46  tff('#skF_3', type, '#skF_3': $i).
% 3.09/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.09/1.46  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.09/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.09/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.09/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.09/1.46  tff('#skF_4', type, '#skF_4': $i).
% 3.09/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.09/1.46  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.09/1.46  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.09/1.46  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.09/1.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.09/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.09/1.46  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 3.09/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.09/1.46  
% 3.22/1.48  tff(f_159, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (r2_hidden(F, u1_struct_0(C)) => (k3_funct_2(u1_struct_0(D), u1_struct_0(B), E, F) = k1_funct_1(k3_tmap_1(A, B, D, C, E), F)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_tmap_1)).
% 3.22/1.48  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.22/1.48  tff(f_69, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 3.22/1.48  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.22/1.48  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 3.22/1.48  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.22/1.48  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.22/1.48  tff(f_56, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.22/1.48  tff(f_108, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 3.22/1.48  tff(f_46, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, B) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_funct_1)).
% 3.22/1.48  tff(c_34, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.22/1.48  tff(c_32, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.22/1.48  tff(c_30, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.22/1.48  tff(c_50, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.22/1.48  tff(c_36, plain, (m1_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.22/1.48  tff(c_65, plain, (![B_120, A_121]: (l1_pre_topc(B_120) | ~m1_pre_topc(B_120, A_121) | ~l1_pre_topc(A_121))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.22/1.48  tff(c_74, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_36, c_65])).
% 3.22/1.48  tff(c_81, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_74])).
% 3.22/1.48  tff(c_28, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.22/1.48  tff(c_26, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.22/1.48  tff(c_250, plain, (![A_176, B_177, C_178, D_179]: (k3_funct_2(A_176, B_177, C_178, D_179)=k1_funct_1(C_178, D_179) | ~m1_subset_1(D_179, A_176) | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))) | ~v1_funct_2(C_178, A_176, B_177) | ~v1_funct_1(C_178) | v1_xboole_0(A_176))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.22/1.48  tff(c_259, plain, (![B_177, C_178]: (k3_funct_2(u1_struct_0('#skF_5'), B_177, C_178, '#skF_7')=k1_funct_1(C_178, '#skF_7') | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), B_177))) | ~v1_funct_2(C_178, u1_struct_0('#skF_5'), B_177) | ~v1_funct_1(C_178) | v1_xboole_0(u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_26, c_250])).
% 3.22/1.48  tff(c_269, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_259])).
% 3.22/1.48  tff(c_111, plain, (![B_133, A_134]: (m1_subset_1(u1_struct_0(B_133), k1_zfmisc_1(u1_struct_0(A_134))) | ~m1_pre_topc(B_133, A_134) | ~l1_pre_topc(A_134))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.22/1.48  tff(c_24, plain, (r2_hidden('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.22/1.48  tff(c_89, plain, (![C_125, A_126, B_127]: (r2_hidden(C_125, A_126) | ~r2_hidden(C_125, B_127) | ~m1_subset_1(B_127, k1_zfmisc_1(A_126)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.22/1.48  tff(c_95, plain, (![A_126]: (r2_hidden('#skF_7', A_126) | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_126)))), inference(resolution, [status(thm)], [c_24, c_89])).
% 3.22/1.48  tff(c_121, plain, (![A_135]: (r2_hidden('#skF_7', u1_struct_0(A_135)) | ~m1_pre_topc('#skF_4', A_135) | ~l1_pre_topc(A_135))), inference(resolution, [status(thm)], [c_111, c_95])).
% 3.22/1.48  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.22/1.48  tff(c_128, plain, (![A_135]: (~v1_xboole_0(u1_struct_0(A_135)) | ~m1_pre_topc('#skF_4', A_135) | ~l1_pre_topc(A_135))), inference(resolution, [status(thm)], [c_121, c_2])).
% 3.22/1.48  tff(c_280, plain, (~m1_pre_topc('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_269, c_128])).
% 3.22/1.48  tff(c_293, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81, c_28, c_280])).
% 3.22/1.48  tff(c_412, plain, (![B_195, C_196]: (k3_funct_2(u1_struct_0('#skF_5'), B_195, C_196, '#skF_7')=k1_funct_1(C_196, '#skF_7') | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), B_195))) | ~v1_funct_2(C_196, u1_struct_0('#skF_5'), B_195) | ~v1_funct_1(C_196))), inference(splitRight, [status(thm)], [c_259])).
% 3.22/1.48  tff(c_415, plain, (k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_7')=k1_funct_1('#skF_6', '#skF_7') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_30, c_412])).
% 3.22/1.48  tff(c_418, plain, (k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_7')=k1_funct_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_415])).
% 3.22/1.48  tff(c_22, plain, (k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_7')!=k1_funct_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.22/1.48  tff(c_419, plain, (k1_funct_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_418, c_22])).
% 3.22/1.48  tff(c_84, plain, (![C_122, A_123, B_124]: (v1_relat_1(C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.22/1.48  tff(c_88, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_30, c_84])).
% 3.22/1.48  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.22/1.48  tff(c_52, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.22/1.48  tff(c_40, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.22/1.48  tff(c_48, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.22/1.48  tff(c_46, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.22/1.48  tff(c_44, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.22/1.48  tff(c_189, plain, (![A_154, B_155, C_156, D_157]: (k2_partfun1(A_154, B_155, C_156, D_157)=k7_relat_1(C_156, D_157) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))) | ~v1_funct_1(C_156))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.22/1.48  tff(c_191, plain, (![D_157]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', D_157)=k7_relat_1('#skF_6', D_157) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_30, c_189])).
% 3.22/1.48  tff(c_194, plain, (![D_157]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', D_157)=k7_relat_1('#skF_6', D_157))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_191])).
% 3.22/1.48  tff(c_312, plain, (![B_188, E_185, D_187, C_186, A_184]: (k3_tmap_1(A_184, B_188, C_186, D_187, E_185)=k2_partfun1(u1_struct_0(C_186), u1_struct_0(B_188), E_185, u1_struct_0(D_187)) | ~m1_pre_topc(D_187, C_186) | ~m1_subset_1(E_185, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_186), u1_struct_0(B_188)))) | ~v1_funct_2(E_185, u1_struct_0(C_186), u1_struct_0(B_188)) | ~v1_funct_1(E_185) | ~m1_pre_topc(D_187, A_184) | ~m1_pre_topc(C_186, A_184) | ~l1_pre_topc(B_188) | ~v2_pre_topc(B_188) | v2_struct_0(B_188) | ~l1_pre_topc(A_184) | ~v2_pre_topc(A_184) | v2_struct_0(A_184))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.22/1.48  tff(c_314, plain, (![A_184, D_187]: (k3_tmap_1(A_184, '#skF_3', '#skF_5', D_187, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_187)) | ~m1_pre_topc(D_187, '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_187, A_184) | ~m1_pre_topc('#skF_5', A_184) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_184) | ~v2_pre_topc(A_184) | v2_struct_0(A_184))), inference(resolution, [status(thm)], [c_30, c_312])).
% 3.22/1.48  tff(c_317, plain, (![D_187, A_184]: (k7_relat_1('#skF_6', u1_struct_0(D_187))=k3_tmap_1(A_184, '#skF_3', '#skF_5', D_187, '#skF_6') | ~m1_pre_topc(D_187, '#skF_5') | ~m1_pre_topc(D_187, A_184) | ~m1_pre_topc('#skF_5', A_184) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_184) | ~v2_pre_topc(A_184) | v2_struct_0(A_184))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_34, c_32, c_194, c_314])).
% 3.22/1.48  tff(c_334, plain, (![D_192, A_193]: (k7_relat_1('#skF_6', u1_struct_0(D_192))=k3_tmap_1(A_193, '#skF_3', '#skF_5', D_192, '#skF_6') | ~m1_pre_topc(D_192, '#skF_5') | ~m1_pre_topc(D_192, A_193) | ~m1_pre_topc('#skF_5', A_193) | ~l1_pre_topc(A_193) | ~v2_pre_topc(A_193) | v2_struct_0(A_193))), inference(negUnitSimplification, [status(thm)], [c_48, c_317])).
% 3.22/1.48  tff(c_336, plain, (k7_relat_1('#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6') | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_334])).
% 3.22/1.48  tff(c_343, plain, (k7_relat_1('#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_36, c_28, c_336])).
% 3.22/1.48  tff(c_344, plain, (k7_relat_1('#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_54, c_343])).
% 3.22/1.48  tff(c_8, plain, (![C_11, B_10, A_9]: (k1_funct_1(k7_relat_1(C_11, B_10), A_9)=k1_funct_1(C_11, A_9) | ~r2_hidden(A_9, B_10) | ~v1_funct_1(C_11) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.22/1.48  tff(c_356, plain, (![A_9]: (k1_funct_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), A_9)=k1_funct_1('#skF_6', A_9) | ~r2_hidden(A_9, u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_344, c_8])).
% 3.22/1.48  tff(c_364, plain, (![A_194]: (k1_funct_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), A_194)=k1_funct_1('#skF_6', A_194) | ~r2_hidden(A_194, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_34, c_356])).
% 3.22/1.48  tff(c_411, plain, (k1_funct_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_7')=k1_funct_1('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_24, c_364])).
% 3.22/1.48  tff(c_424, plain, $false, inference(negUnitSimplification, [status(thm)], [c_419, c_411])).
% 3.22/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.48  
% 3.22/1.48  Inference rules
% 3.22/1.48  ----------------------
% 3.22/1.48  #Ref     : 0
% 3.22/1.48  #Sup     : 74
% 3.22/1.48  #Fact    : 0
% 3.22/1.48  #Define  : 0
% 3.22/1.48  #Split   : 5
% 3.22/1.48  #Chain   : 0
% 3.22/1.48  #Close   : 0
% 3.22/1.48  
% 3.22/1.48  Ordering : KBO
% 3.22/1.48  
% 3.22/1.48  Simplification rules
% 3.22/1.48  ----------------------
% 3.22/1.48  #Subsume      : 7
% 3.22/1.48  #Demod        : 42
% 3.22/1.48  #Tautology    : 10
% 3.22/1.48  #SimpNegUnit  : 6
% 3.22/1.48  #BackRed      : 1
% 3.22/1.48  
% 3.22/1.48  #Partial instantiations: 0
% 3.22/1.48  #Strategies tried      : 1
% 3.22/1.48  
% 3.22/1.48  Timing (in seconds)
% 3.22/1.48  ----------------------
% 3.22/1.48  Preprocessing        : 0.36
% 3.22/1.48  Parsing              : 0.19
% 3.22/1.48  CNF conversion       : 0.04
% 3.22/1.48  Main loop            : 0.34
% 3.22/1.48  Inferencing          : 0.12
% 3.22/1.48  Reduction            : 0.10
% 3.22/1.48  Demodulation         : 0.07
% 3.22/1.48  BG Simplification    : 0.02
% 3.22/1.48  Subsumption          : 0.07
% 3.22/1.48  Abstraction          : 0.02
% 3.22/1.48  MUC search           : 0.00
% 3.22/1.48  Cooper               : 0.00
% 3.22/1.48  Total                : 0.74
% 3.22/1.48  Index Insertion      : 0.00
% 3.22/1.48  Index Deletion       : 0.00
% 3.22/1.48  Index Matching       : 0.00
% 3.22/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
