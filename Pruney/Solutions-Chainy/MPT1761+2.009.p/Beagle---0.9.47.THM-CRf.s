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
% DateTime   : Thu Dec  3 10:27:09 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 143 expanded)
%              Number of leaves         :   43 (  72 expanded)
%              Depth                    :   12
%              Number of atoms          :  206 ( 713 expanded)
%              Number of equality atoms :   29 (  60 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_171,negated_conjecture,(
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

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_127,axiom,(
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

tff(f_33,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,B)
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_funct_1)).

tff(c_40,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_38,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_36,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_46,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_34,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_32,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_135,plain,(
    ! [A_148,B_149,C_150,D_151] :
      ( k3_funct_2(A_148,B_149,C_150,D_151) = k1_funct_1(C_150,D_151)
      | ~ m1_subset_1(D_151,A_148)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_148,B_149)))
      | ~ v1_funct_2(C_150,A_148,B_149)
      | ~ v1_funct_1(C_150)
      | v1_xboole_0(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_141,plain,(
    ! [B_149,C_150] :
      ( k3_funct_2(u1_struct_0('#skF_5'),B_149,C_150,'#skF_7') = k1_funct_1(C_150,'#skF_7')
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),B_149)))
      | ~ v1_funct_2(C_150,u1_struct_0('#skF_5'),B_149)
      | ~ v1_funct_1(C_150)
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_32,c_135])).

tff(c_142,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_141])).

tff(c_10,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_146,plain,(
    u1_struct_0('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_142,c_10])).

tff(c_58,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_56,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_42,plain,(
    m1_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_111,plain,(
    ! [B_140,C_141,A_142] :
      ( r1_tarski(u1_struct_0(B_140),u1_struct_0(C_141))
      | ~ m1_pre_topc(B_140,C_141)
      | ~ m1_pre_topc(C_141,A_142)
      | ~ m1_pre_topc(B_140,A_142)
      | ~ l1_pre_topc(A_142)
      | ~ v2_pre_topc(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_115,plain,(
    ! [B_140] :
      ( r1_tarski(u1_struct_0(B_140),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_140,'#skF_5')
      | ~ m1_pre_topc(B_140,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_111])).

tff(c_123,plain,(
    ! [B_140] :
      ( r1_tarski(u1_struct_0(B_140),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_140,'#skF_5')
      | ~ m1_pre_topc(B_140,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_115])).

tff(c_228,plain,(
    ! [B_159] :
      ( r1_tarski(u1_struct_0(B_159),k1_xboole_0)
      | ~ m1_pre_topc(B_159,'#skF_5')
      | ~ m1_pre_topc(B_159,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_123])).

tff(c_6,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_74,plain,(
    ! [B_127,A_128] :
      ( ~ r1_xboole_0(B_127,A_128)
      | ~ r1_tarski(B_127,A_128)
      | v1_xboole_0(B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_78,plain,(
    ! [A_5] :
      ( ~ r1_tarski(A_5,k1_xboole_0)
      | v1_xboole_0(A_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_74])).

tff(c_239,plain,(
    ! [B_160] :
      ( v1_xboole_0(u1_struct_0(B_160))
      | ~ m1_pre_topc(B_160,'#skF_5')
      | ~ m1_pre_topc(B_160,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_228,c_78])).

tff(c_30,plain,(
    r2_hidden('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_64,plain,(
    ! [B_124,A_125] :
      ( ~ r2_hidden(B_124,A_125)
      | ~ v1_xboole_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_30,c_64])).

tff(c_242,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_239,c_68])).

tff(c_252,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_34,c_242])).

tff(c_407,plain,(
    ! [B_177,C_178] :
      ( k3_funct_2(u1_struct_0('#skF_5'),B_177,C_178,'#skF_7') = k1_funct_1(C_178,'#skF_7')
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),B_177)))
      | ~ v1_funct_2(C_178,u1_struct_0('#skF_5'),B_177)
      | ~ v1_funct_1(C_178) ) ),
    inference(splitRight,[status(thm)],[c_141])).

tff(c_410,plain,
    ( k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_7') = k1_funct_1('#skF_6','#skF_7')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_407])).

tff(c_413,plain,(
    k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_7') = k1_funct_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_410])).

tff(c_28,plain,(
    k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_7') != k1_funct_1(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_414,plain,(
    k1_funct_1(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_7') != k1_funct_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_28])).

tff(c_14,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_80,plain,(
    ! [B_130,A_131] :
      ( v1_relat_1(B_130)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(A_131))
      | ~ v1_relat_1(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_83,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_36,c_80])).

tff(c_86,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_83])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_52,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_50,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_96,plain,(
    ! [A_135,B_136,C_137,D_138] :
      ( k2_partfun1(A_135,B_136,C_137,D_138) = k7_relat_1(C_137,D_138)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136)))
      | ~ v1_funct_1(C_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_98,plain,(
    ! [D_138] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',D_138) = k7_relat_1('#skF_6',D_138)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_36,c_96])).

tff(c_101,plain,(
    ! [D_138] : k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',D_138) = k7_relat_1('#skF_6',D_138) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_98])).

tff(c_420,plain,(
    ! [A_181,D_183,B_185,C_184,E_182] :
      ( k3_tmap_1(A_181,B_185,C_184,D_183,E_182) = k2_partfun1(u1_struct_0(C_184),u1_struct_0(B_185),E_182,u1_struct_0(D_183))
      | ~ m1_pre_topc(D_183,C_184)
      | ~ m1_subset_1(E_182,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_184),u1_struct_0(B_185))))
      | ~ v1_funct_2(E_182,u1_struct_0(C_184),u1_struct_0(B_185))
      | ~ v1_funct_1(E_182)
      | ~ m1_pre_topc(D_183,A_181)
      | ~ m1_pre_topc(C_184,A_181)
      | ~ l1_pre_topc(B_185)
      | ~ v2_pre_topc(B_185)
      | v2_struct_0(B_185)
      | ~ l1_pre_topc(A_181)
      | ~ v2_pre_topc(A_181)
      | v2_struct_0(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_422,plain,(
    ! [A_181,D_183] :
      ( k3_tmap_1(A_181,'#skF_3','#skF_5',D_183,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_183))
      | ~ m1_pre_topc(D_183,'#skF_5')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_183,A_181)
      | ~ m1_pre_topc('#skF_5',A_181)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_181)
      | ~ v2_pre_topc(A_181)
      | v2_struct_0(A_181) ) ),
    inference(resolution,[status(thm)],[c_36,c_420])).

tff(c_425,plain,(
    ! [D_183,A_181] :
      ( k7_relat_1('#skF_6',u1_struct_0(D_183)) = k3_tmap_1(A_181,'#skF_3','#skF_5',D_183,'#skF_6')
      | ~ m1_pre_topc(D_183,'#skF_5')
      | ~ m1_pre_topc(D_183,A_181)
      | ~ m1_pre_topc('#skF_5',A_181)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_181)
      | ~ v2_pre_topc(A_181)
      | v2_struct_0(A_181) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_40,c_38,c_101,c_422])).

tff(c_427,plain,(
    ! [D_186,A_187] :
      ( k7_relat_1('#skF_6',u1_struct_0(D_186)) = k3_tmap_1(A_187,'#skF_3','#skF_5',D_186,'#skF_6')
      | ~ m1_pre_topc(D_186,'#skF_5')
      | ~ m1_pre_topc(D_186,A_187)
      | ~ m1_pre_topc('#skF_5',A_187)
      | ~ l1_pre_topc(A_187)
      | ~ v2_pre_topc(A_187)
      | v2_struct_0(A_187) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_425])).

tff(c_429,plain,
    ( k7_relat_1('#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_427])).

tff(c_436,plain,
    ( k7_relat_1('#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_42,c_34,c_429])).

tff(c_437,plain,(
    k7_relat_1('#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_436])).

tff(c_16,plain,(
    ! [C_16,B_15,A_14] :
      ( k1_funct_1(k7_relat_1(C_16,B_15),A_14) = k1_funct_1(C_16,A_14)
      | ~ r2_hidden(A_14,B_15)
      | ~ v1_funct_1(C_16)
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_449,plain,(
    ! [A_14] :
      ( k1_funct_1(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),A_14) = k1_funct_1('#skF_6',A_14)
      | ~ r2_hidden(A_14,u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_437,c_16])).

tff(c_456,plain,(
    ! [A_188] :
      ( k1_funct_1(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),A_188) = k1_funct_1('#skF_6',A_188)
      | ~ r2_hidden(A_188,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_40,c_449])).

tff(c_463,plain,(
    k1_funct_1(k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_7') = k1_funct_1('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_30,c_456])).

tff(c_470,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_414,c_463])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:07:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.82/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.45  
% 2.82/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.45  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 3.19/1.45  
% 3.19/1.45  %Foreground sorts:
% 3.19/1.45  
% 3.19/1.45  
% 3.19/1.45  %Background operators:
% 3.19/1.45  
% 3.19/1.45  
% 3.19/1.45  %Foreground operators:
% 3.19/1.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.19/1.45  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.19/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.19/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.19/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.19/1.45  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.19/1.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.19/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.19/1.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.19/1.45  tff('#skF_7', type, '#skF_7': $i).
% 3.19/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.19/1.45  tff('#skF_5', type, '#skF_5': $i).
% 3.19/1.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.19/1.45  tff('#skF_6', type, '#skF_6': $i).
% 3.19/1.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.19/1.45  tff('#skF_2', type, '#skF_2': $i).
% 3.19/1.45  tff('#skF_3', type, '#skF_3': $i).
% 3.19/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.19/1.45  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.19/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.19/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.19/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.19/1.45  tff('#skF_4', type, '#skF_4': $i).
% 3.19/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.19/1.45  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.19/1.45  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.19/1.45  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.19/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.19/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.19/1.45  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 3.19/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.19/1.45  
% 3.28/1.47  tff(f_171, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (r2_hidden(F, u1_struct_0(C)) => (k3_funct_2(u1_struct_0(D), u1_struct_0(B), E, F) = k1_funct_1(k3_tmap_1(A, B, D, C, E), F)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_tmap_1)).
% 3.28/1.47  tff(f_81, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 3.28/1.47  tff(f_45, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_boole)).
% 3.28/1.47  tff(f_127, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 3.28/1.47  tff(f_33, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.28/1.47  tff(f_41, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.28/1.47  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.28/1.47  tff(f_54, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.28/1.47  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.28/1.47  tff(f_68, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.28/1.47  tff(f_113, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 3.28/1.47  tff(f_62, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, B) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_funct_1)).
% 3.28/1.47  tff(c_40, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.28/1.47  tff(c_38, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.28/1.47  tff(c_36, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.28/1.47  tff(c_46, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.28/1.47  tff(c_34, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.28/1.47  tff(c_32, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.28/1.47  tff(c_135, plain, (![A_148, B_149, C_150, D_151]: (k3_funct_2(A_148, B_149, C_150, D_151)=k1_funct_1(C_150, D_151) | ~m1_subset_1(D_151, A_148) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_148, B_149))) | ~v1_funct_2(C_150, A_148, B_149) | ~v1_funct_1(C_150) | v1_xboole_0(A_148))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.28/1.47  tff(c_141, plain, (![B_149, C_150]: (k3_funct_2(u1_struct_0('#skF_5'), B_149, C_150, '#skF_7')=k1_funct_1(C_150, '#skF_7') | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), B_149))) | ~v1_funct_2(C_150, u1_struct_0('#skF_5'), B_149) | ~v1_funct_1(C_150) | v1_xboole_0(u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_32, c_135])).
% 3.28/1.47  tff(c_142, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_141])).
% 3.28/1.47  tff(c_10, plain, (![A_8]: (k1_xboole_0=A_8 | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.28/1.47  tff(c_146, plain, (u1_struct_0('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_142, c_10])).
% 3.28/1.47  tff(c_58, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.28/1.47  tff(c_56, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.28/1.47  tff(c_42, plain, (m1_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.28/1.47  tff(c_111, plain, (![B_140, C_141, A_142]: (r1_tarski(u1_struct_0(B_140), u1_struct_0(C_141)) | ~m1_pre_topc(B_140, C_141) | ~m1_pre_topc(C_141, A_142) | ~m1_pre_topc(B_140, A_142) | ~l1_pre_topc(A_142) | ~v2_pre_topc(A_142))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.28/1.47  tff(c_115, plain, (![B_140]: (r1_tarski(u1_struct_0(B_140), u1_struct_0('#skF_5')) | ~m1_pre_topc(B_140, '#skF_5') | ~m1_pre_topc(B_140, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_111])).
% 3.28/1.47  tff(c_123, plain, (![B_140]: (r1_tarski(u1_struct_0(B_140), u1_struct_0('#skF_5')) | ~m1_pre_topc(B_140, '#skF_5') | ~m1_pre_topc(B_140, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_115])).
% 3.28/1.47  tff(c_228, plain, (![B_159]: (r1_tarski(u1_struct_0(B_159), k1_xboole_0) | ~m1_pre_topc(B_159, '#skF_5') | ~m1_pre_topc(B_159, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_123])).
% 3.28/1.47  tff(c_6, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.28/1.47  tff(c_74, plain, (![B_127, A_128]: (~r1_xboole_0(B_127, A_128) | ~r1_tarski(B_127, A_128) | v1_xboole_0(B_127))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.28/1.47  tff(c_78, plain, (![A_5]: (~r1_tarski(A_5, k1_xboole_0) | v1_xboole_0(A_5))), inference(resolution, [status(thm)], [c_6, c_74])).
% 3.28/1.47  tff(c_239, plain, (![B_160]: (v1_xboole_0(u1_struct_0(B_160)) | ~m1_pre_topc(B_160, '#skF_5') | ~m1_pre_topc(B_160, '#skF_2'))), inference(resolution, [status(thm)], [c_228, c_78])).
% 3.28/1.47  tff(c_30, plain, (r2_hidden('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.28/1.47  tff(c_64, plain, (![B_124, A_125]: (~r2_hidden(B_124, A_125) | ~v1_xboole_0(A_125))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.28/1.47  tff(c_68, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_64])).
% 3.28/1.47  tff(c_242, plain, (~m1_pre_topc('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_239, c_68])).
% 3.28/1.48  tff(c_252, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_34, c_242])).
% 3.28/1.48  tff(c_407, plain, (![B_177, C_178]: (k3_funct_2(u1_struct_0('#skF_5'), B_177, C_178, '#skF_7')=k1_funct_1(C_178, '#skF_7') | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), B_177))) | ~v1_funct_2(C_178, u1_struct_0('#skF_5'), B_177) | ~v1_funct_1(C_178))), inference(splitRight, [status(thm)], [c_141])).
% 3.28/1.48  tff(c_410, plain, (k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_7')=k1_funct_1('#skF_6', '#skF_7') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_36, c_407])).
% 3.28/1.48  tff(c_413, plain, (k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_7')=k1_funct_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_410])).
% 3.28/1.48  tff(c_28, plain, (k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_7')!=k1_funct_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.28/1.48  tff(c_414, plain, (k1_funct_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_413, c_28])).
% 3.28/1.48  tff(c_14, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.28/1.48  tff(c_80, plain, (![B_130, A_131]: (v1_relat_1(B_130) | ~m1_subset_1(B_130, k1_zfmisc_1(A_131)) | ~v1_relat_1(A_131))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.28/1.48  tff(c_83, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_36, c_80])).
% 3.28/1.48  tff(c_86, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_83])).
% 3.28/1.48  tff(c_60, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.28/1.48  tff(c_54, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.28/1.48  tff(c_52, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.28/1.48  tff(c_50, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.28/1.48  tff(c_96, plain, (![A_135, B_136, C_137, D_138]: (k2_partfun1(A_135, B_136, C_137, D_138)=k7_relat_1(C_137, D_138) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))) | ~v1_funct_1(C_137))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.28/1.48  tff(c_98, plain, (![D_138]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', D_138)=k7_relat_1('#skF_6', D_138) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_36, c_96])).
% 3.28/1.48  tff(c_101, plain, (![D_138]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', D_138)=k7_relat_1('#skF_6', D_138))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_98])).
% 3.28/1.48  tff(c_420, plain, (![A_181, D_183, B_185, C_184, E_182]: (k3_tmap_1(A_181, B_185, C_184, D_183, E_182)=k2_partfun1(u1_struct_0(C_184), u1_struct_0(B_185), E_182, u1_struct_0(D_183)) | ~m1_pre_topc(D_183, C_184) | ~m1_subset_1(E_182, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_184), u1_struct_0(B_185)))) | ~v1_funct_2(E_182, u1_struct_0(C_184), u1_struct_0(B_185)) | ~v1_funct_1(E_182) | ~m1_pre_topc(D_183, A_181) | ~m1_pre_topc(C_184, A_181) | ~l1_pre_topc(B_185) | ~v2_pre_topc(B_185) | v2_struct_0(B_185) | ~l1_pre_topc(A_181) | ~v2_pre_topc(A_181) | v2_struct_0(A_181))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.28/1.48  tff(c_422, plain, (![A_181, D_183]: (k3_tmap_1(A_181, '#skF_3', '#skF_5', D_183, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_183)) | ~m1_pre_topc(D_183, '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_183, A_181) | ~m1_pre_topc('#skF_5', A_181) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_181) | ~v2_pre_topc(A_181) | v2_struct_0(A_181))), inference(resolution, [status(thm)], [c_36, c_420])).
% 3.28/1.48  tff(c_425, plain, (![D_183, A_181]: (k7_relat_1('#skF_6', u1_struct_0(D_183))=k3_tmap_1(A_181, '#skF_3', '#skF_5', D_183, '#skF_6') | ~m1_pre_topc(D_183, '#skF_5') | ~m1_pre_topc(D_183, A_181) | ~m1_pre_topc('#skF_5', A_181) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_181) | ~v2_pre_topc(A_181) | v2_struct_0(A_181))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_40, c_38, c_101, c_422])).
% 3.28/1.48  tff(c_427, plain, (![D_186, A_187]: (k7_relat_1('#skF_6', u1_struct_0(D_186))=k3_tmap_1(A_187, '#skF_3', '#skF_5', D_186, '#skF_6') | ~m1_pre_topc(D_186, '#skF_5') | ~m1_pre_topc(D_186, A_187) | ~m1_pre_topc('#skF_5', A_187) | ~l1_pre_topc(A_187) | ~v2_pre_topc(A_187) | v2_struct_0(A_187))), inference(negUnitSimplification, [status(thm)], [c_54, c_425])).
% 3.28/1.48  tff(c_429, plain, (k7_relat_1('#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6') | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_46, c_427])).
% 3.28/1.48  tff(c_436, plain, (k7_relat_1('#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_42, c_34, c_429])).
% 3.28/1.48  tff(c_437, plain, (k7_relat_1('#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_60, c_436])).
% 3.28/1.48  tff(c_16, plain, (![C_16, B_15, A_14]: (k1_funct_1(k7_relat_1(C_16, B_15), A_14)=k1_funct_1(C_16, A_14) | ~r2_hidden(A_14, B_15) | ~v1_funct_1(C_16) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.28/1.48  tff(c_449, plain, (![A_14]: (k1_funct_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), A_14)=k1_funct_1('#skF_6', A_14) | ~r2_hidden(A_14, u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_437, c_16])).
% 3.28/1.48  tff(c_456, plain, (![A_188]: (k1_funct_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), A_188)=k1_funct_1('#skF_6', A_188) | ~r2_hidden(A_188, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_40, c_449])).
% 3.28/1.48  tff(c_463, plain, (k1_funct_1(k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_7')=k1_funct_1('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_30, c_456])).
% 3.28/1.48  tff(c_470, plain, $false, inference(negUnitSimplification, [status(thm)], [c_414, c_463])).
% 3.28/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.48  
% 3.28/1.48  Inference rules
% 3.28/1.48  ----------------------
% 3.28/1.48  #Ref     : 0
% 3.28/1.48  #Sup     : 84
% 3.28/1.48  #Fact    : 0
% 3.28/1.48  #Define  : 0
% 3.28/1.48  #Split   : 8
% 3.28/1.48  #Chain   : 0
% 3.28/1.48  #Close   : 0
% 3.28/1.48  
% 3.28/1.48  Ordering : KBO
% 3.28/1.48  
% 3.28/1.48  Simplification rules
% 3.28/1.48  ----------------------
% 3.28/1.48  #Subsume      : 3
% 3.28/1.48  #Demod        : 78
% 3.28/1.48  #Tautology    : 38
% 3.28/1.48  #SimpNegUnit  : 13
% 3.28/1.48  #BackRed      : 12
% 3.28/1.48  
% 3.28/1.48  #Partial instantiations: 0
% 3.28/1.48  #Strategies tried      : 1
% 3.28/1.48  
% 3.28/1.48  Timing (in seconds)
% 3.28/1.48  ----------------------
% 3.28/1.48  Preprocessing        : 0.37
% 3.28/1.48  Parsing              : 0.20
% 3.28/1.48  CNF conversion       : 0.04
% 3.28/1.48  Main loop            : 0.31
% 3.28/1.48  Inferencing          : 0.12
% 3.28/1.48  Reduction            : 0.10
% 3.28/1.48  Demodulation         : 0.07
% 3.28/1.48  BG Simplification    : 0.02
% 3.28/1.48  Subsumption          : 0.05
% 3.28/1.48  Abstraction          : 0.02
% 3.28/1.48  MUC search           : 0.00
% 3.28/1.48  Cooper               : 0.00
% 3.28/1.48  Total                : 0.73
% 3.28/1.48  Index Insertion      : 0.00
% 3.28/1.48  Index Deletion       : 0.00
% 3.28/1.48  Index Matching       : 0.00
% 3.28/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
