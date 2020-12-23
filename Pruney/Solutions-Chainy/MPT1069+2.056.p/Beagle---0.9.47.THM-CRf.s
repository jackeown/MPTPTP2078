%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:53 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 339 expanded)
%              Number of leaves         :   45 ( 136 expanded)
%              Depth                    :   14
%              Number of atoms          :  234 (1135 expanded)
%              Number of equality atoms :   52 ( 261 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_166,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ! [E] :
                ( ( v1_funct_1(E)
                  & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                     => ( B = k1_xboole_0
                        | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k7_partfun1(A,E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_141,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ! [E] :
              ( ( v1_funct_1(E)
                & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
             => ! [F] :
                  ( m1_subset_1(F,B)
                 => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                   => ( B = k1_xboole_0
                      | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k1_funct_1(E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_117,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_54,plain,(
    m1_subset_1('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_58,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_56,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_176,plain,(
    ! [A_96,B_97,C_98] :
      ( k1_relset_1(A_96,B_97,C_98) = k1_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_183,plain,(
    k1_relset_1('#skF_4','#skF_2','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_176])).

tff(c_60,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_158,plain,(
    ! [A_93,B_94,C_95] :
      ( k2_relset_1(A_93,B_94,C_95) = k2_relat_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_166,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_158])).

tff(c_52,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),k1_relset_1('#skF_4','#skF_2','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_171,plain,(
    r1_tarski(k2_relat_1('#skF_5'),k1_relset_1('#skF_4','#skF_2','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_52])).

tff(c_193,plain,(
    r1_tarski(k2_relat_1('#skF_5'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_171])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_64,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_62,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_365,plain,(
    ! [C_137,B_133,A_132,E_134,D_135,F_136] :
      ( k1_funct_1(k8_funct_2(B_133,C_137,A_132,D_135,E_134),F_136) = k1_funct_1(E_134,k1_funct_1(D_135,F_136))
      | k1_xboole_0 = B_133
      | ~ r1_tarski(k2_relset_1(B_133,C_137,D_135),k1_relset_1(C_137,A_132,E_134))
      | ~ m1_subset_1(F_136,B_133)
      | ~ m1_subset_1(E_134,k1_zfmisc_1(k2_zfmisc_1(C_137,A_132)))
      | ~ v1_funct_1(E_134)
      | ~ m1_subset_1(D_135,k1_zfmisc_1(k2_zfmisc_1(B_133,C_137)))
      | ~ v1_funct_2(D_135,B_133,C_137)
      | ~ v1_funct_1(D_135)
      | v1_xboole_0(C_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_371,plain,(
    ! [A_132,E_134,F_136] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4',A_132,'#skF_5',E_134),F_136) = k1_funct_1(E_134,k1_funct_1('#skF_5',F_136))
      | k1_xboole_0 = '#skF_3'
      | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relset_1('#skF_4',A_132,E_134))
      | ~ m1_subset_1(F_136,'#skF_3')
      | ~ m1_subset_1(E_134,k1_zfmisc_1(k2_zfmisc_1('#skF_4',A_132)))
      | ~ v1_funct_1(E_134)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_365])).

tff(c_381,plain,(
    ! [A_132,E_134,F_136] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4',A_132,'#skF_5',E_134),F_136) = k1_funct_1(E_134,k1_funct_1('#skF_5',F_136))
      | k1_xboole_0 = '#skF_3'
      | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relset_1('#skF_4',A_132,E_134))
      | ~ m1_subset_1(F_136,'#skF_3')
      | ~ m1_subset_1(E_134,k1_zfmisc_1(k2_zfmisc_1('#skF_4',A_132)))
      | ~ v1_funct_1(E_134)
      | v1_xboole_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_371])).

tff(c_422,plain,(
    ! [A_142,E_143,F_144] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4',A_142,'#skF_5',E_143),F_144) = k1_funct_1(E_143,k1_funct_1('#skF_5',F_144))
      | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relset_1('#skF_4',A_142,E_143))
      | ~ m1_subset_1(F_144,'#skF_3')
      | ~ m1_subset_1(E_143,k1_zfmisc_1(k2_zfmisc_1('#skF_4',A_142)))
      | ~ v1_funct_1(E_143) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_50,c_381])).

tff(c_424,plain,(
    ! [F_144] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),F_144) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',F_144))
      | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(F_144,'#skF_3')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_422])).

tff(c_429,plain,(
    ! [F_144] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),F_144) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',F_144))
      | ~ m1_subset_1(F_144,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_193,c_424])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_101,plain,(
    ! [B_78,A_79] :
      ( v1_relat_1(B_78)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_79))
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_107,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_60,c_101])).

tff(c_113,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_107])).

tff(c_184,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_176])).

tff(c_262,plain,(
    ! [B_119,A_120,C_121] :
      ( k1_xboole_0 = B_119
      | k1_relset_1(A_120,B_119,C_121) = A_120
      | ~ v1_funct_2(C_121,A_120,B_119)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_120,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_268,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_262])).

tff(c_274,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_184,c_268])).

tff(c_275,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_274])).

tff(c_293,plain,(
    ! [A_122,B_123,C_124] :
      ( k7_partfun1(A_122,B_123,C_124) = k1_funct_1(B_123,C_124)
      | ~ r2_hidden(C_124,k1_relat_1(B_123))
      | ~ v1_funct_1(B_123)
      | ~ v5_relat_1(B_123,A_122)
      | ~ v1_relat_1(B_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_295,plain,(
    ! [A_122,C_124] :
      ( k7_partfun1(A_122,'#skF_5',C_124) = k1_funct_1('#skF_5',C_124)
      | ~ r2_hidden(C_124,'#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_122)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_293])).

tff(c_319,plain,(
    ! [A_126,C_127] :
      ( k7_partfun1(A_126,'#skF_5',C_127) = k1_funct_1('#skF_5',C_127)
      | ~ r2_hidden(C_127,'#skF_3')
      | ~ v5_relat_1('#skF_5',A_126) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_64,c_295])).

tff(c_331,plain,(
    ! [A_126] :
      ( k7_partfun1(A_126,'#skF_5','#skF_1'('#skF_3')) = k1_funct_1('#skF_5','#skF_1'('#skF_3'))
      | ~ v5_relat_1('#skF_5',A_126)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_4,c_319])).

tff(c_332,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_331])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_336,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_332,c_6])).

tff(c_340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_336])).

tff(c_342,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_331])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_125,plain,(
    ! [C_84,B_85,A_86] :
      ( v5_relat_1(C_84,B_85)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_86,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_132,plain,(
    v5_relat_1('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_125])).

tff(c_104,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_56,c_101])).

tff(c_110,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_104])).

tff(c_14,plain,(
    ! [B_13,A_12] :
      ( v5_relat_1(B_13,A_12)
      | ~ r1_tarski(k2_relat_1(B_13),A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_196,plain,
    ( v5_relat_1('#skF_5',k1_relat_1('#skF_6'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_193,c_14])).

tff(c_202,plain,(
    v5_relat_1('#skF_5',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_196])).

tff(c_20,plain,(
    ! [B_17,C_19,A_16] :
      ( r2_hidden(k1_funct_1(B_17,C_19),A_16)
      | ~ r2_hidden(C_19,k1_relat_1(B_17))
      | ~ v1_funct_1(B_17)
      | ~ v5_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_626,plain,(
    ! [A_178,B_179,B_180,C_181] :
      ( k7_partfun1(A_178,B_179,k1_funct_1(B_180,C_181)) = k1_funct_1(B_179,k1_funct_1(B_180,C_181))
      | ~ v1_funct_1(B_179)
      | ~ v5_relat_1(B_179,A_178)
      | ~ v1_relat_1(B_179)
      | ~ r2_hidden(C_181,k1_relat_1(B_180))
      | ~ v1_funct_1(B_180)
      | ~ v5_relat_1(B_180,k1_relat_1(B_179))
      | ~ v1_relat_1(B_180) ) ),
    inference(resolution,[status(thm)],[c_20,c_293])).

tff(c_628,plain,(
    ! [A_178,B_179,C_181] :
      ( k7_partfun1(A_178,B_179,k1_funct_1('#skF_5',C_181)) = k1_funct_1(B_179,k1_funct_1('#skF_5',C_181))
      | ~ v1_funct_1(B_179)
      | ~ v5_relat_1(B_179,A_178)
      | ~ v1_relat_1(B_179)
      | ~ r2_hidden(C_181,'#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',k1_relat_1(B_179))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_626])).

tff(c_643,plain,(
    ! [A_182,B_183,C_184] :
      ( k7_partfun1(A_182,B_183,k1_funct_1('#skF_5',C_184)) = k1_funct_1(B_183,k1_funct_1('#skF_5',C_184))
      | ~ v1_funct_1(B_183)
      | ~ v5_relat_1(B_183,A_182)
      | ~ v1_relat_1(B_183)
      | ~ r2_hidden(C_184,'#skF_3')
      | ~ v5_relat_1('#skF_5',k1_relat_1(B_183)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_64,c_628])).

tff(c_647,plain,(
    ! [A_182,C_184] :
      ( k7_partfun1(A_182,'#skF_6',k1_funct_1('#skF_5',C_184)) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',C_184))
      | ~ v1_funct_1('#skF_6')
      | ~ v5_relat_1('#skF_6',A_182)
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(C_184,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_202,c_643])).

tff(c_653,plain,(
    ! [A_185,C_186] :
      ( k7_partfun1(A_185,'#skF_6',k1_funct_1('#skF_5',C_186)) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',C_186))
      | ~ v5_relat_1('#skF_6',A_185)
      | ~ r2_hidden(C_186,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_58,c_647])).

tff(c_48,plain,(
    k7_partfun1('#skF_2','#skF_6',k1_funct_1('#skF_5','#skF_7')) != k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_659,plain,
    ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7'))
    | ~ v5_relat_1('#skF_6','#skF_2')
    | ~ r2_hidden('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_653,c_48])).

tff(c_665,plain,
    ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7'))
    | ~ r2_hidden('#skF_7','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_659])).

tff(c_667,plain,(
    ~ r2_hidden('#skF_7','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_665])).

tff(c_670,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_667])).

tff(c_673,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_670])).

tff(c_675,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_342,c_673])).

tff(c_676,plain,(
    k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_665])).

tff(c_717,plain,(
    ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_429,c_676])).

tff(c_721,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_717])).

tff(c_722,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_274])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_76,plain,(
    ! [B_73,A_74] :
      ( ~ r1_tarski(B_73,A_74)
      | ~ r2_hidden(A_74,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_81,plain,(
    ! [A_75] :
      ( ~ r1_tarski(A_75,'#skF_1'(A_75))
      | v1_xboole_0(A_75) ) ),
    inference(resolution,[status(thm)],[c_4,c_76])).

tff(c_86,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_81])).

tff(c_743,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_722,c_86])).

tff(c_748,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_743])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:59:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.52/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.59  
% 3.52/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.59  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 3.52/1.59  
% 3.52/1.59  %Foreground sorts:
% 3.52/1.59  
% 3.52/1.59  
% 3.52/1.59  %Background operators:
% 3.52/1.59  
% 3.52/1.59  
% 3.52/1.59  %Foreground operators:
% 3.52/1.59  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.52/1.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.52/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.52/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.52/1.59  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.52/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.52/1.59  tff('#skF_7', type, '#skF_7': $i).
% 3.52/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.52/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.52/1.59  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 3.52/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.52/1.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.52/1.59  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 3.52/1.59  tff('#skF_6', type, '#skF_6': $i).
% 3.52/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.52/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.52/1.59  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.52/1.59  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.52/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.52/1.59  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.52/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.52/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.52/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.52/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.52/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.52/1.59  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.52/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.52/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.52/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.52/1.59  
% 3.52/1.62  tff(f_166, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t186_funct_2)).
% 3.52/1.62  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.52/1.62  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.52/1.62  tff(f_141, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 3.52/1.62  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.52/1.62  tff(f_58, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.52/1.62  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.52/1.62  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.52/1.62  tff(f_117, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 3.52/1.62  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.52/1.62  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.52/1.62  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.52/1.62  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.52/1.62  tff(f_69, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 3.52/1.62  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.52/1.62  tff(f_74, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.52/1.62  tff(c_66, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.52/1.62  tff(c_54, plain, (m1_subset_1('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.52/1.62  tff(c_58, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.52/1.62  tff(c_56, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.52/1.62  tff(c_176, plain, (![A_96, B_97, C_98]: (k1_relset_1(A_96, B_97, C_98)=k1_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.52/1.62  tff(c_183, plain, (k1_relset_1('#skF_4', '#skF_2', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_176])).
% 3.52/1.62  tff(c_60, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.52/1.62  tff(c_158, plain, (![A_93, B_94, C_95]: (k2_relset_1(A_93, B_94, C_95)=k2_relat_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.52/1.62  tff(c_166, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_158])).
% 3.52/1.62  tff(c_52, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), k1_relset_1('#skF_4', '#skF_2', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.52/1.62  tff(c_171, plain, (r1_tarski(k2_relat_1('#skF_5'), k1_relset_1('#skF_4', '#skF_2', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_166, c_52])).
% 3.52/1.62  tff(c_193, plain, (r1_tarski(k2_relat_1('#skF_5'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_183, c_171])).
% 3.52/1.62  tff(c_50, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.52/1.62  tff(c_64, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.52/1.62  tff(c_62, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.52/1.62  tff(c_365, plain, (![C_137, B_133, A_132, E_134, D_135, F_136]: (k1_funct_1(k8_funct_2(B_133, C_137, A_132, D_135, E_134), F_136)=k1_funct_1(E_134, k1_funct_1(D_135, F_136)) | k1_xboole_0=B_133 | ~r1_tarski(k2_relset_1(B_133, C_137, D_135), k1_relset_1(C_137, A_132, E_134)) | ~m1_subset_1(F_136, B_133) | ~m1_subset_1(E_134, k1_zfmisc_1(k2_zfmisc_1(C_137, A_132))) | ~v1_funct_1(E_134) | ~m1_subset_1(D_135, k1_zfmisc_1(k2_zfmisc_1(B_133, C_137))) | ~v1_funct_2(D_135, B_133, C_137) | ~v1_funct_1(D_135) | v1_xboole_0(C_137))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.52/1.62  tff(c_371, plain, (![A_132, E_134, F_136]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', A_132, '#skF_5', E_134), F_136)=k1_funct_1(E_134, k1_funct_1('#skF_5', F_136)) | k1_xboole_0='#skF_3' | ~r1_tarski(k2_relat_1('#skF_5'), k1_relset_1('#skF_4', A_132, E_134)) | ~m1_subset_1(F_136, '#skF_3') | ~m1_subset_1(E_134, k1_zfmisc_1(k2_zfmisc_1('#skF_4', A_132))) | ~v1_funct_1(E_134) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_166, c_365])).
% 3.52/1.62  tff(c_381, plain, (![A_132, E_134, F_136]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', A_132, '#skF_5', E_134), F_136)=k1_funct_1(E_134, k1_funct_1('#skF_5', F_136)) | k1_xboole_0='#skF_3' | ~r1_tarski(k2_relat_1('#skF_5'), k1_relset_1('#skF_4', A_132, E_134)) | ~m1_subset_1(F_136, '#skF_3') | ~m1_subset_1(E_134, k1_zfmisc_1(k2_zfmisc_1('#skF_4', A_132))) | ~v1_funct_1(E_134) | v1_xboole_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_371])).
% 3.52/1.62  tff(c_422, plain, (![A_142, E_143, F_144]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', A_142, '#skF_5', E_143), F_144)=k1_funct_1(E_143, k1_funct_1('#skF_5', F_144)) | ~r1_tarski(k2_relat_1('#skF_5'), k1_relset_1('#skF_4', A_142, E_143)) | ~m1_subset_1(F_144, '#skF_3') | ~m1_subset_1(E_143, k1_zfmisc_1(k2_zfmisc_1('#skF_4', A_142))) | ~v1_funct_1(E_143))), inference(negUnitSimplification, [status(thm)], [c_66, c_50, c_381])).
% 3.52/1.62  tff(c_424, plain, (![F_144]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), F_144)=k1_funct_1('#skF_6', k1_funct_1('#skF_5', F_144)) | ~r1_tarski(k2_relat_1('#skF_5'), k1_relat_1('#skF_6')) | ~m1_subset_1(F_144, '#skF_3') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_183, c_422])).
% 3.52/1.62  tff(c_429, plain, (![F_144]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), F_144)=k1_funct_1('#skF_6', k1_funct_1('#skF_5', F_144)) | ~m1_subset_1(F_144, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_193, c_424])).
% 3.52/1.62  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.52/1.62  tff(c_18, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.52/1.62  tff(c_101, plain, (![B_78, A_79]: (v1_relat_1(B_78) | ~m1_subset_1(B_78, k1_zfmisc_1(A_79)) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.52/1.62  tff(c_107, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_60, c_101])).
% 3.52/1.62  tff(c_113, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_107])).
% 3.52/1.62  tff(c_184, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_176])).
% 3.52/1.62  tff(c_262, plain, (![B_119, A_120, C_121]: (k1_xboole_0=B_119 | k1_relset_1(A_120, B_119, C_121)=A_120 | ~v1_funct_2(C_121, A_120, B_119) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_120, B_119))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.52/1.62  tff(c_268, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_60, c_262])).
% 3.52/1.62  tff(c_274, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_184, c_268])).
% 3.52/1.62  tff(c_275, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_274])).
% 3.52/1.62  tff(c_293, plain, (![A_122, B_123, C_124]: (k7_partfun1(A_122, B_123, C_124)=k1_funct_1(B_123, C_124) | ~r2_hidden(C_124, k1_relat_1(B_123)) | ~v1_funct_1(B_123) | ~v5_relat_1(B_123, A_122) | ~v1_relat_1(B_123))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.52/1.62  tff(c_295, plain, (![A_122, C_124]: (k7_partfun1(A_122, '#skF_5', C_124)=k1_funct_1('#skF_5', C_124) | ~r2_hidden(C_124, '#skF_3') | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_122) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_275, c_293])).
% 3.52/1.62  tff(c_319, plain, (![A_126, C_127]: (k7_partfun1(A_126, '#skF_5', C_127)=k1_funct_1('#skF_5', C_127) | ~r2_hidden(C_127, '#skF_3') | ~v5_relat_1('#skF_5', A_126))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_64, c_295])).
% 3.52/1.62  tff(c_331, plain, (![A_126]: (k7_partfun1(A_126, '#skF_5', '#skF_1'('#skF_3'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3')) | ~v5_relat_1('#skF_5', A_126) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_4, c_319])).
% 3.52/1.62  tff(c_332, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_331])).
% 3.52/1.62  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.52/1.62  tff(c_336, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_332, c_6])).
% 3.52/1.62  tff(c_340, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_336])).
% 3.52/1.62  tff(c_342, plain, (~v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_331])).
% 3.52/1.62  tff(c_10, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.52/1.62  tff(c_125, plain, (![C_84, B_85, A_86]: (v5_relat_1(C_84, B_85) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_86, B_85))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.52/1.62  tff(c_132, plain, (v5_relat_1('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_56, c_125])).
% 3.52/1.62  tff(c_104, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_56, c_101])).
% 3.52/1.62  tff(c_110, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_104])).
% 3.52/1.62  tff(c_14, plain, (![B_13, A_12]: (v5_relat_1(B_13, A_12) | ~r1_tarski(k2_relat_1(B_13), A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.52/1.62  tff(c_196, plain, (v5_relat_1('#skF_5', k1_relat_1('#skF_6')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_193, c_14])).
% 3.52/1.62  tff(c_202, plain, (v5_relat_1('#skF_5', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_196])).
% 3.52/1.62  tff(c_20, plain, (![B_17, C_19, A_16]: (r2_hidden(k1_funct_1(B_17, C_19), A_16) | ~r2_hidden(C_19, k1_relat_1(B_17)) | ~v1_funct_1(B_17) | ~v5_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.52/1.62  tff(c_626, plain, (![A_178, B_179, B_180, C_181]: (k7_partfun1(A_178, B_179, k1_funct_1(B_180, C_181))=k1_funct_1(B_179, k1_funct_1(B_180, C_181)) | ~v1_funct_1(B_179) | ~v5_relat_1(B_179, A_178) | ~v1_relat_1(B_179) | ~r2_hidden(C_181, k1_relat_1(B_180)) | ~v1_funct_1(B_180) | ~v5_relat_1(B_180, k1_relat_1(B_179)) | ~v1_relat_1(B_180))), inference(resolution, [status(thm)], [c_20, c_293])).
% 3.52/1.62  tff(c_628, plain, (![A_178, B_179, C_181]: (k7_partfun1(A_178, B_179, k1_funct_1('#skF_5', C_181))=k1_funct_1(B_179, k1_funct_1('#skF_5', C_181)) | ~v1_funct_1(B_179) | ~v5_relat_1(B_179, A_178) | ~v1_relat_1(B_179) | ~r2_hidden(C_181, '#skF_3') | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', k1_relat_1(B_179)) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_275, c_626])).
% 3.52/1.62  tff(c_643, plain, (![A_182, B_183, C_184]: (k7_partfun1(A_182, B_183, k1_funct_1('#skF_5', C_184))=k1_funct_1(B_183, k1_funct_1('#skF_5', C_184)) | ~v1_funct_1(B_183) | ~v5_relat_1(B_183, A_182) | ~v1_relat_1(B_183) | ~r2_hidden(C_184, '#skF_3') | ~v5_relat_1('#skF_5', k1_relat_1(B_183)))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_64, c_628])).
% 3.52/1.62  tff(c_647, plain, (![A_182, C_184]: (k7_partfun1(A_182, '#skF_6', k1_funct_1('#skF_5', C_184))=k1_funct_1('#skF_6', k1_funct_1('#skF_5', C_184)) | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', A_182) | ~v1_relat_1('#skF_6') | ~r2_hidden(C_184, '#skF_3'))), inference(resolution, [status(thm)], [c_202, c_643])).
% 3.52/1.62  tff(c_653, plain, (![A_185, C_186]: (k7_partfun1(A_185, '#skF_6', k1_funct_1('#skF_5', C_186))=k1_funct_1('#skF_6', k1_funct_1('#skF_5', C_186)) | ~v5_relat_1('#skF_6', A_185) | ~r2_hidden(C_186, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_58, c_647])).
% 3.52/1.62  tff(c_48, plain, (k7_partfun1('#skF_2', '#skF_6', k1_funct_1('#skF_5', '#skF_7'))!=k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.52/1.62  tff(c_659, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7')) | ~v5_relat_1('#skF_6', '#skF_2') | ~r2_hidden('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_653, c_48])).
% 3.52/1.62  tff(c_665, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7')) | ~r2_hidden('#skF_7', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_659])).
% 3.52/1.62  tff(c_667, plain, (~r2_hidden('#skF_7', '#skF_3')), inference(splitLeft, [status(thm)], [c_665])).
% 3.52/1.62  tff(c_670, plain, (v1_xboole_0('#skF_3') | ~m1_subset_1('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_10, c_667])).
% 3.52/1.62  tff(c_673, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_670])).
% 3.52/1.62  tff(c_675, plain, $false, inference(negUnitSimplification, [status(thm)], [c_342, c_673])).
% 3.52/1.62  tff(c_676, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7'))), inference(splitRight, [status(thm)], [c_665])).
% 3.52/1.62  tff(c_717, plain, (~m1_subset_1('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_429, c_676])).
% 3.52/1.62  tff(c_721, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_717])).
% 3.52/1.62  tff(c_722, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_274])).
% 3.52/1.62  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.52/1.62  tff(c_76, plain, (![B_73, A_74]: (~r1_tarski(B_73, A_74) | ~r2_hidden(A_74, B_73))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.52/1.62  tff(c_81, plain, (![A_75]: (~r1_tarski(A_75, '#skF_1'(A_75)) | v1_xboole_0(A_75))), inference(resolution, [status(thm)], [c_4, c_76])).
% 3.52/1.62  tff(c_86, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_81])).
% 3.52/1.62  tff(c_743, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_722, c_86])).
% 3.52/1.62  tff(c_748, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_743])).
% 3.52/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.62  
% 3.52/1.62  Inference rules
% 3.52/1.62  ----------------------
% 3.52/1.62  #Ref     : 0
% 3.52/1.62  #Sup     : 136
% 3.52/1.62  #Fact    : 0
% 3.52/1.62  #Define  : 0
% 3.52/1.62  #Split   : 13
% 3.52/1.62  #Chain   : 0
% 3.52/1.62  #Close   : 0
% 3.52/1.62  
% 3.52/1.62  Ordering : KBO
% 3.52/1.62  
% 3.52/1.62  Simplification rules
% 3.52/1.62  ----------------------
% 3.52/1.62  #Subsume      : 23
% 3.52/1.62  #Demod        : 141
% 3.52/1.62  #Tautology    : 39
% 3.52/1.62  #SimpNegUnit  : 18
% 3.52/1.62  #BackRed      : 12
% 3.52/1.62  
% 3.52/1.62  #Partial instantiations: 0
% 3.52/1.62  #Strategies tried      : 1
% 3.52/1.62  
% 3.52/1.62  Timing (in seconds)
% 3.52/1.62  ----------------------
% 3.52/1.62  Preprocessing        : 0.37
% 3.52/1.62  Parsing              : 0.20
% 3.52/1.62  CNF conversion       : 0.03
% 3.52/1.62  Main loop            : 0.42
% 3.52/1.62  Inferencing          : 0.15
% 3.52/1.62  Reduction            : 0.13
% 3.52/1.62  Demodulation         : 0.09
% 3.52/1.62  BG Simplification    : 0.02
% 3.52/1.62  Subsumption          : 0.08
% 3.52/1.62  Abstraction          : 0.02
% 3.52/1.62  MUC search           : 0.00
% 3.52/1.62  Cooper               : 0.00
% 3.52/1.62  Total                : 0.85
% 3.52/1.62  Index Insertion      : 0.00
% 3.52/1.62  Index Deletion       : 0.00
% 3.52/1.62  Index Matching       : 0.00
% 3.52/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
