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
% DateTime   : Thu Dec  3 10:17:47 EST 2020

% Result     : Theorem 11.06s
% Output     : CNFRefutation 11.16s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 558 expanded)
%              Number of leaves         :   46 ( 213 expanded)
%              Depth                    :   12
%              Number of atoms          :  300 (1916 expanded)
%              Number of equality atoms :   60 ( 375 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2

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

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_194,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_169,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_70,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_134,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_145,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_88,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_76,plain,(
    m1_subset_1('#skF_8','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_86,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_84,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_82,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_78,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_7370,plain,(
    ! [A_787,B_788,C_789] :
      ( k1_relset_1(A_787,B_788,C_789) = k1_relat_1(C_789)
      | ~ m1_subset_1(C_789,k1_zfmisc_1(k2_zfmisc_1(A_787,B_788))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_7388,plain,(
    k1_relset_1('#skF_5','#skF_3','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_78,c_7370])).

tff(c_7273,plain,(
    ! [A_778,B_779,C_780] :
      ( k2_relset_1(A_778,B_779,C_780) = k2_relat_1(C_780)
      | ~ m1_subset_1(C_780,k1_zfmisc_1(k2_zfmisc_1(A_778,B_779))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_7292,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_7273])).

tff(c_74,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_7299,plain,(
    r1_tarski(k2_relat_1('#skF_6'),k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7292,c_74])).

tff(c_7391,plain,(
    r1_tarski(k2_relat_1('#skF_6'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7388,c_7299])).

tff(c_80,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_10749,plain,(
    ! [A_1139,B_1134,F_1135,C_1138,E_1137,D_1136] :
      ( k1_funct_1(k8_funct_2(B_1134,C_1138,A_1139,D_1136,E_1137),F_1135) = k1_funct_1(E_1137,k1_funct_1(D_1136,F_1135))
      | k1_xboole_0 = B_1134
      | ~ r1_tarski(k2_relset_1(B_1134,C_1138,D_1136),k1_relset_1(C_1138,A_1139,E_1137))
      | ~ m1_subset_1(F_1135,B_1134)
      | ~ m1_subset_1(E_1137,k1_zfmisc_1(k2_zfmisc_1(C_1138,A_1139)))
      | ~ v1_funct_1(E_1137)
      | ~ m1_subset_1(D_1136,k1_zfmisc_1(k2_zfmisc_1(B_1134,C_1138)))
      | ~ v1_funct_2(D_1136,B_1134,C_1138)
      | ~ v1_funct_1(D_1136)
      | v1_xboole_0(C_1138) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_10761,plain,(
    ! [B_1134,D_1136,F_1135] :
      ( k1_funct_1(k8_funct_2(B_1134,'#skF_5','#skF_3',D_1136,'#skF_7'),F_1135) = k1_funct_1('#skF_7',k1_funct_1(D_1136,F_1135))
      | k1_xboole_0 = B_1134
      | ~ r1_tarski(k2_relset_1(B_1134,'#skF_5',D_1136),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_1135,B_1134)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(D_1136,k1_zfmisc_1(k2_zfmisc_1(B_1134,'#skF_5')))
      | ~ v1_funct_2(D_1136,B_1134,'#skF_5')
      | ~ v1_funct_1(D_1136)
      | v1_xboole_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7388,c_10749])).

tff(c_10776,plain,(
    ! [B_1134,D_1136,F_1135] :
      ( k1_funct_1(k8_funct_2(B_1134,'#skF_5','#skF_3',D_1136,'#skF_7'),F_1135) = k1_funct_1('#skF_7',k1_funct_1(D_1136,F_1135))
      | k1_xboole_0 = B_1134
      | ~ r1_tarski(k2_relset_1(B_1134,'#skF_5',D_1136),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_1135,B_1134)
      | ~ m1_subset_1(D_1136,k1_zfmisc_1(k2_zfmisc_1(B_1134,'#skF_5')))
      | ~ v1_funct_2(D_1136,B_1134,'#skF_5')
      | ~ v1_funct_1(D_1136)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_10761])).

tff(c_11052,plain,(
    ! [B_1164,D_1165,F_1166] :
      ( k1_funct_1(k8_funct_2(B_1164,'#skF_5','#skF_3',D_1165,'#skF_7'),F_1166) = k1_funct_1('#skF_7',k1_funct_1(D_1165,F_1166))
      | k1_xboole_0 = B_1164
      | ~ r1_tarski(k2_relset_1(B_1164,'#skF_5',D_1165),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_1166,B_1164)
      | ~ m1_subset_1(D_1165,k1_zfmisc_1(k2_zfmisc_1(B_1164,'#skF_5')))
      | ~ v1_funct_2(D_1165,B_1164,'#skF_5')
      | ~ v1_funct_1(D_1165) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_10776])).

tff(c_11060,plain,(
    ! [F_1166] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_1166) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_1166))
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_1166,'#skF_4')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7292,c_11052])).

tff(c_11067,plain,(
    ! [F_1166] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_1166) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_1166))
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1(F_1166,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_7391,c_11060])).

tff(c_11068,plain,(
    ! [F_1166] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_1166) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_1166))
      | ~ m1_subset_1(F_1166,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_11067])).

tff(c_213,plain,(
    ! [A_95,B_96] :
      ( r2_hidden('#skF_2'(A_95,B_96),A_95)
      | r1_tarski(A_95,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_217,plain,(
    ! [A_95,B_96] :
      ( ~ v1_xboole_0(A_95)
      | r1_tarski(A_95,B_96) ) ),
    inference(resolution,[status(thm)],[c_213,c_2])).

tff(c_135,plain,(
    ! [A_85,B_86] :
      ( r1_tarski(A_85,B_86)
      | ~ m1_subset_1(A_85,k1_zfmisc_1(B_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_146,plain,(
    r1_tarski('#skF_7',k2_zfmisc_1('#skF_5','#skF_3')) ),
    inference(resolution,[status(thm)],[c_78,c_135])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_384,plain,(
    ! [C_131,B_132,A_133] :
      ( r2_hidden(C_131,B_132)
      | ~ r2_hidden(C_131,A_133)
      | ~ r1_tarski(A_133,B_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_510,plain,(
    ! [A_149,B_150,B_151] :
      ( r2_hidden('#skF_2'(A_149,B_150),B_151)
      | ~ r1_tarski(A_149,B_151)
      | r1_tarski(A_149,B_150) ) ),
    inference(resolution,[status(thm)],[c_10,c_384])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10852,plain,(
    ! [A_1148,B_1149,B_1150,B_1151] :
      ( r2_hidden('#skF_2'(A_1148,B_1149),B_1150)
      | ~ r1_tarski(B_1151,B_1150)
      | ~ r1_tarski(A_1148,B_1151)
      | r1_tarski(A_1148,B_1149) ) ),
    inference(resolution,[status(thm)],[c_510,c_6])).

tff(c_10912,plain,(
    ! [A_1155,B_1156] :
      ( r2_hidden('#skF_2'(A_1155,B_1156),k2_zfmisc_1('#skF_5','#skF_3'))
      | ~ r1_tarski(A_1155,'#skF_7')
      | r1_tarski(A_1155,B_1156) ) ),
    inference(resolution,[status(thm)],[c_146,c_10852])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10925,plain,(
    ! [A_1157] :
      ( ~ r1_tarski(A_1157,'#skF_7')
      | r1_tarski(A_1157,k2_zfmisc_1('#skF_5','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_10912,c_8])).

tff(c_26,plain,(
    ! [A_14,B_15] :
      ( r2_hidden(A_14,B_15)
      | v1_xboole_0(B_15)
      | ~ m1_subset_1(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_391,plain,(
    ! [A_14,B_132,B_15] :
      ( r2_hidden(A_14,B_132)
      | ~ r1_tarski(B_15,B_132)
      | v1_xboole_0(B_15)
      | ~ m1_subset_1(A_14,B_15) ) ),
    inference(resolution,[status(thm)],[c_26,c_384])).

tff(c_11595,plain,(
    ! [A_1204,A_1205] :
      ( r2_hidden(A_1204,k2_zfmisc_1('#skF_5','#skF_3'))
      | v1_xboole_0(A_1205)
      | ~ m1_subset_1(A_1204,A_1205)
      | ~ r1_tarski(A_1205,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_10925,c_391])).

tff(c_11610,plain,
    ( r2_hidden('#skF_8',k2_zfmisc_1('#skF_5','#skF_3'))
    | v1_xboole_0('#skF_4')
    | ~ r1_tarski('#skF_4','#skF_7') ),
    inference(resolution,[status(thm)],[c_76,c_11595])).

tff(c_11611,plain,(
    ~ r1_tarski('#skF_4','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_11610])).

tff(c_11615,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_217,c_11611])).

tff(c_293,plain,(
    ! [C_109,B_110,A_111] :
      ( v5_relat_1(C_109,B_110)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_111,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_311,plain,(
    v5_relat_1('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_293])).

tff(c_34,plain,(
    ! [A_21,B_22] : v1_relat_1(k2_zfmisc_1(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_175,plain,(
    ! [B_91,A_92] :
      ( v1_relat_1(B_91)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_92))
      | ~ v1_relat_1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_184,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_82,c_175])).

tff(c_191,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_184])).

tff(c_7389,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_7370])).

tff(c_10229,plain,(
    ! [B_1069,A_1070,C_1071] :
      ( k1_xboole_0 = B_1069
      | k1_relset_1(A_1070,B_1069,C_1071) = A_1070
      | ~ v1_funct_2(C_1071,A_1070,B_1069)
      | ~ m1_subset_1(C_1071,k1_zfmisc_1(k2_zfmisc_1(A_1070,B_1069))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_10242,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_10229])).

tff(c_10252,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_7389,c_10242])).

tff(c_10254,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_10252])).

tff(c_181,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_3')) ),
    inference(resolution,[status(thm)],[c_78,c_175])).

tff(c_188,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_181])).

tff(c_10076,plain,(
    ! [B_1046,A_1047] :
      ( r2_hidden(k1_funct_1(B_1046,A_1047),k2_relat_1(B_1046))
      | ~ r2_hidden(A_1047,k1_relat_1(B_1046))
      | ~ v1_funct_1(B_1046)
      | ~ v1_relat_1(B_1046) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_11555,plain,(
    ! [B_1200,A_1201,B_1202] :
      ( r2_hidden(k1_funct_1(B_1200,A_1201),B_1202)
      | ~ r1_tarski(k2_relat_1(B_1200),B_1202)
      | ~ r2_hidden(A_1201,k1_relat_1(B_1200))
      | ~ v1_funct_1(B_1200)
      | ~ v1_relat_1(B_1200) ) ),
    inference(resolution,[status(thm)],[c_10076,c_6])).

tff(c_66,plain,(
    ! [A_42,B_43,C_45] :
      ( k7_partfun1(A_42,B_43,C_45) = k1_funct_1(B_43,C_45)
      | ~ r2_hidden(C_45,k1_relat_1(B_43))
      | ~ v1_funct_1(B_43)
      | ~ v5_relat_1(B_43,A_42)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_12914,plain,(
    ! [A_1300,B_1301,B_1302,A_1303] :
      ( k7_partfun1(A_1300,B_1301,k1_funct_1(B_1302,A_1303)) = k1_funct_1(B_1301,k1_funct_1(B_1302,A_1303))
      | ~ v1_funct_1(B_1301)
      | ~ v5_relat_1(B_1301,A_1300)
      | ~ v1_relat_1(B_1301)
      | ~ r1_tarski(k2_relat_1(B_1302),k1_relat_1(B_1301))
      | ~ r2_hidden(A_1303,k1_relat_1(B_1302))
      | ~ v1_funct_1(B_1302)
      | ~ v1_relat_1(B_1302) ) ),
    inference(resolution,[status(thm)],[c_11555,c_66])).

tff(c_12920,plain,(
    ! [A_1300,A_1303] :
      ( k7_partfun1(A_1300,'#skF_7',k1_funct_1('#skF_6',A_1303)) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',A_1303))
      | ~ v1_funct_1('#skF_7')
      | ~ v5_relat_1('#skF_7',A_1300)
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(A_1303,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_7391,c_12914])).

tff(c_14224,plain,(
    ! [A_1412,A_1413] :
      ( k7_partfun1(A_1412,'#skF_7',k1_funct_1('#skF_6',A_1413)) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',A_1413))
      | ~ v5_relat_1('#skF_7',A_1412)
      | ~ r2_hidden(A_1413,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_86,c_10254,c_188,c_80,c_12920])).

tff(c_70,plain,(
    k7_partfun1('#skF_3','#skF_7',k1_funct_1('#skF_6','#skF_8')) != k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_14230,plain,
    ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
    | ~ v5_relat_1('#skF_7','#skF_3')
    | ~ r2_hidden('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_14224,c_70])).

tff(c_14236,plain,
    ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
    | ~ r2_hidden('#skF_8','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_14230])).

tff(c_14277,plain,(
    ~ r2_hidden('#skF_8','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_14236])).

tff(c_14280,plain,
    ( v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_14277])).

tff(c_14283,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_14280])).

tff(c_14285,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11615,c_14283])).

tff(c_14286,plain,(
    k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_14236])).

tff(c_14516,plain,(
    ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_11068,c_14286])).

tff(c_14520,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_14516])).

tff(c_14522,plain,(
    r1_tarski('#skF_4','#skF_7') ),
    inference(splitRight,[status(thm)],[c_11610])).

tff(c_14556,plain,(
    ! [A_14] :
      ( r2_hidden(A_14,'#skF_7')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_14,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_14522,c_391])).

tff(c_14635,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_14556])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_218,plain,(
    ! [A_97,B_98] :
      ( ~ v1_xboole_0(A_97)
      | r1_tarski(A_97,B_98) ) ),
    inference(resolution,[status(thm)],[c_213,c_2])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_246,plain,(
    ! [B_102,A_103] :
      ( B_102 = A_103
      | ~ r1_tarski(B_102,A_103)
      | ~ v1_xboole_0(A_103) ) ),
    inference(resolution,[status(thm)],[c_218,c_14])).

tff(c_268,plain,(
    ! [B_104,A_105] :
      ( B_104 = A_105
      | ~ v1_xboole_0(B_104)
      | ~ v1_xboole_0(A_105) ) ),
    inference(resolution,[status(thm)],[c_217,c_246])).

tff(c_271,plain,(
    ! [A_105] :
      ( k1_xboole_0 = A_105
      | ~ v1_xboole_0(A_105) ) ),
    inference(resolution,[status(thm)],[c_12,c_268])).

tff(c_14644,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_14635,c_271])).

tff(c_14659,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_14644])).

tff(c_14661,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_14556])).

tff(c_16026,plain,(
    ! [A_1515,B_1516,B_1517,A_1518] :
      ( k7_partfun1(A_1515,B_1516,k1_funct_1(B_1517,A_1518)) = k1_funct_1(B_1516,k1_funct_1(B_1517,A_1518))
      | ~ v1_funct_1(B_1516)
      | ~ v5_relat_1(B_1516,A_1515)
      | ~ v1_relat_1(B_1516)
      | ~ r1_tarski(k2_relat_1(B_1517),k1_relat_1(B_1516))
      | ~ r2_hidden(A_1518,k1_relat_1(B_1517))
      | ~ v1_funct_1(B_1517)
      | ~ v1_relat_1(B_1517) ) ),
    inference(resolution,[status(thm)],[c_11555,c_66])).

tff(c_16032,plain,(
    ! [A_1515,A_1518] :
      ( k7_partfun1(A_1515,'#skF_7',k1_funct_1('#skF_6',A_1518)) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',A_1518))
      | ~ v1_funct_1('#skF_7')
      | ~ v5_relat_1('#skF_7',A_1515)
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(A_1518,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_7391,c_16026])).

tff(c_19268,plain,(
    ! [A_1709,A_1710] :
      ( k7_partfun1(A_1709,'#skF_7',k1_funct_1('#skF_6',A_1710)) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',A_1710))
      | ~ v5_relat_1('#skF_7',A_1709)
      | ~ r2_hidden(A_1710,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_86,c_10254,c_188,c_80,c_16032])).

tff(c_19274,plain,
    ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
    | ~ v5_relat_1('#skF_7','#skF_3')
    | ~ r2_hidden('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_19268,c_70])).

tff(c_19280,plain,
    ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
    | ~ r2_hidden('#skF_8','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_19274])).

tff(c_19288,plain,(
    ~ r2_hidden('#skF_8','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_19280])).

tff(c_19297,plain,
    ( v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_19288])).

tff(c_19304,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_19297])).

tff(c_19306,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14661,c_19304])).

tff(c_19307,plain,(
    k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_19280])).

tff(c_19429,plain,(
    ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_11068,c_19307])).

tff(c_19433,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_19429])).

tff(c_19434,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_10252])).

tff(c_19471,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19434,c_12])).

tff(c_19474,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_19471])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n023.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:39:36 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.06/4.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.06/4.65  
% 11.06/4.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.16/4.65  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2
% 11.16/4.65  
% 11.16/4.65  %Foreground sorts:
% 11.16/4.65  
% 11.16/4.65  
% 11.16/4.65  %Background operators:
% 11.16/4.65  
% 11.16/4.65  
% 11.16/4.65  %Foreground operators:
% 11.16/4.65  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 11.16/4.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.16/4.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.16/4.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.16/4.65  tff('#skF_1', type, '#skF_1': $i > $i).
% 11.16/4.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.16/4.65  tff('#skF_7', type, '#skF_7': $i).
% 11.16/4.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.16/4.65  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.16/4.65  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 11.16/4.65  tff('#skF_5', type, '#skF_5': $i).
% 11.16/4.65  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.16/4.65  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 11.16/4.65  tff('#skF_6', type, '#skF_6': $i).
% 11.16/4.65  tff('#skF_3', type, '#skF_3': $i).
% 11.16/4.65  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.16/4.65  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 11.16/4.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.16/4.65  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 11.16/4.65  tff('#skF_8', type, '#skF_8': $i).
% 11.16/4.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.16/4.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.16/4.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.16/4.65  tff('#skF_4', type, '#skF_4': $i).
% 11.16/4.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.16/4.65  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.16/4.65  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 11.16/4.65  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.16/4.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.16/4.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.16/4.65  
% 11.16/4.68  tff(f_194, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 11.16/4.68  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.16/4.68  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 11.16/4.68  tff(f_169, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 11.16/4.68  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 11.16/4.68  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 11.16/4.68  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 11.16/4.68  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 11.16/4.68  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 11.16/4.68  tff(f_70, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 11.16/4.68  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 11.16/4.68  tff(f_134, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 11.16/4.68  tff(f_82, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 11.16/4.68  tff(f_145, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 11.16/4.68  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 11.16/4.68  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.16/4.68  tff(c_88, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_194])).
% 11.16/4.68  tff(c_76, plain, (m1_subset_1('#skF_8', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_194])).
% 11.16/4.68  tff(c_72, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_194])).
% 11.16/4.68  tff(c_86, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_194])).
% 11.16/4.68  tff(c_84, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_194])).
% 11.16/4.68  tff(c_82, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_194])).
% 11.16/4.68  tff(c_78, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_194])).
% 11.16/4.68  tff(c_7370, plain, (![A_787, B_788, C_789]: (k1_relset_1(A_787, B_788, C_789)=k1_relat_1(C_789) | ~m1_subset_1(C_789, k1_zfmisc_1(k2_zfmisc_1(A_787, B_788))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.16/4.68  tff(c_7388, plain, (k1_relset_1('#skF_5', '#skF_3', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_78, c_7370])).
% 11.16/4.68  tff(c_7273, plain, (![A_778, B_779, C_780]: (k2_relset_1(A_778, B_779, C_780)=k2_relat_1(C_780) | ~m1_subset_1(C_780, k1_zfmisc_1(k2_zfmisc_1(A_778, B_779))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.16/4.68  tff(c_7292, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_7273])).
% 11.16/4.68  tff(c_74, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_194])).
% 11.16/4.68  tff(c_7299, plain, (r1_tarski(k2_relat_1('#skF_6'), k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_7292, c_74])).
% 11.16/4.68  tff(c_7391, plain, (r1_tarski(k2_relat_1('#skF_6'), k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_7388, c_7299])).
% 11.16/4.68  tff(c_80, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_194])).
% 11.16/4.68  tff(c_10749, plain, (![A_1139, B_1134, F_1135, C_1138, E_1137, D_1136]: (k1_funct_1(k8_funct_2(B_1134, C_1138, A_1139, D_1136, E_1137), F_1135)=k1_funct_1(E_1137, k1_funct_1(D_1136, F_1135)) | k1_xboole_0=B_1134 | ~r1_tarski(k2_relset_1(B_1134, C_1138, D_1136), k1_relset_1(C_1138, A_1139, E_1137)) | ~m1_subset_1(F_1135, B_1134) | ~m1_subset_1(E_1137, k1_zfmisc_1(k2_zfmisc_1(C_1138, A_1139))) | ~v1_funct_1(E_1137) | ~m1_subset_1(D_1136, k1_zfmisc_1(k2_zfmisc_1(B_1134, C_1138))) | ~v1_funct_2(D_1136, B_1134, C_1138) | ~v1_funct_1(D_1136) | v1_xboole_0(C_1138))), inference(cnfTransformation, [status(thm)], [f_169])).
% 11.16/4.68  tff(c_10761, plain, (![B_1134, D_1136, F_1135]: (k1_funct_1(k8_funct_2(B_1134, '#skF_5', '#skF_3', D_1136, '#skF_7'), F_1135)=k1_funct_1('#skF_7', k1_funct_1(D_1136, F_1135)) | k1_xboole_0=B_1134 | ~r1_tarski(k2_relset_1(B_1134, '#skF_5', D_1136), k1_relat_1('#skF_7')) | ~m1_subset_1(F_1135, B_1134) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3'))) | ~v1_funct_1('#skF_7') | ~m1_subset_1(D_1136, k1_zfmisc_1(k2_zfmisc_1(B_1134, '#skF_5'))) | ~v1_funct_2(D_1136, B_1134, '#skF_5') | ~v1_funct_1(D_1136) | v1_xboole_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_7388, c_10749])).
% 11.16/4.68  tff(c_10776, plain, (![B_1134, D_1136, F_1135]: (k1_funct_1(k8_funct_2(B_1134, '#skF_5', '#skF_3', D_1136, '#skF_7'), F_1135)=k1_funct_1('#skF_7', k1_funct_1(D_1136, F_1135)) | k1_xboole_0=B_1134 | ~r1_tarski(k2_relset_1(B_1134, '#skF_5', D_1136), k1_relat_1('#skF_7')) | ~m1_subset_1(F_1135, B_1134) | ~m1_subset_1(D_1136, k1_zfmisc_1(k2_zfmisc_1(B_1134, '#skF_5'))) | ~v1_funct_2(D_1136, B_1134, '#skF_5') | ~v1_funct_1(D_1136) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_10761])).
% 11.16/4.68  tff(c_11052, plain, (![B_1164, D_1165, F_1166]: (k1_funct_1(k8_funct_2(B_1164, '#skF_5', '#skF_3', D_1165, '#skF_7'), F_1166)=k1_funct_1('#skF_7', k1_funct_1(D_1165, F_1166)) | k1_xboole_0=B_1164 | ~r1_tarski(k2_relset_1(B_1164, '#skF_5', D_1165), k1_relat_1('#skF_7')) | ~m1_subset_1(F_1166, B_1164) | ~m1_subset_1(D_1165, k1_zfmisc_1(k2_zfmisc_1(B_1164, '#skF_5'))) | ~v1_funct_2(D_1165, B_1164, '#skF_5') | ~v1_funct_1(D_1165))), inference(negUnitSimplification, [status(thm)], [c_88, c_10776])).
% 11.16/4.68  tff(c_11060, plain, (![F_1166]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_1166)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_1166)) | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relat_1('#skF_6'), k1_relat_1('#skF_7')) | ~m1_subset_1(F_1166, '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_7292, c_11052])).
% 11.16/4.68  tff(c_11067, plain, (![F_1166]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_1166)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_1166)) | k1_xboole_0='#skF_4' | ~m1_subset_1(F_1166, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_7391, c_11060])).
% 11.16/4.68  tff(c_11068, plain, (![F_1166]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_1166)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_1166)) | ~m1_subset_1(F_1166, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_72, c_11067])).
% 11.16/4.68  tff(c_213, plain, (![A_95, B_96]: (r2_hidden('#skF_2'(A_95, B_96), A_95) | r1_tarski(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.16/4.68  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.16/4.68  tff(c_217, plain, (![A_95, B_96]: (~v1_xboole_0(A_95) | r1_tarski(A_95, B_96))), inference(resolution, [status(thm)], [c_213, c_2])).
% 11.16/4.68  tff(c_135, plain, (![A_85, B_86]: (r1_tarski(A_85, B_86) | ~m1_subset_1(A_85, k1_zfmisc_1(B_86)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.16/4.68  tff(c_146, plain, (r1_tarski('#skF_7', k2_zfmisc_1('#skF_5', '#skF_3'))), inference(resolution, [status(thm)], [c_78, c_135])).
% 11.16/4.68  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.16/4.68  tff(c_384, plain, (![C_131, B_132, A_133]: (r2_hidden(C_131, B_132) | ~r2_hidden(C_131, A_133) | ~r1_tarski(A_133, B_132))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.16/4.68  tff(c_510, plain, (![A_149, B_150, B_151]: (r2_hidden('#skF_2'(A_149, B_150), B_151) | ~r1_tarski(A_149, B_151) | r1_tarski(A_149, B_150))), inference(resolution, [status(thm)], [c_10, c_384])).
% 11.16/4.68  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.16/4.68  tff(c_10852, plain, (![A_1148, B_1149, B_1150, B_1151]: (r2_hidden('#skF_2'(A_1148, B_1149), B_1150) | ~r1_tarski(B_1151, B_1150) | ~r1_tarski(A_1148, B_1151) | r1_tarski(A_1148, B_1149))), inference(resolution, [status(thm)], [c_510, c_6])).
% 11.16/4.68  tff(c_10912, plain, (![A_1155, B_1156]: (r2_hidden('#skF_2'(A_1155, B_1156), k2_zfmisc_1('#skF_5', '#skF_3')) | ~r1_tarski(A_1155, '#skF_7') | r1_tarski(A_1155, B_1156))), inference(resolution, [status(thm)], [c_146, c_10852])).
% 11.16/4.68  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.16/4.68  tff(c_10925, plain, (![A_1157]: (~r1_tarski(A_1157, '#skF_7') | r1_tarski(A_1157, k2_zfmisc_1('#skF_5', '#skF_3')))), inference(resolution, [status(thm)], [c_10912, c_8])).
% 11.16/4.68  tff(c_26, plain, (![A_14, B_15]: (r2_hidden(A_14, B_15) | v1_xboole_0(B_15) | ~m1_subset_1(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.16/4.68  tff(c_391, plain, (![A_14, B_132, B_15]: (r2_hidden(A_14, B_132) | ~r1_tarski(B_15, B_132) | v1_xboole_0(B_15) | ~m1_subset_1(A_14, B_15))), inference(resolution, [status(thm)], [c_26, c_384])).
% 11.16/4.68  tff(c_11595, plain, (![A_1204, A_1205]: (r2_hidden(A_1204, k2_zfmisc_1('#skF_5', '#skF_3')) | v1_xboole_0(A_1205) | ~m1_subset_1(A_1204, A_1205) | ~r1_tarski(A_1205, '#skF_7'))), inference(resolution, [status(thm)], [c_10925, c_391])).
% 11.16/4.68  tff(c_11610, plain, (r2_hidden('#skF_8', k2_zfmisc_1('#skF_5', '#skF_3')) | v1_xboole_0('#skF_4') | ~r1_tarski('#skF_4', '#skF_7')), inference(resolution, [status(thm)], [c_76, c_11595])).
% 11.16/4.68  tff(c_11611, plain, (~r1_tarski('#skF_4', '#skF_7')), inference(splitLeft, [status(thm)], [c_11610])).
% 11.16/4.68  tff(c_11615, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_217, c_11611])).
% 11.16/4.68  tff(c_293, plain, (![C_109, B_110, A_111]: (v5_relat_1(C_109, B_110) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_111, B_110))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.16/4.68  tff(c_311, plain, (v5_relat_1('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_78, c_293])).
% 11.16/4.68  tff(c_34, plain, (![A_21, B_22]: (v1_relat_1(k2_zfmisc_1(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 11.16/4.68  tff(c_175, plain, (![B_91, A_92]: (v1_relat_1(B_91) | ~m1_subset_1(B_91, k1_zfmisc_1(A_92)) | ~v1_relat_1(A_92))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.16/4.68  tff(c_184, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_82, c_175])).
% 11.16/4.68  tff(c_191, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_184])).
% 11.16/4.68  tff(c_7389, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_7370])).
% 11.16/4.68  tff(c_10229, plain, (![B_1069, A_1070, C_1071]: (k1_xboole_0=B_1069 | k1_relset_1(A_1070, B_1069, C_1071)=A_1070 | ~v1_funct_2(C_1071, A_1070, B_1069) | ~m1_subset_1(C_1071, k1_zfmisc_1(k2_zfmisc_1(A_1070, B_1069))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 11.16/4.68  tff(c_10242, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_82, c_10229])).
% 11.16/4.68  tff(c_10252, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_7389, c_10242])).
% 11.16/4.68  tff(c_10254, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_10252])).
% 11.16/4.68  tff(c_181, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_3'))), inference(resolution, [status(thm)], [c_78, c_175])).
% 11.16/4.68  tff(c_188, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_181])).
% 11.16/4.68  tff(c_10076, plain, (![B_1046, A_1047]: (r2_hidden(k1_funct_1(B_1046, A_1047), k2_relat_1(B_1046)) | ~r2_hidden(A_1047, k1_relat_1(B_1046)) | ~v1_funct_1(B_1046) | ~v1_relat_1(B_1046))), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.16/4.68  tff(c_11555, plain, (![B_1200, A_1201, B_1202]: (r2_hidden(k1_funct_1(B_1200, A_1201), B_1202) | ~r1_tarski(k2_relat_1(B_1200), B_1202) | ~r2_hidden(A_1201, k1_relat_1(B_1200)) | ~v1_funct_1(B_1200) | ~v1_relat_1(B_1200))), inference(resolution, [status(thm)], [c_10076, c_6])).
% 11.16/4.68  tff(c_66, plain, (![A_42, B_43, C_45]: (k7_partfun1(A_42, B_43, C_45)=k1_funct_1(B_43, C_45) | ~r2_hidden(C_45, k1_relat_1(B_43)) | ~v1_funct_1(B_43) | ~v5_relat_1(B_43, A_42) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_145])).
% 11.16/4.68  tff(c_12914, plain, (![A_1300, B_1301, B_1302, A_1303]: (k7_partfun1(A_1300, B_1301, k1_funct_1(B_1302, A_1303))=k1_funct_1(B_1301, k1_funct_1(B_1302, A_1303)) | ~v1_funct_1(B_1301) | ~v5_relat_1(B_1301, A_1300) | ~v1_relat_1(B_1301) | ~r1_tarski(k2_relat_1(B_1302), k1_relat_1(B_1301)) | ~r2_hidden(A_1303, k1_relat_1(B_1302)) | ~v1_funct_1(B_1302) | ~v1_relat_1(B_1302))), inference(resolution, [status(thm)], [c_11555, c_66])).
% 11.16/4.68  tff(c_12920, plain, (![A_1300, A_1303]: (k7_partfun1(A_1300, '#skF_7', k1_funct_1('#skF_6', A_1303))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', A_1303)) | ~v1_funct_1('#skF_7') | ~v5_relat_1('#skF_7', A_1300) | ~v1_relat_1('#skF_7') | ~r2_hidden(A_1303, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_7391, c_12914])).
% 11.16/4.68  tff(c_14224, plain, (![A_1412, A_1413]: (k7_partfun1(A_1412, '#skF_7', k1_funct_1('#skF_6', A_1413))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', A_1413)) | ~v5_relat_1('#skF_7', A_1412) | ~r2_hidden(A_1413, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_191, c_86, c_10254, c_188, c_80, c_12920])).
% 11.16/4.68  tff(c_70, plain, (k7_partfun1('#skF_3', '#skF_7', k1_funct_1('#skF_6', '#skF_8'))!=k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_194])).
% 11.16/4.68  tff(c_14230, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | ~v5_relat_1('#skF_7', '#skF_3') | ~r2_hidden('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_14224, c_70])).
% 11.16/4.68  tff(c_14236, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | ~r2_hidden('#skF_8', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_311, c_14230])).
% 11.16/4.68  tff(c_14277, plain, (~r2_hidden('#skF_8', '#skF_4')), inference(splitLeft, [status(thm)], [c_14236])).
% 11.16/4.68  tff(c_14280, plain, (v1_xboole_0('#skF_4') | ~m1_subset_1('#skF_8', '#skF_4')), inference(resolution, [status(thm)], [c_26, c_14277])).
% 11.16/4.68  tff(c_14283, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_14280])).
% 11.16/4.68  tff(c_14285, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11615, c_14283])).
% 11.16/4.68  tff(c_14286, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_14236])).
% 11.16/4.68  tff(c_14516, plain, (~m1_subset_1('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_11068, c_14286])).
% 11.16/4.68  tff(c_14520, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_14516])).
% 11.16/4.68  tff(c_14522, plain, (r1_tarski('#skF_4', '#skF_7')), inference(splitRight, [status(thm)], [c_11610])).
% 11.16/4.68  tff(c_14556, plain, (![A_14]: (r2_hidden(A_14, '#skF_7') | v1_xboole_0('#skF_4') | ~m1_subset_1(A_14, '#skF_4'))), inference(resolution, [status(thm)], [c_14522, c_391])).
% 11.16/4.68  tff(c_14635, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_14556])).
% 11.16/4.68  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.16/4.68  tff(c_218, plain, (![A_97, B_98]: (~v1_xboole_0(A_97) | r1_tarski(A_97, B_98))), inference(resolution, [status(thm)], [c_213, c_2])).
% 11.16/4.68  tff(c_14, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.16/4.68  tff(c_246, plain, (![B_102, A_103]: (B_102=A_103 | ~r1_tarski(B_102, A_103) | ~v1_xboole_0(A_103))), inference(resolution, [status(thm)], [c_218, c_14])).
% 11.16/4.68  tff(c_268, plain, (![B_104, A_105]: (B_104=A_105 | ~v1_xboole_0(B_104) | ~v1_xboole_0(A_105))), inference(resolution, [status(thm)], [c_217, c_246])).
% 11.16/4.68  tff(c_271, plain, (![A_105]: (k1_xboole_0=A_105 | ~v1_xboole_0(A_105))), inference(resolution, [status(thm)], [c_12, c_268])).
% 11.16/4.68  tff(c_14644, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_14635, c_271])).
% 11.16/4.68  tff(c_14659, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_14644])).
% 11.16/4.68  tff(c_14661, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_14556])).
% 11.16/4.68  tff(c_16026, plain, (![A_1515, B_1516, B_1517, A_1518]: (k7_partfun1(A_1515, B_1516, k1_funct_1(B_1517, A_1518))=k1_funct_1(B_1516, k1_funct_1(B_1517, A_1518)) | ~v1_funct_1(B_1516) | ~v5_relat_1(B_1516, A_1515) | ~v1_relat_1(B_1516) | ~r1_tarski(k2_relat_1(B_1517), k1_relat_1(B_1516)) | ~r2_hidden(A_1518, k1_relat_1(B_1517)) | ~v1_funct_1(B_1517) | ~v1_relat_1(B_1517))), inference(resolution, [status(thm)], [c_11555, c_66])).
% 11.16/4.68  tff(c_16032, plain, (![A_1515, A_1518]: (k7_partfun1(A_1515, '#skF_7', k1_funct_1('#skF_6', A_1518))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', A_1518)) | ~v1_funct_1('#skF_7') | ~v5_relat_1('#skF_7', A_1515) | ~v1_relat_1('#skF_7') | ~r2_hidden(A_1518, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_7391, c_16026])).
% 11.16/4.68  tff(c_19268, plain, (![A_1709, A_1710]: (k7_partfun1(A_1709, '#skF_7', k1_funct_1('#skF_6', A_1710))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', A_1710)) | ~v5_relat_1('#skF_7', A_1709) | ~r2_hidden(A_1710, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_191, c_86, c_10254, c_188, c_80, c_16032])).
% 11.16/4.68  tff(c_19274, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | ~v5_relat_1('#skF_7', '#skF_3') | ~r2_hidden('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_19268, c_70])).
% 11.16/4.68  tff(c_19280, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | ~r2_hidden('#skF_8', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_311, c_19274])).
% 11.16/4.68  tff(c_19288, plain, (~r2_hidden('#skF_8', '#skF_4')), inference(splitLeft, [status(thm)], [c_19280])).
% 11.16/4.68  tff(c_19297, plain, (v1_xboole_0('#skF_4') | ~m1_subset_1('#skF_8', '#skF_4')), inference(resolution, [status(thm)], [c_26, c_19288])).
% 11.16/4.68  tff(c_19304, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_19297])).
% 11.16/4.68  tff(c_19306, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14661, c_19304])).
% 11.16/4.68  tff(c_19307, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_19280])).
% 11.16/4.68  tff(c_19429, plain, (~m1_subset_1('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_11068, c_19307])).
% 11.16/4.68  tff(c_19433, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_19429])).
% 11.16/4.68  tff(c_19434, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_10252])).
% 11.16/4.68  tff(c_19471, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_19434, c_12])).
% 11.16/4.68  tff(c_19474, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_19471])).
% 11.16/4.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.16/4.68  
% 11.16/4.68  Inference rules
% 11.16/4.68  ----------------------
% 11.16/4.68  #Ref     : 6
% 11.16/4.68  #Sup     : 4142
% 11.16/4.68  #Fact    : 0
% 11.16/4.68  #Define  : 0
% 11.16/4.68  #Split   : 152
% 11.16/4.68  #Chain   : 0
% 11.16/4.68  #Close   : 0
% 11.16/4.68  
% 11.16/4.68  Ordering : KBO
% 11.16/4.68  
% 11.16/4.68  Simplification rules
% 11.16/4.68  ----------------------
% 11.16/4.68  #Subsume      : 1631
% 11.16/4.68  #Demod        : 3380
% 11.16/4.68  #Tautology    : 1089
% 11.16/4.68  #SimpNegUnit  : 333
% 11.16/4.68  #BackRed      : 887
% 11.16/4.68  
% 11.16/4.68  #Partial instantiations: 0
% 11.16/4.68  #Strategies tried      : 1
% 11.16/4.68  
% 11.16/4.68  Timing (in seconds)
% 11.16/4.68  ----------------------
% 11.16/4.68  Preprocessing        : 0.39
% 11.16/4.68  Parsing              : 0.20
% 11.16/4.68  CNF conversion       : 0.03
% 11.16/4.68  Main loop            : 3.47
% 11.16/4.68  Inferencing          : 0.98
% 11.16/4.68  Reduction            : 1.21
% 11.16/4.68  Demodulation         : 0.79
% 11.16/4.68  BG Simplification    : 0.09
% 11.16/4.68  Subsumption          : 0.91
% 11.16/4.68  Abstraction          : 0.11
% 11.16/4.68  MUC search           : 0.00
% 11.16/4.68  Cooper               : 0.00
% 11.16/4.68  Total                : 3.90
% 11.16/4.68  Index Insertion      : 0.00
% 11.16/4.68  Index Deletion       : 0.00
% 11.16/4.68  Index Matching       : 0.00
% 11.16/4.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
