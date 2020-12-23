%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:49 EST 2020

% Result     : Theorem 5.18s
% Output     : CNFRefutation 5.58s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 209 expanded)
%              Number of leaves         :   41 (  92 expanded)
%              Depth                    :   15
%              Number of atoms          :  194 ( 724 expanded)
%              Number of equality atoms :   41 ( 143 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2

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

tff(f_137,negated_conjecture,(
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

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_100,axiom,(
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

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_112,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_42,plain,(
    m1_subset_1('#skF_8','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_52,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_50,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_44,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_182,plain,(
    ! [A_96,B_97,C_98] :
      ( k1_relset_1(A_96,B_97,C_98) = k1_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_189,plain,(
    k1_relset_1('#skF_5','#skF_3','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_182])).

tff(c_40,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_191,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_40])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_46,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_575,plain,(
    ! [B_155,A_156,C_152,F_154,D_151,E_153] :
      ( k1_funct_1(k8_funct_2(B_155,C_152,A_156,D_151,E_153),F_154) = k1_funct_1(E_153,k1_funct_1(D_151,F_154))
      | k1_xboole_0 = B_155
      | ~ r1_tarski(k2_relset_1(B_155,C_152,D_151),k1_relset_1(C_152,A_156,E_153))
      | ~ m1_subset_1(F_154,B_155)
      | ~ m1_subset_1(E_153,k1_zfmisc_1(k2_zfmisc_1(C_152,A_156)))
      | ~ v1_funct_1(E_153)
      | ~ m1_subset_1(D_151,k1_zfmisc_1(k2_zfmisc_1(B_155,C_152)))
      | ~ v1_funct_2(D_151,B_155,C_152)
      | ~ v1_funct_1(D_151)
      | v1_xboole_0(C_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_579,plain,(
    ! [B_155,D_151,F_154] :
      ( k1_funct_1(k8_funct_2(B_155,'#skF_5','#skF_3',D_151,'#skF_7'),F_154) = k1_funct_1('#skF_7',k1_funct_1(D_151,F_154))
      | k1_xboole_0 = B_155
      | ~ r1_tarski(k2_relset_1(B_155,'#skF_5',D_151),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_154,B_155)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(D_151,k1_zfmisc_1(k2_zfmisc_1(B_155,'#skF_5')))
      | ~ v1_funct_2(D_151,B_155,'#skF_5')
      | ~ v1_funct_1(D_151)
      | v1_xboole_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_575])).

tff(c_586,plain,(
    ! [B_155,D_151,F_154] :
      ( k1_funct_1(k8_funct_2(B_155,'#skF_5','#skF_3',D_151,'#skF_7'),F_154) = k1_funct_1('#skF_7',k1_funct_1(D_151,F_154))
      | k1_xboole_0 = B_155
      | ~ r1_tarski(k2_relset_1(B_155,'#skF_5',D_151),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_154,B_155)
      | ~ m1_subset_1(D_151,k1_zfmisc_1(k2_zfmisc_1(B_155,'#skF_5')))
      | ~ v1_funct_2(D_151,B_155,'#skF_5')
      | ~ v1_funct_1(D_151)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_579])).

tff(c_625,plain,(
    ! [B_165,D_166,F_167] :
      ( k1_funct_1(k8_funct_2(B_165,'#skF_5','#skF_3',D_166,'#skF_7'),F_167) = k1_funct_1('#skF_7',k1_funct_1(D_166,F_167))
      | k1_xboole_0 = B_165
      | ~ r1_tarski(k2_relset_1(B_165,'#skF_5',D_166),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_167,B_165)
      | ~ m1_subset_1(D_166,k1_zfmisc_1(k2_zfmisc_1(B_165,'#skF_5')))
      | ~ v1_funct_2(D_166,B_165,'#skF_5')
      | ~ v1_funct_1(D_166) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_586])).

tff(c_627,plain,(
    ! [F_167] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_167) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_167))
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1(F_167,'#skF_4')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_191,c_625])).

tff(c_633,plain,(
    ! [F_167] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_167) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_167))
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1(F_167,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_627])).

tff(c_634,plain,(
    ! [F_167] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_167) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_167))
      | ~ m1_subset_1(F_167,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_633])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( r2_hidden(A_12,B_13)
      | v1_xboole_0(B_13)
      | ~ m1_subset_1(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_142,plain,(
    ! [C_84,B_85,A_86] :
      ( v5_relat_1(C_84,B_85)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_86,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_149,plain,(
    v5_relat_1('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_142])).

tff(c_68,plain,(
    ! [C_65,A_66,B_67] :
      ( v1_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_75,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_68])).

tff(c_506,plain,(
    ! [D_137,C_138,A_139,B_140] :
      ( r2_hidden(k1_funct_1(D_137,C_138),k2_relset_1(A_139,B_140,D_137))
      | k1_xboole_0 = B_140
      | ~ r2_hidden(C_138,A_139)
      | ~ m1_subset_1(D_137,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140)))
      | ~ v1_funct_2(D_137,A_139,B_140)
      | ~ v1_funct_1(D_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_937,plain,(
    ! [B_216,A_215,B_217,C_214,D_218] :
      ( r2_hidden(k1_funct_1(D_218,C_214),B_217)
      | ~ r1_tarski(k2_relset_1(A_215,B_216,D_218),B_217)
      | k1_xboole_0 = B_216
      | ~ r2_hidden(C_214,A_215)
      | ~ m1_subset_1(D_218,k1_zfmisc_1(k2_zfmisc_1(A_215,B_216)))
      | ~ v1_funct_2(D_218,A_215,B_216)
      | ~ v1_funct_1(D_218) ) ),
    inference(resolution,[status(thm)],[c_506,c_6])).

tff(c_939,plain,(
    ! [C_214] :
      ( r2_hidden(k1_funct_1('#skF_6',C_214),k1_relat_1('#skF_7'))
      | k1_xboole_0 = '#skF_5'
      | ~ r2_hidden(C_214,'#skF_4')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_191,c_937])).

tff(c_948,plain,(
    ! [C_214] :
      ( r2_hidden(k1_funct_1('#skF_6',C_214),k1_relat_1('#skF_7'))
      | k1_xboole_0 = '#skF_5'
      | ~ r2_hidden(C_214,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_939])).

tff(c_951,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_948])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_967,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_951,c_12])).

tff(c_970,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_967])).

tff(c_974,plain,(
    ! [C_219] :
      ( r2_hidden(k1_funct_1('#skF_6',C_219),k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_219,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_948])).

tff(c_30,plain,(
    ! [A_23,B_24,C_26] :
      ( k7_partfun1(A_23,B_24,C_26) = k1_funct_1(B_24,C_26)
      | ~ r2_hidden(C_26,k1_relat_1(B_24))
      | ~ v1_funct_1(B_24)
      | ~ v5_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_978,plain,(
    ! [A_23,C_219] :
      ( k7_partfun1(A_23,'#skF_7',k1_funct_1('#skF_6',C_219)) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',C_219))
      | ~ v1_funct_1('#skF_7')
      | ~ v5_relat_1('#skF_7',A_23)
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(C_219,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_974,c_30])).

tff(c_1019,plain,(
    ! [A_225,C_226] :
      ( k7_partfun1(A_225,'#skF_7',k1_funct_1('#skF_6',C_226)) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',C_226))
      | ~ v5_relat_1('#skF_7',A_225)
      | ~ r2_hidden(C_226,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_46,c_978])).

tff(c_36,plain,(
    k7_partfun1('#skF_3','#skF_7',k1_funct_1('#skF_6','#skF_8')) != k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1025,plain,
    ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
    | ~ v5_relat_1('#skF_7','#skF_3')
    | ~ r2_hidden('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1019,c_36])).

tff(c_1031,plain,
    ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
    | ~ r2_hidden('#skF_8','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_1025])).

tff(c_1045,plain,(
    ~ r2_hidden('#skF_8','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1031])).

tff(c_1048,plain,
    ( v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_1045])).

tff(c_1051,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1048])).

tff(c_77,plain,(
    ! [A_68,B_69] :
      ( r2_hidden('#skF_2'(A_68,B_69),A_68)
      | r1_tarski(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_81,plain,(
    ! [A_68,B_69] :
      ( ~ v1_xboole_0(A_68)
      | r1_tarski(A_68,B_69) ) ),
    inference(resolution,[status(thm)],[c_77,c_2])).

tff(c_83,plain,(
    ! [B_72,A_73] :
      ( B_72 = A_73
      | ~ r1_tarski(B_72,A_73)
      | ~ r1_tarski(A_73,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_96,plain,(
    ! [B_74,A_75] :
      ( B_74 = A_75
      | ~ r1_tarski(B_74,A_75)
      | ~ v1_xboole_0(A_75) ) ),
    inference(resolution,[status(thm)],[c_81,c_83])).

tff(c_110,plain,(
    ! [B_76,A_77] :
      ( B_76 = A_77
      | ~ v1_xboole_0(B_76)
      | ~ v1_xboole_0(A_77) ) ),
    inference(resolution,[status(thm)],[c_81,c_96])).

tff(c_113,plain,(
    ! [A_77] :
      ( k1_xboole_0 = A_77
      | ~ v1_xboole_0(A_77) ) ),
    inference(resolution,[status(thm)],[c_12,c_110])).

tff(c_1054,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1051,c_113])).

tff(c_1060,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1054])).

tff(c_1061,plain,(
    k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_1031])).

tff(c_1120,plain,(
    ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_634,c_1061])).

tff(c_1124,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1120])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:42:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.18/2.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.18/2.36  
% 5.18/2.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.18/2.36  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2
% 5.18/2.36  
% 5.18/2.36  %Foreground sorts:
% 5.18/2.36  
% 5.18/2.36  
% 5.18/2.36  %Background operators:
% 5.18/2.36  
% 5.18/2.36  
% 5.18/2.36  %Foreground operators:
% 5.18/2.36  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.18/2.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.18/2.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.18/2.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.18/2.36  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.18/2.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.18/2.36  tff('#skF_7', type, '#skF_7': $i).
% 5.18/2.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.18/2.36  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 5.18/2.36  tff('#skF_5', type, '#skF_5': $i).
% 5.18/2.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.18/2.36  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 5.18/2.36  tff('#skF_6', type, '#skF_6': $i).
% 5.18/2.36  tff('#skF_3', type, '#skF_3': $i).
% 5.18/2.36  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.18/2.36  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.18/2.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.18/2.36  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.18/2.36  tff('#skF_8', type, '#skF_8': $i).
% 5.18/2.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.18/2.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.18/2.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.18/2.36  tff('#skF_4', type, '#skF_4': $i).
% 5.18/2.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.18/2.36  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.18/2.36  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.18/2.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.18/2.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.18/2.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.18/2.36  
% 5.58/2.39  tff(f_137, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 5.58/2.39  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.58/2.39  tff(f_100, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 5.58/2.39  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 5.58/2.39  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.58/2.39  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.58/2.39  tff(f_112, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 5.58/2.39  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.58/2.39  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.58/2.39  tff(f_76, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 5.58/2.39  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.58/2.39  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.58/2.39  tff(c_42, plain, (m1_subset_1('#skF_8', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.58/2.39  tff(c_38, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.58/2.39  tff(c_52, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.58/2.39  tff(c_50, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.58/2.39  tff(c_48, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.58/2.39  tff(c_44, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.58/2.39  tff(c_182, plain, (![A_96, B_97, C_98]: (k1_relset_1(A_96, B_97, C_98)=k1_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.58/2.39  tff(c_189, plain, (k1_relset_1('#skF_5', '#skF_3', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_44, c_182])).
% 5.58/2.39  tff(c_40, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.58/2.39  tff(c_191, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_40])).
% 5.58/2.39  tff(c_54, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.58/2.39  tff(c_46, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.58/2.39  tff(c_575, plain, (![B_155, A_156, C_152, F_154, D_151, E_153]: (k1_funct_1(k8_funct_2(B_155, C_152, A_156, D_151, E_153), F_154)=k1_funct_1(E_153, k1_funct_1(D_151, F_154)) | k1_xboole_0=B_155 | ~r1_tarski(k2_relset_1(B_155, C_152, D_151), k1_relset_1(C_152, A_156, E_153)) | ~m1_subset_1(F_154, B_155) | ~m1_subset_1(E_153, k1_zfmisc_1(k2_zfmisc_1(C_152, A_156))) | ~v1_funct_1(E_153) | ~m1_subset_1(D_151, k1_zfmisc_1(k2_zfmisc_1(B_155, C_152))) | ~v1_funct_2(D_151, B_155, C_152) | ~v1_funct_1(D_151) | v1_xboole_0(C_152))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.58/2.39  tff(c_579, plain, (![B_155, D_151, F_154]: (k1_funct_1(k8_funct_2(B_155, '#skF_5', '#skF_3', D_151, '#skF_7'), F_154)=k1_funct_1('#skF_7', k1_funct_1(D_151, F_154)) | k1_xboole_0=B_155 | ~r1_tarski(k2_relset_1(B_155, '#skF_5', D_151), k1_relat_1('#skF_7')) | ~m1_subset_1(F_154, B_155) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3'))) | ~v1_funct_1('#skF_7') | ~m1_subset_1(D_151, k1_zfmisc_1(k2_zfmisc_1(B_155, '#skF_5'))) | ~v1_funct_2(D_151, B_155, '#skF_5') | ~v1_funct_1(D_151) | v1_xboole_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_189, c_575])).
% 5.58/2.39  tff(c_586, plain, (![B_155, D_151, F_154]: (k1_funct_1(k8_funct_2(B_155, '#skF_5', '#skF_3', D_151, '#skF_7'), F_154)=k1_funct_1('#skF_7', k1_funct_1(D_151, F_154)) | k1_xboole_0=B_155 | ~r1_tarski(k2_relset_1(B_155, '#skF_5', D_151), k1_relat_1('#skF_7')) | ~m1_subset_1(F_154, B_155) | ~m1_subset_1(D_151, k1_zfmisc_1(k2_zfmisc_1(B_155, '#skF_5'))) | ~v1_funct_2(D_151, B_155, '#skF_5') | ~v1_funct_1(D_151) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_579])).
% 5.58/2.39  tff(c_625, plain, (![B_165, D_166, F_167]: (k1_funct_1(k8_funct_2(B_165, '#skF_5', '#skF_3', D_166, '#skF_7'), F_167)=k1_funct_1('#skF_7', k1_funct_1(D_166, F_167)) | k1_xboole_0=B_165 | ~r1_tarski(k2_relset_1(B_165, '#skF_5', D_166), k1_relat_1('#skF_7')) | ~m1_subset_1(F_167, B_165) | ~m1_subset_1(D_166, k1_zfmisc_1(k2_zfmisc_1(B_165, '#skF_5'))) | ~v1_funct_2(D_166, B_165, '#skF_5') | ~v1_funct_1(D_166))), inference(negUnitSimplification, [status(thm)], [c_54, c_586])).
% 5.58/2.39  tff(c_627, plain, (![F_167]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_167)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_167)) | k1_xboole_0='#skF_4' | ~m1_subset_1(F_167, '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_191, c_625])).
% 5.58/2.39  tff(c_633, plain, (![F_167]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_167)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_167)) | k1_xboole_0='#skF_4' | ~m1_subset_1(F_167, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_627])).
% 5.58/2.39  tff(c_634, plain, (![F_167]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_167)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_167)) | ~m1_subset_1(F_167, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_38, c_633])).
% 5.58/2.39  tff(c_20, plain, (![A_12, B_13]: (r2_hidden(A_12, B_13) | v1_xboole_0(B_13) | ~m1_subset_1(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.58/2.39  tff(c_142, plain, (![C_84, B_85, A_86]: (v5_relat_1(C_84, B_85) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_86, B_85))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.58/2.39  tff(c_149, plain, (v5_relat_1('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_142])).
% 5.58/2.39  tff(c_68, plain, (![C_65, A_66, B_67]: (v1_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.58/2.39  tff(c_75, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_44, c_68])).
% 5.58/2.39  tff(c_506, plain, (![D_137, C_138, A_139, B_140]: (r2_hidden(k1_funct_1(D_137, C_138), k2_relset_1(A_139, B_140, D_137)) | k1_xboole_0=B_140 | ~r2_hidden(C_138, A_139) | ~m1_subset_1(D_137, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))) | ~v1_funct_2(D_137, A_139, B_140) | ~v1_funct_1(D_137))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.58/2.39  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.58/2.39  tff(c_937, plain, (![B_216, A_215, B_217, C_214, D_218]: (r2_hidden(k1_funct_1(D_218, C_214), B_217) | ~r1_tarski(k2_relset_1(A_215, B_216, D_218), B_217) | k1_xboole_0=B_216 | ~r2_hidden(C_214, A_215) | ~m1_subset_1(D_218, k1_zfmisc_1(k2_zfmisc_1(A_215, B_216))) | ~v1_funct_2(D_218, A_215, B_216) | ~v1_funct_1(D_218))), inference(resolution, [status(thm)], [c_506, c_6])).
% 5.58/2.39  tff(c_939, plain, (![C_214]: (r2_hidden(k1_funct_1('#skF_6', C_214), k1_relat_1('#skF_7')) | k1_xboole_0='#skF_5' | ~r2_hidden(C_214, '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_191, c_937])).
% 5.58/2.39  tff(c_948, plain, (![C_214]: (r2_hidden(k1_funct_1('#skF_6', C_214), k1_relat_1('#skF_7')) | k1_xboole_0='#skF_5' | ~r2_hidden(C_214, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_939])).
% 5.58/2.39  tff(c_951, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_948])).
% 5.58/2.39  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.58/2.39  tff(c_967, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_951, c_12])).
% 5.58/2.39  tff(c_970, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_967])).
% 5.58/2.39  tff(c_974, plain, (![C_219]: (r2_hidden(k1_funct_1('#skF_6', C_219), k1_relat_1('#skF_7')) | ~r2_hidden(C_219, '#skF_4'))), inference(splitRight, [status(thm)], [c_948])).
% 5.58/2.39  tff(c_30, plain, (![A_23, B_24, C_26]: (k7_partfun1(A_23, B_24, C_26)=k1_funct_1(B_24, C_26) | ~r2_hidden(C_26, k1_relat_1(B_24)) | ~v1_funct_1(B_24) | ~v5_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.58/2.39  tff(c_978, plain, (![A_23, C_219]: (k7_partfun1(A_23, '#skF_7', k1_funct_1('#skF_6', C_219))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', C_219)) | ~v1_funct_1('#skF_7') | ~v5_relat_1('#skF_7', A_23) | ~v1_relat_1('#skF_7') | ~r2_hidden(C_219, '#skF_4'))), inference(resolution, [status(thm)], [c_974, c_30])).
% 5.58/2.39  tff(c_1019, plain, (![A_225, C_226]: (k7_partfun1(A_225, '#skF_7', k1_funct_1('#skF_6', C_226))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', C_226)) | ~v5_relat_1('#skF_7', A_225) | ~r2_hidden(C_226, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_46, c_978])).
% 5.58/2.39  tff(c_36, plain, (k7_partfun1('#skF_3', '#skF_7', k1_funct_1('#skF_6', '#skF_8'))!=k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.58/2.39  tff(c_1025, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | ~v5_relat_1('#skF_7', '#skF_3') | ~r2_hidden('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1019, c_36])).
% 5.58/2.39  tff(c_1031, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | ~r2_hidden('#skF_8', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_149, c_1025])).
% 5.58/2.39  tff(c_1045, plain, (~r2_hidden('#skF_8', '#skF_4')), inference(splitLeft, [status(thm)], [c_1031])).
% 5.58/2.39  tff(c_1048, plain, (v1_xboole_0('#skF_4') | ~m1_subset_1('#skF_8', '#skF_4')), inference(resolution, [status(thm)], [c_20, c_1045])).
% 5.58/2.39  tff(c_1051, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1048])).
% 5.58/2.39  tff(c_77, plain, (![A_68, B_69]: (r2_hidden('#skF_2'(A_68, B_69), A_68) | r1_tarski(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.58/2.39  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.58/2.39  tff(c_81, plain, (![A_68, B_69]: (~v1_xboole_0(A_68) | r1_tarski(A_68, B_69))), inference(resolution, [status(thm)], [c_77, c_2])).
% 5.58/2.39  tff(c_83, plain, (![B_72, A_73]: (B_72=A_73 | ~r1_tarski(B_72, A_73) | ~r1_tarski(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.58/2.39  tff(c_96, plain, (![B_74, A_75]: (B_74=A_75 | ~r1_tarski(B_74, A_75) | ~v1_xboole_0(A_75))), inference(resolution, [status(thm)], [c_81, c_83])).
% 5.58/2.39  tff(c_110, plain, (![B_76, A_77]: (B_76=A_77 | ~v1_xboole_0(B_76) | ~v1_xboole_0(A_77))), inference(resolution, [status(thm)], [c_81, c_96])).
% 5.58/2.39  tff(c_113, plain, (![A_77]: (k1_xboole_0=A_77 | ~v1_xboole_0(A_77))), inference(resolution, [status(thm)], [c_12, c_110])).
% 5.58/2.39  tff(c_1054, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1051, c_113])).
% 5.58/2.39  tff(c_1060, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_1054])).
% 5.58/2.39  tff(c_1061, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_1031])).
% 5.58/2.39  tff(c_1120, plain, (~m1_subset_1('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_634, c_1061])).
% 5.58/2.39  tff(c_1124, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_1120])).
% 5.58/2.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.58/2.39  
% 5.58/2.39  Inference rules
% 5.58/2.39  ----------------------
% 5.58/2.39  #Ref     : 0
% 5.58/2.39  #Sup     : 234
% 5.58/2.39  #Fact    : 0
% 5.58/2.39  #Define  : 0
% 5.58/2.39  #Split   : 11
% 5.58/2.39  #Chain   : 0
% 5.58/2.39  #Close   : 0
% 5.58/2.39  
% 5.58/2.39  Ordering : KBO
% 5.58/2.39  
% 5.58/2.39  Simplification rules
% 5.58/2.39  ----------------------
% 5.58/2.39  #Subsume      : 66
% 5.58/2.39  #Demod        : 163
% 5.58/2.39  #Tautology    : 52
% 5.58/2.39  #SimpNegUnit  : 14
% 5.58/2.39  #BackRed      : 33
% 5.58/2.39  
% 5.58/2.39  #Partial instantiations: 0
% 5.58/2.39  #Strategies tried      : 1
% 5.58/2.39  
% 5.58/2.39  Timing (in seconds)
% 5.58/2.39  ----------------------
% 5.58/2.40  Preprocessing        : 0.55
% 5.58/2.40  Parsing              : 0.28
% 5.58/2.40  CNF conversion       : 0.05
% 5.58/2.40  Main loop            : 0.89
% 5.58/2.40  Inferencing          : 0.30
% 5.58/2.40  Reduction            : 0.28
% 5.58/2.40  Demodulation         : 0.19
% 5.58/2.40  BG Simplification    : 0.04
% 5.58/2.40  Subsumption          : 0.20
% 5.58/2.40  Abstraction          : 0.05
% 5.58/2.40  MUC search           : 0.00
% 5.58/2.40  Cooper               : 0.00
% 5.58/2.40  Total                : 1.51
% 5.58/2.40  Index Insertion      : 0.00
% 5.58/2.40  Index Deletion       : 0.00
% 5.58/2.40  Index Matching       : 0.00
% 5.58/2.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
