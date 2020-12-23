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
% DateTime   : Thu Dec  3 10:16:33 EST 2020

% Result     : Theorem 7.29s
% Output     : CNFRefutation 7.29s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 402 expanded)
%              Number of leaves         :   36 ( 148 expanded)
%              Depth                    :   10
%              Number of atoms          :  271 (1182 expanded)
%              Number of equality atoms :   29 ( 156 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_146,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ( m1_subset_1(F,A)
                 => ~ ( r2_hidden(F,C)
                      & E = k1_funct_1(D,F) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_101,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_93,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_127,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ~ v1_xboole_0(C)
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
                 => ! [E] :
                      ( m1_subset_1(E,A)
                     => ( r2_hidden(E,k7_relset_1(C,A,D,B))
                      <=> ? [F] :
                            ( m1_subset_1(F,C)
                            & r2_hidden(k4_tarski(F,E),D)
                            & r2_hidden(F,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(c_54,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_98,plain,(
    ! [C_149,A_150,B_151] :
      ( v1_relat_1(C_149)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_112,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_98])).

tff(c_10,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ v1_xboole_0(B_6)
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r2_hidden(B_6,A_5)
      | ~ m1_subset_1(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_124,plain,(
    ! [F_156] :
      ( k1_funct_1('#skF_7',F_156) != '#skF_8'
      | ~ r2_hidden(F_156,'#skF_6')
      | ~ m1_subset_1(F_156,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_133,plain,(
    ! [B_6] :
      ( k1_funct_1('#skF_7',B_6) != '#skF_8'
      | ~ m1_subset_1(B_6,'#skF_4')
      | ~ m1_subset_1(B_6,'#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_8,c_124])).

tff(c_216,plain,(
    ! [B_178] :
      ( k1_funct_1('#skF_7',B_178) != '#skF_8'
      | ~ m1_subset_1(B_178,'#skF_4')
      | ~ m1_subset_1(B_178,'#skF_6') ) ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_225,plain,(
    ! [B_6] :
      ( k1_funct_1('#skF_7',B_6) != '#skF_8'
      | ~ m1_subset_1(B_6,'#skF_4')
      | ~ v1_xboole_0(B_6)
      | ~ v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_10,c_216])).

tff(c_227,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_225])).

tff(c_394,plain,(
    ! [A_215,B_216,C_217,D_218] :
      ( k7_relset_1(A_215,B_216,C_217,D_218) = k9_relat_1(C_217,D_218)
      | ~ m1_subset_1(C_217,k1_zfmisc_1(k2_zfmisc_1(A_215,B_216))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_415,plain,(
    ! [D_218] : k7_relset_1('#skF_4','#skF_5','#skF_7',D_218) = k9_relat_1('#skF_7',D_218) ),
    inference(resolution,[status(thm)],[c_54,c_394])).

tff(c_52,plain,(
    r2_hidden('#skF_8',k7_relset_1('#skF_4','#skF_5','#skF_7','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_418,plain,(
    r2_hidden('#skF_8',k9_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_415,c_52])).

tff(c_419,plain,(
    ! [D_219] : k7_relset_1('#skF_4','#skF_5','#skF_7',D_219) = k9_relat_1('#skF_7',D_219) ),
    inference(resolution,[status(thm)],[c_54,c_394])).

tff(c_38,plain,(
    ! [A_32,B_33,C_34,D_35] :
      ( m1_subset_1(k7_relset_1(A_32,B_33,C_34,D_35),k1_zfmisc_1(B_33))
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_425,plain,(
    ! [D_219] :
      ( m1_subset_1(k9_relat_1('#skF_7',D_219),k1_zfmisc_1('#skF_5'))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_419,c_38])).

tff(c_481,plain,(
    ! [D_220] : m1_subset_1(k9_relat_1('#skF_7',D_220),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_425])).

tff(c_16,plain,(
    ! [A_9,C_11,B_10] :
      ( m1_subset_1(A_9,C_11)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(C_11))
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_549,plain,(
    ! [A_224,D_225] :
      ( m1_subset_1(A_224,'#skF_5')
      | ~ r2_hidden(A_224,k9_relat_1('#skF_7',D_225)) ) ),
    inference(resolution,[status(thm)],[c_481,c_16])).

tff(c_570,plain,(
    m1_subset_1('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_418,c_549])).

tff(c_135,plain,(
    ! [C_157,B_158,A_159] :
      ( v1_xboole_0(C_157)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(B_158,A_159)))
      | ~ v1_xboole_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_151,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_135])).

tff(c_152,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_166,plain,(
    ! [C_165,A_166,B_167] :
      ( v1_xboole_0(C_165)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167)))
      | ~ v1_xboole_0(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_182,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_166])).

tff(c_183,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_182])).

tff(c_1046,plain,(
    ! [C_290,B_292,A_288,E_289,D_291] :
      ( r2_hidden('#skF_3'(A_288,E_289,C_290,D_291,B_292),B_292)
      | ~ r2_hidden(E_289,k7_relset_1(C_290,A_288,D_291,B_292))
      | ~ m1_subset_1(E_289,A_288)
      | ~ m1_subset_1(D_291,k1_zfmisc_1(k2_zfmisc_1(C_290,A_288)))
      | v1_xboole_0(C_290)
      | v1_xboole_0(B_292)
      | v1_xboole_0(A_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1063,plain,(
    ! [E_289,B_292] :
      ( r2_hidden('#skF_3'('#skF_5',E_289,'#skF_4','#skF_7',B_292),B_292)
      | ~ r2_hidden(E_289,k7_relset_1('#skF_4','#skF_5','#skF_7',B_292))
      | ~ m1_subset_1(E_289,'#skF_5')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(B_292)
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_1046])).

tff(c_1072,plain,(
    ! [E_289,B_292] :
      ( r2_hidden('#skF_3'('#skF_5',E_289,'#skF_4','#skF_7',B_292),B_292)
      | ~ r2_hidden(E_289,k9_relat_1('#skF_7',B_292))
      | ~ m1_subset_1(E_289,'#skF_5')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(B_292)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_415,c_1063])).

tff(c_2082,plain,(
    ! [E_437,B_438] :
      ( r2_hidden('#skF_3'('#skF_5',E_437,'#skF_4','#skF_7',B_438),B_438)
      | ~ r2_hidden(E_437,k9_relat_1('#skF_7',B_438))
      | ~ m1_subset_1(E_437,'#skF_5')
      | v1_xboole_0(B_438) ) ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_183,c_1072])).

tff(c_50,plain,(
    ! [F_138] :
      ( k1_funct_1('#skF_7',F_138) != '#skF_8'
      | ~ r2_hidden(F_138,'#skF_6')
      | ~ m1_subset_1(F_138,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_2178,plain,(
    ! [E_437] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_5',E_437,'#skF_4','#skF_7','#skF_6')) != '#skF_8'
      | ~ m1_subset_1('#skF_3'('#skF_5',E_437,'#skF_4','#skF_7','#skF_6'),'#skF_4')
      | ~ r2_hidden(E_437,k9_relat_1('#skF_7','#skF_6'))
      | ~ m1_subset_1(E_437,'#skF_5')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2082,c_50])).

tff(c_2315,plain,(
    ! [E_452] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_5',E_452,'#skF_4','#skF_7','#skF_6')) != '#skF_8'
      | ~ m1_subset_1('#skF_3'('#skF_5',E_452,'#skF_4','#skF_7','#skF_6'),'#skF_4')
      | ~ r2_hidden(E_452,k9_relat_1('#skF_7','#skF_6'))
      | ~ m1_subset_1(E_452,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_227,c_2178])).

tff(c_2334,plain,
    ( k1_funct_1('#skF_7','#skF_3'('#skF_5','#skF_8','#skF_4','#skF_7','#skF_6')) != '#skF_8'
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8','#skF_4','#skF_7','#skF_6'),'#skF_4')
    | ~ m1_subset_1('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_418,c_2315])).

tff(c_2355,plain,
    ( k1_funct_1('#skF_7','#skF_3'('#skF_5','#skF_8','#skF_4','#skF_7','#skF_6')) != '#skF_8'
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_8','#skF_4','#skF_7','#skF_6'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_570,c_2334])).

tff(c_2363,plain,(
    ~ m1_subset_1('#skF_3'('#skF_5','#skF_8','#skF_4','#skF_7','#skF_6'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2355])).

tff(c_902,plain,(
    ! [D_264,C_263,E_262,A_261,B_265] :
      ( m1_subset_1('#skF_3'(A_261,E_262,C_263,D_264,B_265),C_263)
      | ~ r2_hidden(E_262,k7_relset_1(C_263,A_261,D_264,B_265))
      | ~ m1_subset_1(E_262,A_261)
      | ~ m1_subset_1(D_264,k1_zfmisc_1(k2_zfmisc_1(C_263,A_261)))
      | v1_xboole_0(C_263)
      | v1_xboole_0(B_265)
      | v1_xboole_0(A_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_910,plain,(
    ! [E_262,D_218] :
      ( m1_subset_1('#skF_3'('#skF_5',E_262,'#skF_4','#skF_7',D_218),'#skF_4')
      | ~ r2_hidden(E_262,k9_relat_1('#skF_7',D_218))
      | ~ m1_subset_1(E_262,'#skF_5')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(D_218)
      | v1_xboole_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_415,c_902])).

tff(c_923,plain,(
    ! [E_262,D_218] :
      ( m1_subset_1('#skF_3'('#skF_5',E_262,'#skF_4','#skF_7',D_218),'#skF_4')
      | ~ r2_hidden(E_262,k9_relat_1('#skF_7',D_218))
      | ~ m1_subset_1(E_262,'#skF_5')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(D_218)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_910])).

tff(c_2368,plain,(
    ! [E_453,D_454] :
      ( m1_subset_1('#skF_3'('#skF_5',E_453,'#skF_4','#skF_7',D_454),'#skF_4')
      | ~ r2_hidden(E_453,k9_relat_1('#skF_7',D_454))
      | ~ m1_subset_1(E_453,'#skF_5')
      | v1_xboole_0(D_454) ) ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_183,c_923])).

tff(c_2391,plain,
    ( m1_subset_1('#skF_3'('#skF_5','#skF_8','#skF_4','#skF_7','#skF_6'),'#skF_4')
    | ~ m1_subset_1('#skF_8','#skF_5')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_418,c_2368])).

tff(c_2414,plain,
    ( m1_subset_1('#skF_3'('#skF_5','#skF_8','#skF_4','#skF_7','#skF_6'),'#skF_4')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_570,c_2391])).

tff(c_2416,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_227,c_2363,c_2414])).

tff(c_2417,plain,(
    k1_funct_1('#skF_7','#skF_3'('#skF_5','#skF_8','#skF_4','#skF_7','#skF_6')) != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_2355])).

tff(c_58,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1287,plain,(
    ! [C_322,A_320,D_323,B_324,E_321] :
      ( r2_hidden(k4_tarski('#skF_3'(A_320,E_321,C_322,D_323,B_324),E_321),D_323)
      | ~ r2_hidden(E_321,k7_relset_1(C_322,A_320,D_323,B_324))
      | ~ m1_subset_1(E_321,A_320)
      | ~ m1_subset_1(D_323,k1_zfmisc_1(k2_zfmisc_1(C_322,A_320)))
      | v1_xboole_0(C_322)
      | v1_xboole_0(B_324)
      | v1_xboole_0(A_320) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_28,plain,(
    ! [C_20,A_18,B_19] :
      ( k1_funct_1(C_20,A_18) = B_19
      | ~ r2_hidden(k4_tarski(A_18,B_19),C_20)
      | ~ v1_funct_1(C_20)
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_5059,plain,(
    ! [A_622,D_619,E_621,C_620,B_618] :
      ( k1_funct_1(D_619,'#skF_3'(A_622,E_621,C_620,D_619,B_618)) = E_621
      | ~ v1_funct_1(D_619)
      | ~ v1_relat_1(D_619)
      | ~ r2_hidden(E_621,k7_relset_1(C_620,A_622,D_619,B_618))
      | ~ m1_subset_1(E_621,A_622)
      | ~ m1_subset_1(D_619,k1_zfmisc_1(k2_zfmisc_1(C_620,A_622)))
      | v1_xboole_0(C_620)
      | v1_xboole_0(B_618)
      | v1_xboole_0(A_622) ) ),
    inference(resolution,[status(thm)],[c_1287,c_28])).

tff(c_5075,plain,(
    ! [E_621,D_218] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_5',E_621,'#skF_4','#skF_7',D_218)) = E_621
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(E_621,k9_relat_1('#skF_7',D_218))
      | ~ m1_subset_1(E_621,'#skF_5')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(D_218)
      | v1_xboole_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_415,c_5059])).

tff(c_5092,plain,(
    ! [E_621,D_218] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_5',E_621,'#skF_4','#skF_7',D_218)) = E_621
      | ~ r2_hidden(E_621,k9_relat_1('#skF_7',D_218))
      | ~ m1_subset_1(E_621,'#skF_5')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(D_218)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_112,c_58,c_5075])).

tff(c_5098,plain,(
    ! [E_623,D_624] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_5',E_623,'#skF_4','#skF_7',D_624)) = E_623
      | ~ r2_hidden(E_623,k9_relat_1('#skF_7',D_624))
      | ~ m1_subset_1(E_623,'#skF_5')
      | v1_xboole_0(D_624) ) ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_183,c_5092])).

tff(c_5139,plain,
    ( k1_funct_1('#skF_7','#skF_3'('#skF_5','#skF_8','#skF_4','#skF_7','#skF_6')) = '#skF_8'
    | ~ m1_subset_1('#skF_8','#skF_5')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_418,c_5098])).

tff(c_5179,plain,
    ( k1_funct_1('#skF_7','#skF_3'('#skF_5','#skF_8','#skF_4','#skF_7','#skF_6')) = '#skF_8'
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_570,c_5139])).

tff(c_5181,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_227,c_2417,c_5179])).

tff(c_5183,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_225])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5198,plain,(
    ! [A_626,B_627,C_628] :
      ( r2_hidden('#skF_2'(A_626,B_627,C_628),B_627)
      | ~ r2_hidden(A_626,k9_relat_1(C_628,B_627))
      | ~ v1_relat_1(C_628) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5217,plain,(
    ! [B_629,A_630,C_631] :
      ( ~ v1_xboole_0(B_629)
      | ~ r2_hidden(A_630,k9_relat_1(C_631,B_629))
      | ~ v1_relat_1(C_631) ) ),
    inference(resolution,[status(thm)],[c_5198,c_2])).

tff(c_5232,plain,(
    ! [B_629,C_631] :
      ( ~ v1_xboole_0(B_629)
      | ~ v1_relat_1(C_631)
      | v1_xboole_0(k9_relat_1(C_631,B_629)) ) ),
    inference(resolution,[status(thm)],[c_4,c_5217])).

tff(c_5369,plain,(
    ! [A_662,B_663,C_664,D_665] :
      ( k7_relset_1(A_662,B_663,C_664,D_665) = k9_relat_1(C_664,D_665)
      | ~ m1_subset_1(C_664,k1_zfmisc_1(k2_zfmisc_1(A_662,B_663))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_5390,plain,(
    ! [D_665] : k7_relset_1('#skF_4','#skF_5','#skF_7',D_665) = k9_relat_1('#skF_7',D_665) ),
    inference(resolution,[status(thm)],[c_54,c_5369])).

tff(c_92,plain,(
    ~ v1_xboole_0(k7_relset_1('#skF_4','#skF_5','#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_52,c_2])).

tff(c_5392,plain,(
    ~ v1_xboole_0(k9_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5390,c_92])).

tff(c_5413,plain,
    ( ~ v1_xboole_0('#skF_6')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_5232,c_5392])).

tff(c_5420,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_5183,c_5413])).

tff(c_5421,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_182])).

tff(c_5642,plain,(
    ! [A_716,B_717,C_718,D_719] :
      ( k7_relset_1(A_716,B_717,C_718,D_719) = k9_relat_1(C_718,D_719)
      | ~ m1_subset_1(C_718,k1_zfmisc_1(k2_zfmisc_1(A_716,B_717))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_5663,plain,(
    ! [D_719] : k7_relset_1('#skF_4','#skF_5','#skF_7',D_719) = k9_relat_1('#skF_7',D_719) ),
    inference(resolution,[status(thm)],[c_54,c_5642])).

tff(c_5666,plain,(
    r2_hidden('#skF_8',k9_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5663,c_52])).

tff(c_5697,plain,(
    ! [A_721,B_722,C_723] :
      ( r2_hidden(k4_tarski('#skF_2'(A_721,B_722,C_723),A_721),C_723)
      | ~ r2_hidden(A_721,k9_relat_1(C_723,B_722))
      | ~ v1_relat_1(C_723) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_5884,plain,(
    ! [C_729,A_730,B_731] :
      ( ~ v1_xboole_0(C_729)
      | ~ r2_hidden(A_730,k9_relat_1(C_729,B_731))
      | ~ v1_relat_1(C_729) ) ),
    inference(resolution,[status(thm)],[c_5697,c_2])).

tff(c_5891,plain,
    ( ~ v1_xboole_0('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_5666,c_5884])).

tff(c_5912,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_5421,c_5891])).

tff(c_5913,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_6162,plain,(
    ! [A_789,B_790,C_791,D_792] :
      ( k7_relset_1(A_789,B_790,C_791,D_792) = k9_relat_1(C_791,D_792)
      | ~ m1_subset_1(C_791,k1_zfmisc_1(k2_zfmisc_1(A_789,B_790))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_6183,plain,(
    ! [D_792] : k7_relset_1('#skF_4','#skF_5','#skF_7',D_792) = k9_relat_1('#skF_7',D_792) ),
    inference(resolution,[status(thm)],[c_54,c_6162])).

tff(c_6186,plain,(
    r2_hidden('#skF_8',k9_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6183,c_52])).

tff(c_6319,plain,(
    ! [A_797,B_798,C_799] :
      ( r2_hidden(k4_tarski('#skF_2'(A_797,B_798,C_799),A_797),C_799)
      | ~ r2_hidden(A_797,k9_relat_1(C_799,B_798))
      | ~ v1_relat_1(C_799) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6411,plain,(
    ! [C_803,A_804,B_805] :
      ( ~ v1_xboole_0(C_803)
      | ~ r2_hidden(A_804,k9_relat_1(C_803,B_805))
      | ~ v1_relat_1(C_803) ) ),
    inference(resolution,[status(thm)],[c_6319,c_2])).

tff(c_6418,plain,
    ( ~ v1_xboole_0('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_6186,c_6411])).

tff(c_6439,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_5913,c_6418])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:02:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.29/2.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.29/2.61  
% 7.29/2.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.29/2.61  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4
% 7.29/2.61  
% 7.29/2.61  %Foreground sorts:
% 7.29/2.61  
% 7.29/2.61  
% 7.29/2.61  %Background operators:
% 7.29/2.61  
% 7.29/2.61  
% 7.29/2.61  %Foreground operators:
% 7.29/2.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.29/2.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.29/2.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.29/2.61  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.29/2.61  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.29/2.61  tff('#skF_7', type, '#skF_7': $i).
% 7.29/2.61  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 7.29/2.61  tff('#skF_5', type, '#skF_5': $i).
% 7.29/2.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.29/2.61  tff('#skF_6', type, '#skF_6': $i).
% 7.29/2.61  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.29/2.61  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.29/2.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.29/2.61  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.29/2.61  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 7.29/2.61  tff('#skF_8', type, '#skF_8': $i).
% 7.29/2.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.29/2.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.29/2.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.29/2.61  tff('#skF_4', type, '#skF_4': $i).
% 7.29/2.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.29/2.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.29/2.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.29/2.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.29/2.61  
% 7.29/2.63  tff(f_146, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_funct_2)).
% 7.29/2.63  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.29/2.63  tff(f_44, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 7.29/2.63  tff(f_101, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 7.29/2.63  tff(f_97, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 7.29/2.63  tff(f_54, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 7.29/2.63  tff(f_93, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 7.29/2.63  tff(f_86, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 7.29/2.63  tff(f_127, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k7_relset_1(C, A, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(F, E), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relset_1)).
% 7.29/2.63  tff(f_75, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 7.29/2.63  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.29/2.63  tff(f_65, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 7.29/2.63  tff(c_54, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.29/2.63  tff(c_98, plain, (![C_149, A_150, B_151]: (v1_relat_1(C_149) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.29/2.63  tff(c_112, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_54, c_98])).
% 7.29/2.63  tff(c_10, plain, (![B_6, A_5]: (m1_subset_1(B_6, A_5) | ~v1_xboole_0(B_6) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.29/2.63  tff(c_8, plain, (![B_6, A_5]: (r2_hidden(B_6, A_5) | ~m1_subset_1(B_6, A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.29/2.63  tff(c_124, plain, (![F_156]: (k1_funct_1('#skF_7', F_156)!='#skF_8' | ~r2_hidden(F_156, '#skF_6') | ~m1_subset_1(F_156, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.29/2.63  tff(c_133, plain, (![B_6]: (k1_funct_1('#skF_7', B_6)!='#skF_8' | ~m1_subset_1(B_6, '#skF_4') | ~m1_subset_1(B_6, '#skF_6') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_8, c_124])).
% 7.29/2.63  tff(c_216, plain, (![B_178]: (k1_funct_1('#skF_7', B_178)!='#skF_8' | ~m1_subset_1(B_178, '#skF_4') | ~m1_subset_1(B_178, '#skF_6'))), inference(splitLeft, [status(thm)], [c_133])).
% 7.29/2.63  tff(c_225, plain, (![B_6]: (k1_funct_1('#skF_7', B_6)!='#skF_8' | ~m1_subset_1(B_6, '#skF_4') | ~v1_xboole_0(B_6) | ~v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_10, c_216])).
% 7.29/2.63  tff(c_227, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_225])).
% 7.29/2.63  tff(c_394, plain, (![A_215, B_216, C_217, D_218]: (k7_relset_1(A_215, B_216, C_217, D_218)=k9_relat_1(C_217, D_218) | ~m1_subset_1(C_217, k1_zfmisc_1(k2_zfmisc_1(A_215, B_216))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.29/2.63  tff(c_415, plain, (![D_218]: (k7_relset_1('#skF_4', '#skF_5', '#skF_7', D_218)=k9_relat_1('#skF_7', D_218))), inference(resolution, [status(thm)], [c_54, c_394])).
% 7.29/2.63  tff(c_52, plain, (r2_hidden('#skF_8', k7_relset_1('#skF_4', '#skF_5', '#skF_7', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.29/2.63  tff(c_418, plain, (r2_hidden('#skF_8', k9_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_415, c_52])).
% 7.29/2.63  tff(c_419, plain, (![D_219]: (k7_relset_1('#skF_4', '#skF_5', '#skF_7', D_219)=k9_relat_1('#skF_7', D_219))), inference(resolution, [status(thm)], [c_54, c_394])).
% 7.29/2.63  tff(c_38, plain, (![A_32, B_33, C_34, D_35]: (m1_subset_1(k7_relset_1(A_32, B_33, C_34, D_35), k1_zfmisc_1(B_33)) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.29/2.63  tff(c_425, plain, (![D_219]: (m1_subset_1(k9_relat_1('#skF_7', D_219), k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_419, c_38])).
% 7.29/2.63  tff(c_481, plain, (![D_220]: (m1_subset_1(k9_relat_1('#skF_7', D_220), k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_425])).
% 7.29/2.63  tff(c_16, plain, (![A_9, C_11, B_10]: (m1_subset_1(A_9, C_11) | ~m1_subset_1(B_10, k1_zfmisc_1(C_11)) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.29/2.63  tff(c_549, plain, (![A_224, D_225]: (m1_subset_1(A_224, '#skF_5') | ~r2_hidden(A_224, k9_relat_1('#skF_7', D_225)))), inference(resolution, [status(thm)], [c_481, c_16])).
% 7.29/2.63  tff(c_570, plain, (m1_subset_1('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_418, c_549])).
% 7.29/2.63  tff(c_135, plain, (![C_157, B_158, A_159]: (v1_xboole_0(C_157) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(B_158, A_159))) | ~v1_xboole_0(A_159))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.29/2.63  tff(c_151, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_54, c_135])).
% 7.29/2.63  tff(c_152, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_151])).
% 7.29/2.63  tff(c_166, plain, (![C_165, A_166, B_167]: (v1_xboole_0(C_165) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))) | ~v1_xboole_0(A_166))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.29/2.63  tff(c_182, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_54, c_166])).
% 7.29/2.63  tff(c_183, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_182])).
% 7.29/2.63  tff(c_1046, plain, (![C_290, B_292, A_288, E_289, D_291]: (r2_hidden('#skF_3'(A_288, E_289, C_290, D_291, B_292), B_292) | ~r2_hidden(E_289, k7_relset_1(C_290, A_288, D_291, B_292)) | ~m1_subset_1(E_289, A_288) | ~m1_subset_1(D_291, k1_zfmisc_1(k2_zfmisc_1(C_290, A_288))) | v1_xboole_0(C_290) | v1_xboole_0(B_292) | v1_xboole_0(A_288))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.29/2.63  tff(c_1063, plain, (![E_289, B_292]: (r2_hidden('#skF_3'('#skF_5', E_289, '#skF_4', '#skF_7', B_292), B_292) | ~r2_hidden(E_289, k7_relset_1('#skF_4', '#skF_5', '#skF_7', B_292)) | ~m1_subset_1(E_289, '#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0(B_292) | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_1046])).
% 7.29/2.63  tff(c_1072, plain, (![E_289, B_292]: (r2_hidden('#skF_3'('#skF_5', E_289, '#skF_4', '#skF_7', B_292), B_292) | ~r2_hidden(E_289, k9_relat_1('#skF_7', B_292)) | ~m1_subset_1(E_289, '#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0(B_292) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_415, c_1063])).
% 7.29/2.63  tff(c_2082, plain, (![E_437, B_438]: (r2_hidden('#skF_3'('#skF_5', E_437, '#skF_4', '#skF_7', B_438), B_438) | ~r2_hidden(E_437, k9_relat_1('#skF_7', B_438)) | ~m1_subset_1(E_437, '#skF_5') | v1_xboole_0(B_438))), inference(negUnitSimplification, [status(thm)], [c_152, c_183, c_1072])).
% 7.29/2.63  tff(c_50, plain, (![F_138]: (k1_funct_1('#skF_7', F_138)!='#skF_8' | ~r2_hidden(F_138, '#skF_6') | ~m1_subset_1(F_138, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.29/2.63  tff(c_2178, plain, (![E_437]: (k1_funct_1('#skF_7', '#skF_3'('#skF_5', E_437, '#skF_4', '#skF_7', '#skF_6'))!='#skF_8' | ~m1_subset_1('#skF_3'('#skF_5', E_437, '#skF_4', '#skF_7', '#skF_6'), '#skF_4') | ~r2_hidden(E_437, k9_relat_1('#skF_7', '#skF_6')) | ~m1_subset_1(E_437, '#skF_5') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_2082, c_50])).
% 7.29/2.63  tff(c_2315, plain, (![E_452]: (k1_funct_1('#skF_7', '#skF_3'('#skF_5', E_452, '#skF_4', '#skF_7', '#skF_6'))!='#skF_8' | ~m1_subset_1('#skF_3'('#skF_5', E_452, '#skF_4', '#skF_7', '#skF_6'), '#skF_4') | ~r2_hidden(E_452, k9_relat_1('#skF_7', '#skF_6')) | ~m1_subset_1(E_452, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_227, c_2178])).
% 7.29/2.63  tff(c_2334, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_5', '#skF_8', '#skF_4', '#skF_7', '#skF_6'))!='#skF_8' | ~m1_subset_1('#skF_3'('#skF_5', '#skF_8', '#skF_4', '#skF_7', '#skF_6'), '#skF_4') | ~m1_subset_1('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_418, c_2315])).
% 7.29/2.63  tff(c_2355, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_5', '#skF_8', '#skF_4', '#skF_7', '#skF_6'))!='#skF_8' | ~m1_subset_1('#skF_3'('#skF_5', '#skF_8', '#skF_4', '#skF_7', '#skF_6'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_570, c_2334])).
% 7.29/2.63  tff(c_2363, plain, (~m1_subset_1('#skF_3'('#skF_5', '#skF_8', '#skF_4', '#skF_7', '#skF_6'), '#skF_4')), inference(splitLeft, [status(thm)], [c_2355])).
% 7.29/2.63  tff(c_902, plain, (![D_264, C_263, E_262, A_261, B_265]: (m1_subset_1('#skF_3'(A_261, E_262, C_263, D_264, B_265), C_263) | ~r2_hidden(E_262, k7_relset_1(C_263, A_261, D_264, B_265)) | ~m1_subset_1(E_262, A_261) | ~m1_subset_1(D_264, k1_zfmisc_1(k2_zfmisc_1(C_263, A_261))) | v1_xboole_0(C_263) | v1_xboole_0(B_265) | v1_xboole_0(A_261))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.29/2.63  tff(c_910, plain, (![E_262, D_218]: (m1_subset_1('#skF_3'('#skF_5', E_262, '#skF_4', '#skF_7', D_218), '#skF_4') | ~r2_hidden(E_262, k9_relat_1('#skF_7', D_218)) | ~m1_subset_1(E_262, '#skF_5') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | v1_xboole_0('#skF_4') | v1_xboole_0(D_218) | v1_xboole_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_415, c_902])).
% 7.29/2.63  tff(c_923, plain, (![E_262, D_218]: (m1_subset_1('#skF_3'('#skF_5', E_262, '#skF_4', '#skF_7', D_218), '#skF_4') | ~r2_hidden(E_262, k9_relat_1('#skF_7', D_218)) | ~m1_subset_1(E_262, '#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0(D_218) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_910])).
% 7.29/2.63  tff(c_2368, plain, (![E_453, D_454]: (m1_subset_1('#skF_3'('#skF_5', E_453, '#skF_4', '#skF_7', D_454), '#skF_4') | ~r2_hidden(E_453, k9_relat_1('#skF_7', D_454)) | ~m1_subset_1(E_453, '#skF_5') | v1_xboole_0(D_454))), inference(negUnitSimplification, [status(thm)], [c_152, c_183, c_923])).
% 7.29/2.63  tff(c_2391, plain, (m1_subset_1('#skF_3'('#skF_5', '#skF_8', '#skF_4', '#skF_7', '#skF_6'), '#skF_4') | ~m1_subset_1('#skF_8', '#skF_5') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_418, c_2368])).
% 7.29/2.63  tff(c_2414, plain, (m1_subset_1('#skF_3'('#skF_5', '#skF_8', '#skF_4', '#skF_7', '#skF_6'), '#skF_4') | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_570, c_2391])).
% 7.29/2.63  tff(c_2416, plain, $false, inference(negUnitSimplification, [status(thm)], [c_227, c_2363, c_2414])).
% 7.29/2.63  tff(c_2417, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_5', '#skF_8', '#skF_4', '#skF_7', '#skF_6'))!='#skF_8'), inference(splitRight, [status(thm)], [c_2355])).
% 7.29/2.63  tff(c_58, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.29/2.63  tff(c_1287, plain, (![C_322, A_320, D_323, B_324, E_321]: (r2_hidden(k4_tarski('#skF_3'(A_320, E_321, C_322, D_323, B_324), E_321), D_323) | ~r2_hidden(E_321, k7_relset_1(C_322, A_320, D_323, B_324)) | ~m1_subset_1(E_321, A_320) | ~m1_subset_1(D_323, k1_zfmisc_1(k2_zfmisc_1(C_322, A_320))) | v1_xboole_0(C_322) | v1_xboole_0(B_324) | v1_xboole_0(A_320))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.29/2.63  tff(c_28, plain, (![C_20, A_18, B_19]: (k1_funct_1(C_20, A_18)=B_19 | ~r2_hidden(k4_tarski(A_18, B_19), C_20) | ~v1_funct_1(C_20) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.29/2.63  tff(c_5059, plain, (![A_622, D_619, E_621, C_620, B_618]: (k1_funct_1(D_619, '#skF_3'(A_622, E_621, C_620, D_619, B_618))=E_621 | ~v1_funct_1(D_619) | ~v1_relat_1(D_619) | ~r2_hidden(E_621, k7_relset_1(C_620, A_622, D_619, B_618)) | ~m1_subset_1(E_621, A_622) | ~m1_subset_1(D_619, k1_zfmisc_1(k2_zfmisc_1(C_620, A_622))) | v1_xboole_0(C_620) | v1_xboole_0(B_618) | v1_xboole_0(A_622))), inference(resolution, [status(thm)], [c_1287, c_28])).
% 7.29/2.63  tff(c_5075, plain, (![E_621, D_218]: (k1_funct_1('#skF_7', '#skF_3'('#skF_5', E_621, '#skF_4', '#skF_7', D_218))=E_621 | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(E_621, k9_relat_1('#skF_7', D_218)) | ~m1_subset_1(E_621, '#skF_5') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | v1_xboole_0('#skF_4') | v1_xboole_0(D_218) | v1_xboole_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_415, c_5059])).
% 7.29/2.63  tff(c_5092, plain, (![E_621, D_218]: (k1_funct_1('#skF_7', '#skF_3'('#skF_5', E_621, '#skF_4', '#skF_7', D_218))=E_621 | ~r2_hidden(E_621, k9_relat_1('#skF_7', D_218)) | ~m1_subset_1(E_621, '#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0(D_218) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_112, c_58, c_5075])).
% 7.29/2.63  tff(c_5098, plain, (![E_623, D_624]: (k1_funct_1('#skF_7', '#skF_3'('#skF_5', E_623, '#skF_4', '#skF_7', D_624))=E_623 | ~r2_hidden(E_623, k9_relat_1('#skF_7', D_624)) | ~m1_subset_1(E_623, '#skF_5') | v1_xboole_0(D_624))), inference(negUnitSimplification, [status(thm)], [c_152, c_183, c_5092])).
% 7.29/2.63  tff(c_5139, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_5', '#skF_8', '#skF_4', '#skF_7', '#skF_6'))='#skF_8' | ~m1_subset_1('#skF_8', '#skF_5') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_418, c_5098])).
% 7.29/2.63  tff(c_5179, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_5', '#skF_8', '#skF_4', '#skF_7', '#skF_6'))='#skF_8' | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_570, c_5139])).
% 7.29/2.63  tff(c_5181, plain, $false, inference(negUnitSimplification, [status(thm)], [c_227, c_2417, c_5179])).
% 7.29/2.63  tff(c_5183, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_225])).
% 7.29/2.63  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.29/2.63  tff(c_5198, plain, (![A_626, B_627, C_628]: (r2_hidden('#skF_2'(A_626, B_627, C_628), B_627) | ~r2_hidden(A_626, k9_relat_1(C_628, B_627)) | ~v1_relat_1(C_628))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.29/2.63  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.29/2.63  tff(c_5217, plain, (![B_629, A_630, C_631]: (~v1_xboole_0(B_629) | ~r2_hidden(A_630, k9_relat_1(C_631, B_629)) | ~v1_relat_1(C_631))), inference(resolution, [status(thm)], [c_5198, c_2])).
% 7.29/2.63  tff(c_5232, plain, (![B_629, C_631]: (~v1_xboole_0(B_629) | ~v1_relat_1(C_631) | v1_xboole_0(k9_relat_1(C_631, B_629)))), inference(resolution, [status(thm)], [c_4, c_5217])).
% 7.29/2.63  tff(c_5369, plain, (![A_662, B_663, C_664, D_665]: (k7_relset_1(A_662, B_663, C_664, D_665)=k9_relat_1(C_664, D_665) | ~m1_subset_1(C_664, k1_zfmisc_1(k2_zfmisc_1(A_662, B_663))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.29/2.63  tff(c_5390, plain, (![D_665]: (k7_relset_1('#skF_4', '#skF_5', '#skF_7', D_665)=k9_relat_1('#skF_7', D_665))), inference(resolution, [status(thm)], [c_54, c_5369])).
% 7.29/2.63  tff(c_92, plain, (~v1_xboole_0(k7_relset_1('#skF_4', '#skF_5', '#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_52, c_2])).
% 7.29/2.63  tff(c_5392, plain, (~v1_xboole_0(k9_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_5390, c_92])).
% 7.29/2.63  tff(c_5413, plain, (~v1_xboole_0('#skF_6') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_5232, c_5392])).
% 7.29/2.63  tff(c_5420, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_5183, c_5413])).
% 7.29/2.63  tff(c_5421, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_182])).
% 7.29/2.63  tff(c_5642, plain, (![A_716, B_717, C_718, D_719]: (k7_relset_1(A_716, B_717, C_718, D_719)=k9_relat_1(C_718, D_719) | ~m1_subset_1(C_718, k1_zfmisc_1(k2_zfmisc_1(A_716, B_717))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.29/2.63  tff(c_5663, plain, (![D_719]: (k7_relset_1('#skF_4', '#skF_5', '#skF_7', D_719)=k9_relat_1('#skF_7', D_719))), inference(resolution, [status(thm)], [c_54, c_5642])).
% 7.29/2.63  tff(c_5666, plain, (r2_hidden('#skF_8', k9_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_5663, c_52])).
% 7.29/2.63  tff(c_5697, plain, (![A_721, B_722, C_723]: (r2_hidden(k4_tarski('#skF_2'(A_721, B_722, C_723), A_721), C_723) | ~r2_hidden(A_721, k9_relat_1(C_723, B_722)) | ~v1_relat_1(C_723))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.29/2.63  tff(c_5884, plain, (![C_729, A_730, B_731]: (~v1_xboole_0(C_729) | ~r2_hidden(A_730, k9_relat_1(C_729, B_731)) | ~v1_relat_1(C_729))), inference(resolution, [status(thm)], [c_5697, c_2])).
% 7.29/2.63  tff(c_5891, plain, (~v1_xboole_0('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_5666, c_5884])).
% 7.29/2.63  tff(c_5912, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_5421, c_5891])).
% 7.29/2.63  tff(c_5913, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_151])).
% 7.29/2.63  tff(c_6162, plain, (![A_789, B_790, C_791, D_792]: (k7_relset_1(A_789, B_790, C_791, D_792)=k9_relat_1(C_791, D_792) | ~m1_subset_1(C_791, k1_zfmisc_1(k2_zfmisc_1(A_789, B_790))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.29/2.63  tff(c_6183, plain, (![D_792]: (k7_relset_1('#skF_4', '#skF_5', '#skF_7', D_792)=k9_relat_1('#skF_7', D_792))), inference(resolution, [status(thm)], [c_54, c_6162])).
% 7.29/2.63  tff(c_6186, plain, (r2_hidden('#skF_8', k9_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_6183, c_52])).
% 7.29/2.63  tff(c_6319, plain, (![A_797, B_798, C_799]: (r2_hidden(k4_tarski('#skF_2'(A_797, B_798, C_799), A_797), C_799) | ~r2_hidden(A_797, k9_relat_1(C_799, B_798)) | ~v1_relat_1(C_799))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.29/2.63  tff(c_6411, plain, (![C_803, A_804, B_805]: (~v1_xboole_0(C_803) | ~r2_hidden(A_804, k9_relat_1(C_803, B_805)) | ~v1_relat_1(C_803))), inference(resolution, [status(thm)], [c_6319, c_2])).
% 7.29/2.63  tff(c_6418, plain, (~v1_xboole_0('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_6186, c_6411])).
% 7.29/2.63  tff(c_6439, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_5913, c_6418])).
% 7.29/2.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.29/2.63  
% 7.29/2.63  Inference rules
% 7.29/2.63  ----------------------
% 7.29/2.63  #Ref     : 0
% 7.29/2.63  #Sup     : 1279
% 7.29/2.63  #Fact    : 0
% 7.29/2.63  #Define  : 0
% 7.29/2.63  #Split   : 37
% 7.29/2.63  #Chain   : 0
% 7.29/2.63  #Close   : 0
% 7.29/2.63  
% 7.29/2.63  Ordering : KBO
% 7.29/2.63  
% 7.29/2.63  Simplification rules
% 7.29/2.63  ----------------------
% 7.29/2.63  #Subsume      : 309
% 7.29/2.63  #Demod        : 350
% 7.29/2.63  #Tautology    : 102
% 7.29/2.63  #SimpNegUnit  : 137
% 7.29/2.63  #BackRed      : 14
% 7.29/2.63  
% 7.29/2.63  #Partial instantiations: 0
% 7.29/2.63  #Strategies tried      : 1
% 7.29/2.63  
% 7.29/2.63  Timing (in seconds)
% 7.29/2.63  ----------------------
% 7.49/2.64  Preprocessing        : 0.36
% 7.49/2.64  Parsing              : 0.19
% 7.49/2.64  CNF conversion       : 0.03
% 7.49/2.64  Main loop            : 1.42
% 7.49/2.64  Inferencing          : 0.45
% 7.49/2.64  Reduction            : 0.38
% 7.49/2.64  Demodulation         : 0.24
% 7.49/2.64  BG Simplification    : 0.05
% 7.49/2.64  Subsumption          : 0.43
% 7.49/2.64  Abstraction          : 0.06
% 7.49/2.64  MUC search           : 0.00
% 7.49/2.64  Cooper               : 0.00
% 7.49/2.64  Total                : 1.82
% 7.49/2.64  Index Insertion      : 0.00
% 7.49/2.64  Index Deletion       : 0.00
% 7.49/2.64  Index Matching       : 0.00
% 7.49/2.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
