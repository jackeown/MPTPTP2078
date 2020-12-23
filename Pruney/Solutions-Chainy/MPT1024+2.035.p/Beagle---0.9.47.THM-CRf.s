%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:26 EST 2020

% Result     : Theorem 7.85s
% Output     : CNFRefutation 8.03s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 121 expanded)
%              Number of leaves         :   35 (  60 expanded)
%              Depth                    :   12
%              Number of atoms          :  141 ( 289 expanded)
%              Number of equality atoms :   11 (  24 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_47,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_93,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ~ ( r2_hidden(F,A)
                    & r2_hidden(F,C)
                    & E = k1_funct_1(D,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(E,k1_relat_1(A))
                  & r2_hidden(E,B)
                  & D = k1_funct_1(A,E) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_14,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_50,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_56,plain,(
    ! [B_69,A_70] :
      ( v1_relat_1(B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_70))
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_59,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_50,c_56])).

tff(c_62,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_59])).

tff(c_54,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_64,plain,(
    ! [A_73,B_74] :
      ( r2_hidden('#skF_1'(A_73,B_74),A_73)
      | r1_tarski(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_69,plain,(
    ! [A_73] : r1_tarski(A_73,A_73) ),
    inference(resolution,[status(thm)],[c_64,c_4])).

tff(c_78,plain,(
    ! [B_79,A_80] :
      ( v4_relat_1(B_79,A_80)
      | ~ r1_tarski(k1_relat_1(B_79),A_80)
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_87,plain,(
    ! [B_79] :
      ( v4_relat_1(B_79,k1_relat_1(B_79))
      | ~ v1_relat_1(B_79) ) ),
    inference(resolution,[status(thm)],[c_69,c_78])).

tff(c_101,plain,(
    ! [C_88,A_89,B_90] :
      ( v4_relat_1(C_88,A_89)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_105,plain,(
    v4_relat_1('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_101])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_relat_1(B_10),A_9)
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_89,plain,(
    ! [C_82,B_83,A_84] :
      ( r2_hidden(C_82,B_83)
      | ~ r2_hidden(C_82,A_84)
      | ~ r1_tarski(A_84,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_113,plain,(
    ! [A_92,B_93,B_94] :
      ( r2_hidden('#skF_1'(A_92,B_93),B_94)
      | ~ r1_tarski(A_92,B_94)
      | r1_tarski(A_92,B_93) ) ),
    inference(resolution,[status(thm)],[c_6,c_89])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_180,plain,(
    ! [A_107,B_108,B_109,B_110] :
      ( r2_hidden('#skF_1'(A_107,B_108),B_109)
      | ~ r1_tarski(B_110,B_109)
      | ~ r1_tarski(A_107,B_110)
      | r1_tarski(A_107,B_108) ) ),
    inference(resolution,[status(thm)],[c_113,c_2])).

tff(c_192,plain,(
    ! [A_116,B_117,A_118,B_119] :
      ( r2_hidden('#skF_1'(A_116,B_117),A_118)
      | ~ r1_tarski(A_116,k1_relat_1(B_119))
      | r1_tarski(A_116,B_117)
      | ~ v4_relat_1(B_119,A_118)
      | ~ v1_relat_1(B_119) ) ),
    inference(resolution,[status(thm)],[c_12,c_180])).

tff(c_304,plain,(
    ! [B_160,B_161,A_162,B_163] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_160),B_161),A_162)
      | r1_tarski(k1_relat_1(B_160),B_161)
      | ~ v4_relat_1(B_163,A_162)
      | ~ v1_relat_1(B_163)
      | ~ v4_relat_1(B_160,k1_relat_1(B_163))
      | ~ v1_relat_1(B_160) ) ),
    inference(resolution,[status(thm)],[c_12,c_192])).

tff(c_306,plain,(
    ! [B_160,B_161] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_160),B_161),'#skF_6')
      | r1_tarski(k1_relat_1(B_160),B_161)
      | ~ v1_relat_1('#skF_9')
      | ~ v4_relat_1(B_160,k1_relat_1('#skF_9'))
      | ~ v1_relat_1(B_160) ) ),
    inference(resolution,[status(thm)],[c_105,c_304])).

tff(c_313,plain,(
    ! [B_164,B_165] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_164),B_165),'#skF_6')
      | r1_tarski(k1_relat_1(B_164),B_165)
      | ~ v4_relat_1(B_164,k1_relat_1('#skF_9'))
      | ~ v1_relat_1(B_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_306])).

tff(c_326,plain,(
    ! [B_166] :
      ( r1_tarski(k1_relat_1(B_166),'#skF_6')
      | ~ v4_relat_1(B_166,k1_relat_1('#skF_9'))
      | ~ v1_relat_1(B_166) ) ),
    inference(resolution,[status(thm)],[c_313,c_4])).

tff(c_330,plain,
    ( r1_tarski(k1_relat_1('#skF_9'),'#skF_6')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_87,c_326])).

tff(c_333,plain,(
    r1_tarski(k1_relat_1('#skF_9'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_330])).

tff(c_18,plain,(
    ! [A_13,B_36,D_51] :
      ( k1_funct_1(A_13,'#skF_5'(A_13,B_36,k9_relat_1(A_13,B_36),D_51)) = D_51
      | ~ r2_hidden(D_51,k9_relat_1(A_13,B_36))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    ! [A_13,B_36,D_51] :
      ( r2_hidden('#skF_5'(A_13,B_36,k9_relat_1(A_13,B_36),D_51),B_36)
      | ~ r2_hidden(D_51,k9_relat_1(A_13,B_36))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_250,plain,(
    ! [A_132,B_133,D_134] :
      ( r2_hidden('#skF_5'(A_132,B_133,k9_relat_1(A_132,B_133),D_134),k1_relat_1(A_132))
      | ~ r2_hidden(D_134,k9_relat_1(A_132,B_133))
      | ~ v1_funct_1(A_132)
      | ~ v1_relat_1(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_622,plain,(
    ! [A_227,B_228,D_229,B_230] :
      ( r2_hidden('#skF_5'(A_227,B_228,k9_relat_1(A_227,B_228),D_229),B_230)
      | ~ r1_tarski(k1_relat_1(A_227),B_230)
      | ~ r2_hidden(D_229,k9_relat_1(A_227,B_228))
      | ~ v1_funct_1(A_227)
      | ~ v1_relat_1(A_227) ) ),
    inference(resolution,[status(thm)],[c_250,c_2])).

tff(c_46,plain,(
    ! [F_66] :
      ( k1_funct_1('#skF_9',F_66) != '#skF_10'
      | ~ r2_hidden(F_66,'#skF_8')
      | ~ r2_hidden(F_66,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2164,plain,(
    ! [A_408,B_409,D_410] :
      ( k1_funct_1('#skF_9','#skF_5'(A_408,B_409,k9_relat_1(A_408,B_409),D_410)) != '#skF_10'
      | ~ r2_hidden('#skF_5'(A_408,B_409,k9_relat_1(A_408,B_409),D_410),'#skF_8')
      | ~ r1_tarski(k1_relat_1(A_408),'#skF_6')
      | ~ r2_hidden(D_410,k9_relat_1(A_408,B_409))
      | ~ v1_funct_1(A_408)
      | ~ v1_relat_1(A_408) ) ),
    inference(resolution,[status(thm)],[c_622,c_46])).

tff(c_2190,plain,(
    ! [A_411,D_412] :
      ( k1_funct_1('#skF_9','#skF_5'(A_411,'#skF_8',k9_relat_1(A_411,'#skF_8'),D_412)) != '#skF_10'
      | ~ r1_tarski(k1_relat_1(A_411),'#skF_6')
      | ~ r2_hidden(D_412,k9_relat_1(A_411,'#skF_8'))
      | ~ v1_funct_1(A_411)
      | ~ v1_relat_1(A_411) ) ),
    inference(resolution,[status(thm)],[c_20,c_2164])).

tff(c_2194,plain,(
    ! [D_51] :
      ( D_51 != '#skF_10'
      | ~ r1_tarski(k1_relat_1('#skF_9'),'#skF_6')
      | ~ r2_hidden(D_51,k9_relat_1('#skF_9','#skF_8'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(D_51,k9_relat_1('#skF_9','#skF_8'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2190])).

tff(c_2197,plain,(
    ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_54,c_62,c_54,c_333,c_2194])).

tff(c_127,plain,(
    ! [A_95,B_96,C_97,D_98] :
      ( k7_relset_1(A_95,B_96,C_97,D_98) = k9_relat_1(C_97,D_98)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_130,plain,(
    ! [D_98] : k7_relset_1('#skF_6','#skF_7','#skF_9',D_98) = k9_relat_1('#skF_9',D_98) ),
    inference(resolution,[status(thm)],[c_50,c_127])).

tff(c_48,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_6','#skF_7','#skF_9','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_132,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_48])).

tff(c_2199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2197,c_132])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:38:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.85/2.98  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.85/2.99  
% 7.85/2.99  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.85/2.99  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3 > #skF_1
% 7.85/2.99  
% 7.85/2.99  %Foreground sorts:
% 7.85/2.99  
% 7.85/2.99  
% 7.85/2.99  %Background operators:
% 7.85/2.99  
% 7.85/2.99  
% 7.85/2.99  %Foreground operators:
% 7.85/2.99  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.85/2.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.85/2.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.85/2.99  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 7.85/2.99  tff('#skF_7', type, '#skF_7': $i).
% 7.85/2.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.85/2.99  tff('#skF_10', type, '#skF_10': $i).
% 7.85/2.99  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 7.85/2.99  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.85/2.99  tff('#skF_6', type, '#skF_6': $i).
% 7.85/2.99  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.85/2.99  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.85/2.99  tff('#skF_9', type, '#skF_9': $i).
% 7.85/2.99  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.85/2.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.85/2.99  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.85/2.99  tff('#skF_8', type, '#skF_8': $i).
% 7.85/2.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.85/2.99  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 7.85/2.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.85/2.99  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.85/2.99  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.85/2.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.85/2.99  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.85/2.99  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.85/2.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.85/2.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.85/2.99  
% 8.03/3.02  tff(f_47, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.03/3.02  tff(f_93, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_funct_2)).
% 8.03/3.02  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.03/3.02  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 8.03/3.02  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 8.03/3.02  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.03/3.02  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_1)).
% 8.03/3.02  tff(f_74, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 8.03/3.02  tff(c_14, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.03/3.02  tff(c_50, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.03/3.02  tff(c_56, plain, (![B_69, A_70]: (v1_relat_1(B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(A_70)) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.03/3.02  tff(c_59, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_50, c_56])).
% 8.03/3.02  tff(c_62, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_59])).
% 8.03/3.02  tff(c_54, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.03/3.02  tff(c_64, plain, (![A_73, B_74]: (r2_hidden('#skF_1'(A_73, B_74), A_73) | r1_tarski(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.03/3.02  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.03/3.02  tff(c_69, plain, (![A_73]: (r1_tarski(A_73, A_73))), inference(resolution, [status(thm)], [c_64, c_4])).
% 8.03/3.02  tff(c_78, plain, (![B_79, A_80]: (v4_relat_1(B_79, A_80) | ~r1_tarski(k1_relat_1(B_79), A_80) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.03/3.02  tff(c_87, plain, (![B_79]: (v4_relat_1(B_79, k1_relat_1(B_79)) | ~v1_relat_1(B_79))), inference(resolution, [status(thm)], [c_69, c_78])).
% 8.03/3.02  tff(c_101, plain, (![C_88, A_89, B_90]: (v4_relat_1(C_88, A_89) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.03/3.02  tff(c_105, plain, (v4_relat_1('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_50, c_101])).
% 8.03/3.02  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k1_relat_1(B_10), A_9) | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.03/3.02  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.03/3.02  tff(c_89, plain, (![C_82, B_83, A_84]: (r2_hidden(C_82, B_83) | ~r2_hidden(C_82, A_84) | ~r1_tarski(A_84, B_83))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.03/3.02  tff(c_113, plain, (![A_92, B_93, B_94]: (r2_hidden('#skF_1'(A_92, B_93), B_94) | ~r1_tarski(A_92, B_94) | r1_tarski(A_92, B_93))), inference(resolution, [status(thm)], [c_6, c_89])).
% 8.03/3.02  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.03/3.02  tff(c_180, plain, (![A_107, B_108, B_109, B_110]: (r2_hidden('#skF_1'(A_107, B_108), B_109) | ~r1_tarski(B_110, B_109) | ~r1_tarski(A_107, B_110) | r1_tarski(A_107, B_108))), inference(resolution, [status(thm)], [c_113, c_2])).
% 8.03/3.02  tff(c_192, plain, (![A_116, B_117, A_118, B_119]: (r2_hidden('#skF_1'(A_116, B_117), A_118) | ~r1_tarski(A_116, k1_relat_1(B_119)) | r1_tarski(A_116, B_117) | ~v4_relat_1(B_119, A_118) | ~v1_relat_1(B_119))), inference(resolution, [status(thm)], [c_12, c_180])).
% 8.03/3.02  tff(c_304, plain, (![B_160, B_161, A_162, B_163]: (r2_hidden('#skF_1'(k1_relat_1(B_160), B_161), A_162) | r1_tarski(k1_relat_1(B_160), B_161) | ~v4_relat_1(B_163, A_162) | ~v1_relat_1(B_163) | ~v4_relat_1(B_160, k1_relat_1(B_163)) | ~v1_relat_1(B_160))), inference(resolution, [status(thm)], [c_12, c_192])).
% 8.03/3.02  tff(c_306, plain, (![B_160, B_161]: (r2_hidden('#skF_1'(k1_relat_1(B_160), B_161), '#skF_6') | r1_tarski(k1_relat_1(B_160), B_161) | ~v1_relat_1('#skF_9') | ~v4_relat_1(B_160, k1_relat_1('#skF_9')) | ~v1_relat_1(B_160))), inference(resolution, [status(thm)], [c_105, c_304])).
% 8.03/3.02  tff(c_313, plain, (![B_164, B_165]: (r2_hidden('#skF_1'(k1_relat_1(B_164), B_165), '#skF_6') | r1_tarski(k1_relat_1(B_164), B_165) | ~v4_relat_1(B_164, k1_relat_1('#skF_9')) | ~v1_relat_1(B_164))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_306])).
% 8.03/3.02  tff(c_326, plain, (![B_166]: (r1_tarski(k1_relat_1(B_166), '#skF_6') | ~v4_relat_1(B_166, k1_relat_1('#skF_9')) | ~v1_relat_1(B_166))), inference(resolution, [status(thm)], [c_313, c_4])).
% 8.03/3.02  tff(c_330, plain, (r1_tarski(k1_relat_1('#skF_9'), '#skF_6') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_87, c_326])).
% 8.03/3.02  tff(c_333, plain, (r1_tarski(k1_relat_1('#skF_9'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_330])).
% 8.03/3.02  tff(c_18, plain, (![A_13, B_36, D_51]: (k1_funct_1(A_13, '#skF_5'(A_13, B_36, k9_relat_1(A_13, B_36), D_51))=D_51 | ~r2_hidden(D_51, k9_relat_1(A_13, B_36)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.03/3.02  tff(c_20, plain, (![A_13, B_36, D_51]: (r2_hidden('#skF_5'(A_13, B_36, k9_relat_1(A_13, B_36), D_51), B_36) | ~r2_hidden(D_51, k9_relat_1(A_13, B_36)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.03/3.02  tff(c_250, plain, (![A_132, B_133, D_134]: (r2_hidden('#skF_5'(A_132, B_133, k9_relat_1(A_132, B_133), D_134), k1_relat_1(A_132)) | ~r2_hidden(D_134, k9_relat_1(A_132, B_133)) | ~v1_funct_1(A_132) | ~v1_relat_1(A_132))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.03/3.02  tff(c_622, plain, (![A_227, B_228, D_229, B_230]: (r2_hidden('#skF_5'(A_227, B_228, k9_relat_1(A_227, B_228), D_229), B_230) | ~r1_tarski(k1_relat_1(A_227), B_230) | ~r2_hidden(D_229, k9_relat_1(A_227, B_228)) | ~v1_funct_1(A_227) | ~v1_relat_1(A_227))), inference(resolution, [status(thm)], [c_250, c_2])).
% 8.03/3.02  tff(c_46, plain, (![F_66]: (k1_funct_1('#skF_9', F_66)!='#skF_10' | ~r2_hidden(F_66, '#skF_8') | ~r2_hidden(F_66, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.03/3.02  tff(c_2164, plain, (![A_408, B_409, D_410]: (k1_funct_1('#skF_9', '#skF_5'(A_408, B_409, k9_relat_1(A_408, B_409), D_410))!='#skF_10' | ~r2_hidden('#skF_5'(A_408, B_409, k9_relat_1(A_408, B_409), D_410), '#skF_8') | ~r1_tarski(k1_relat_1(A_408), '#skF_6') | ~r2_hidden(D_410, k9_relat_1(A_408, B_409)) | ~v1_funct_1(A_408) | ~v1_relat_1(A_408))), inference(resolution, [status(thm)], [c_622, c_46])).
% 8.03/3.02  tff(c_2190, plain, (![A_411, D_412]: (k1_funct_1('#skF_9', '#skF_5'(A_411, '#skF_8', k9_relat_1(A_411, '#skF_8'), D_412))!='#skF_10' | ~r1_tarski(k1_relat_1(A_411), '#skF_6') | ~r2_hidden(D_412, k9_relat_1(A_411, '#skF_8')) | ~v1_funct_1(A_411) | ~v1_relat_1(A_411))), inference(resolution, [status(thm)], [c_20, c_2164])).
% 8.03/3.02  tff(c_2194, plain, (![D_51]: (D_51!='#skF_10' | ~r1_tarski(k1_relat_1('#skF_9'), '#skF_6') | ~r2_hidden(D_51, k9_relat_1('#skF_9', '#skF_8')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(D_51, k9_relat_1('#skF_9', '#skF_8')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_2190])).
% 8.03/3.02  tff(c_2197, plain, (~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_54, c_62, c_54, c_333, c_2194])).
% 8.03/3.02  tff(c_127, plain, (![A_95, B_96, C_97, D_98]: (k7_relset_1(A_95, B_96, C_97, D_98)=k9_relat_1(C_97, D_98) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.03/3.02  tff(c_130, plain, (![D_98]: (k7_relset_1('#skF_6', '#skF_7', '#skF_9', D_98)=k9_relat_1('#skF_9', D_98))), inference(resolution, [status(thm)], [c_50, c_127])).
% 8.03/3.02  tff(c_48, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.03/3.02  tff(c_132, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_48])).
% 8.03/3.02  tff(c_2199, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2197, c_132])).
% 8.03/3.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.03/3.02  
% 8.03/3.02  Inference rules
% 8.03/3.02  ----------------------
% 8.03/3.02  #Ref     : 2
% 8.03/3.02  #Sup     : 503
% 8.03/3.02  #Fact    : 0
% 8.03/3.02  #Define  : 0
% 8.03/3.02  #Split   : 7
% 8.03/3.02  #Chain   : 0
% 8.03/3.02  #Close   : 0
% 8.03/3.02  
% 8.03/3.02  Ordering : KBO
% 8.03/3.02  
% 8.03/3.02  Simplification rules
% 8.03/3.02  ----------------------
% 8.03/3.02  #Subsume      : 132
% 8.03/3.02  #Demod        : 92
% 8.03/3.02  #Tautology    : 24
% 8.03/3.02  #SimpNegUnit  : 1
% 8.03/3.02  #BackRed      : 3
% 8.03/3.02  
% 8.03/3.02  #Partial instantiations: 0
% 8.03/3.02  #Strategies tried      : 1
% 8.03/3.02  
% 8.03/3.02  Timing (in seconds)
% 8.03/3.02  ----------------------
% 8.03/3.02  Preprocessing        : 0.52
% 8.03/3.02  Parsing              : 0.25
% 8.03/3.02  CNF conversion       : 0.05
% 8.03/3.02  Main loop            : 1.56
% 8.03/3.02  Inferencing          : 0.51
% 8.03/3.02  Reduction            : 0.37
% 8.03/3.02  Demodulation         : 0.25
% 8.03/3.02  BG Simplification    : 0.06
% 8.03/3.02  Subsumption          : 0.51
% 8.03/3.02  Abstraction          : 0.07
% 8.03/3.02  MUC search           : 0.00
% 8.03/3.02  Cooper               : 0.00
% 8.03/3.02  Total                : 2.13
% 8.03/3.02  Index Insertion      : 0.00
% 8.03/3.02  Index Deletion       : 0.00
% 8.03/3.02  Index Matching       : 0.00
% 8.03/3.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
