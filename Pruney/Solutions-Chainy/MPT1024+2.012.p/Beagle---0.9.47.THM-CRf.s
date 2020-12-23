%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:23 EST 2020

% Result     : Theorem 6.04s
% Output     : CNFRefutation 6.04s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 109 expanded)
%              Number of leaves         :   34 (  56 expanded)
%              Depth                    :   12
%              Number of atoms          :  135 ( 265 expanded)
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

tff(f_88,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_55,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_53,plain,(
    ! [C_65,A_66,B_67] :
      ( v1_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_57,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_48,c_53])).

tff(c_52,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_59,plain,(
    ! [A_70,B_71] :
      ( ~ r2_hidden('#skF_1'(A_70,B_71),B_71)
      | r1_tarski(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_64,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_59])).

tff(c_84,plain,(
    ! [B_80,A_81] :
      ( v4_relat_1(B_80,A_81)
      | ~ r1_tarski(k1_relat_1(B_80),A_81)
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_89,plain,(
    ! [B_80] :
      ( v4_relat_1(B_80,k1_relat_1(B_80))
      | ~ v1_relat_1(B_80) ) ),
    inference(resolution,[status(thm)],[c_64,c_84])).

tff(c_96,plain,(
    ! [C_85,A_86,B_87] :
      ( v4_relat_1(C_85,A_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_100,plain,(
    v4_relat_1('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_96])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_72,plain,(
    ! [C_74,B_75,A_76] :
      ( r2_hidden(C_74,B_75)
      | ~ r2_hidden(C_74,A_76)
      | ~ r1_tarski(A_76,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_109,plain,(
    ! [A_90,B_91,B_92] :
      ( r2_hidden('#skF_1'(A_90,B_91),B_92)
      | ~ r1_tarski(A_90,B_92)
      | r1_tarski(A_90,B_91) ) ),
    inference(resolution,[status(thm)],[c_6,c_72])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_175,plain,(
    ! [A_104,B_105,B_106,B_107] :
      ( r2_hidden('#skF_1'(A_104,B_105),B_106)
      | ~ r1_tarski(B_107,B_106)
      | ~ r1_tarski(A_104,B_107)
      | r1_tarski(A_104,B_105) ) ),
    inference(resolution,[status(thm)],[c_109,c_2])).

tff(c_183,plain,(
    ! [A_110,B_111,A_112,B_113] :
      ( r2_hidden('#skF_1'(A_110,B_111),A_112)
      | ~ r1_tarski(A_110,k1_relat_1(B_113))
      | r1_tarski(A_110,B_111)
      | ~ v4_relat_1(B_113,A_112)
      | ~ v1_relat_1(B_113) ) ),
    inference(resolution,[status(thm)],[c_10,c_175])).

tff(c_299,plain,(
    ! [B_157,B_158,A_159,B_160] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_157),B_158),A_159)
      | r1_tarski(k1_relat_1(B_157),B_158)
      | ~ v4_relat_1(B_160,A_159)
      | ~ v1_relat_1(B_160)
      | ~ v4_relat_1(B_157,k1_relat_1(B_160))
      | ~ v1_relat_1(B_157) ) ),
    inference(resolution,[status(thm)],[c_10,c_183])).

tff(c_301,plain,(
    ! [B_157,B_158] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_157),B_158),'#skF_6')
      | r1_tarski(k1_relat_1(B_157),B_158)
      | ~ v1_relat_1('#skF_9')
      | ~ v4_relat_1(B_157,k1_relat_1('#skF_9'))
      | ~ v1_relat_1(B_157) ) ),
    inference(resolution,[status(thm)],[c_100,c_299])).

tff(c_308,plain,(
    ! [B_161,B_162] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_161),B_162),'#skF_6')
      | r1_tarski(k1_relat_1(B_161),B_162)
      | ~ v4_relat_1(B_161,k1_relat_1('#skF_9'))
      | ~ v1_relat_1(B_161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_301])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_321,plain,(
    ! [B_163] :
      ( r1_tarski(k1_relat_1(B_163),'#skF_6')
      | ~ v4_relat_1(B_163,k1_relat_1('#skF_9'))
      | ~ v1_relat_1(B_163) ) ),
    inference(resolution,[status(thm)],[c_308,c_4])).

tff(c_325,plain,
    ( r1_tarski(k1_relat_1('#skF_9'),'#skF_6')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_89,c_321])).

tff(c_328,plain,(
    r1_tarski(k1_relat_1('#skF_9'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_325])).

tff(c_14,plain,(
    ! [A_8,B_31,D_46] :
      ( k1_funct_1(A_8,'#skF_5'(A_8,B_31,k9_relat_1(A_8,B_31),D_46)) = D_46
      | ~ r2_hidden(D_46,k9_relat_1(A_8,B_31))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16,plain,(
    ! [A_8,B_31,D_46] :
      ( r2_hidden('#skF_5'(A_8,B_31,k9_relat_1(A_8,B_31),D_46),B_31)
      | ~ r2_hidden(D_46,k9_relat_1(A_8,B_31))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_245,plain,(
    ! [A_129,B_130,D_131] :
      ( r2_hidden('#skF_5'(A_129,B_130,k9_relat_1(A_129,B_130),D_131),k1_relat_1(A_129))
      | ~ r2_hidden(D_131,k9_relat_1(A_129,B_130))
      | ~ v1_funct_1(A_129)
      | ~ v1_relat_1(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_612,plain,(
    ! [A_220,B_221,D_222,B_223] :
      ( r2_hidden('#skF_5'(A_220,B_221,k9_relat_1(A_220,B_221),D_222),B_223)
      | ~ r1_tarski(k1_relat_1(A_220),B_223)
      | ~ r2_hidden(D_222,k9_relat_1(A_220,B_221))
      | ~ v1_funct_1(A_220)
      | ~ v1_relat_1(A_220) ) ),
    inference(resolution,[status(thm)],[c_245,c_2])).

tff(c_44,plain,(
    ! [F_64] :
      ( k1_funct_1('#skF_9',F_64) != '#skF_10'
      | ~ r2_hidden(F_64,'#skF_8')
      | ~ r2_hidden(F_64,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2958,plain,(
    ! [A_507,B_508,D_509] :
      ( k1_funct_1('#skF_9','#skF_5'(A_507,B_508,k9_relat_1(A_507,B_508),D_509)) != '#skF_10'
      | ~ r2_hidden('#skF_5'(A_507,B_508,k9_relat_1(A_507,B_508),D_509),'#skF_8')
      | ~ r1_tarski(k1_relat_1(A_507),'#skF_6')
      | ~ r2_hidden(D_509,k9_relat_1(A_507,B_508))
      | ~ v1_funct_1(A_507)
      | ~ v1_relat_1(A_507) ) ),
    inference(resolution,[status(thm)],[c_612,c_44])).

tff(c_2984,plain,(
    ! [A_510,D_511] :
      ( k1_funct_1('#skF_9','#skF_5'(A_510,'#skF_8',k9_relat_1(A_510,'#skF_8'),D_511)) != '#skF_10'
      | ~ r1_tarski(k1_relat_1(A_510),'#skF_6')
      | ~ r2_hidden(D_511,k9_relat_1(A_510,'#skF_8'))
      | ~ v1_funct_1(A_510)
      | ~ v1_relat_1(A_510) ) ),
    inference(resolution,[status(thm)],[c_16,c_2958])).

tff(c_2988,plain,(
    ! [D_46] :
      ( D_46 != '#skF_10'
      | ~ r1_tarski(k1_relat_1('#skF_9'),'#skF_6')
      | ~ r2_hidden(D_46,k9_relat_1('#skF_9','#skF_8'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(D_46,k9_relat_1('#skF_9','#skF_8'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_2984])).

tff(c_2991,plain,(
    ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_52,c_57,c_52,c_328,c_2988])).

tff(c_129,plain,(
    ! [A_93,B_94,C_95,D_96] :
      ( k7_relset_1(A_93,B_94,C_95,D_96) = k9_relat_1(C_95,D_96)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_132,plain,(
    ! [D_96] : k7_relset_1('#skF_6','#skF_7','#skF_9',D_96) = k9_relat_1('#skF_9',D_96) ),
    inference(resolution,[status(thm)],[c_48,c_129])).

tff(c_46,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_6','#skF_7','#skF_9','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_134,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_46])).

tff(c_2993,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2991,c_134])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:41:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.04/2.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.04/2.18  
% 6.04/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.04/2.18  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3 > #skF_1
% 6.04/2.18  
% 6.04/2.18  %Foreground sorts:
% 6.04/2.18  
% 6.04/2.18  
% 6.04/2.18  %Background operators:
% 6.04/2.18  
% 6.04/2.18  
% 6.04/2.18  %Foreground operators:
% 6.04/2.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.04/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.04/2.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.04/2.18  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 6.04/2.18  tff('#skF_7', type, '#skF_7': $i).
% 6.04/2.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.04/2.18  tff('#skF_10', type, '#skF_10': $i).
% 6.04/2.18  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 6.04/2.18  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.04/2.18  tff('#skF_6', type, '#skF_6': $i).
% 6.04/2.18  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.04/2.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.04/2.18  tff('#skF_9', type, '#skF_9': $i).
% 6.04/2.18  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.04/2.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.04/2.18  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.04/2.18  tff('#skF_8', type, '#skF_8': $i).
% 6.04/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.04/2.18  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 6.04/2.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.04/2.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.04/2.18  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.04/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.04/2.18  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.04/2.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.04/2.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.04/2.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.04/2.18  
% 6.04/2.20  tff(f_88, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_funct_2)).
% 6.04/2.20  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.04/2.20  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.04/2.20  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 6.04/2.20  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.04/2.20  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 6.04/2.20  tff(f_69, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 6.04/2.20  tff(c_48, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.04/2.20  tff(c_53, plain, (![C_65, A_66, B_67]: (v1_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.04/2.20  tff(c_57, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_48, c_53])).
% 6.04/2.20  tff(c_52, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.04/2.20  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.04/2.20  tff(c_59, plain, (![A_70, B_71]: (~r2_hidden('#skF_1'(A_70, B_71), B_71) | r1_tarski(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.04/2.20  tff(c_64, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_59])).
% 6.04/2.20  tff(c_84, plain, (![B_80, A_81]: (v4_relat_1(B_80, A_81) | ~r1_tarski(k1_relat_1(B_80), A_81) | ~v1_relat_1(B_80))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.04/2.20  tff(c_89, plain, (![B_80]: (v4_relat_1(B_80, k1_relat_1(B_80)) | ~v1_relat_1(B_80))), inference(resolution, [status(thm)], [c_64, c_84])).
% 6.04/2.20  tff(c_96, plain, (![C_85, A_86, B_87]: (v4_relat_1(C_85, A_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.04/2.20  tff(c_100, plain, (v4_relat_1('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_48, c_96])).
% 6.04/2.20  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.04/2.20  tff(c_72, plain, (![C_74, B_75, A_76]: (r2_hidden(C_74, B_75) | ~r2_hidden(C_74, A_76) | ~r1_tarski(A_76, B_75))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.04/2.20  tff(c_109, plain, (![A_90, B_91, B_92]: (r2_hidden('#skF_1'(A_90, B_91), B_92) | ~r1_tarski(A_90, B_92) | r1_tarski(A_90, B_91))), inference(resolution, [status(thm)], [c_6, c_72])).
% 6.04/2.20  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.04/2.20  tff(c_175, plain, (![A_104, B_105, B_106, B_107]: (r2_hidden('#skF_1'(A_104, B_105), B_106) | ~r1_tarski(B_107, B_106) | ~r1_tarski(A_104, B_107) | r1_tarski(A_104, B_105))), inference(resolution, [status(thm)], [c_109, c_2])).
% 6.04/2.20  tff(c_183, plain, (![A_110, B_111, A_112, B_113]: (r2_hidden('#skF_1'(A_110, B_111), A_112) | ~r1_tarski(A_110, k1_relat_1(B_113)) | r1_tarski(A_110, B_111) | ~v4_relat_1(B_113, A_112) | ~v1_relat_1(B_113))), inference(resolution, [status(thm)], [c_10, c_175])).
% 6.04/2.20  tff(c_299, plain, (![B_157, B_158, A_159, B_160]: (r2_hidden('#skF_1'(k1_relat_1(B_157), B_158), A_159) | r1_tarski(k1_relat_1(B_157), B_158) | ~v4_relat_1(B_160, A_159) | ~v1_relat_1(B_160) | ~v4_relat_1(B_157, k1_relat_1(B_160)) | ~v1_relat_1(B_157))), inference(resolution, [status(thm)], [c_10, c_183])).
% 6.04/2.20  tff(c_301, plain, (![B_157, B_158]: (r2_hidden('#skF_1'(k1_relat_1(B_157), B_158), '#skF_6') | r1_tarski(k1_relat_1(B_157), B_158) | ~v1_relat_1('#skF_9') | ~v4_relat_1(B_157, k1_relat_1('#skF_9')) | ~v1_relat_1(B_157))), inference(resolution, [status(thm)], [c_100, c_299])).
% 6.04/2.20  tff(c_308, plain, (![B_161, B_162]: (r2_hidden('#skF_1'(k1_relat_1(B_161), B_162), '#skF_6') | r1_tarski(k1_relat_1(B_161), B_162) | ~v4_relat_1(B_161, k1_relat_1('#skF_9')) | ~v1_relat_1(B_161))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_301])).
% 6.04/2.20  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.04/2.20  tff(c_321, plain, (![B_163]: (r1_tarski(k1_relat_1(B_163), '#skF_6') | ~v4_relat_1(B_163, k1_relat_1('#skF_9')) | ~v1_relat_1(B_163))), inference(resolution, [status(thm)], [c_308, c_4])).
% 6.04/2.20  tff(c_325, plain, (r1_tarski(k1_relat_1('#skF_9'), '#skF_6') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_89, c_321])).
% 6.04/2.20  tff(c_328, plain, (r1_tarski(k1_relat_1('#skF_9'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_325])).
% 6.04/2.20  tff(c_14, plain, (![A_8, B_31, D_46]: (k1_funct_1(A_8, '#skF_5'(A_8, B_31, k9_relat_1(A_8, B_31), D_46))=D_46 | ~r2_hidden(D_46, k9_relat_1(A_8, B_31)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.04/2.20  tff(c_16, plain, (![A_8, B_31, D_46]: (r2_hidden('#skF_5'(A_8, B_31, k9_relat_1(A_8, B_31), D_46), B_31) | ~r2_hidden(D_46, k9_relat_1(A_8, B_31)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.04/2.20  tff(c_245, plain, (![A_129, B_130, D_131]: (r2_hidden('#skF_5'(A_129, B_130, k9_relat_1(A_129, B_130), D_131), k1_relat_1(A_129)) | ~r2_hidden(D_131, k9_relat_1(A_129, B_130)) | ~v1_funct_1(A_129) | ~v1_relat_1(A_129))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.04/2.20  tff(c_612, plain, (![A_220, B_221, D_222, B_223]: (r2_hidden('#skF_5'(A_220, B_221, k9_relat_1(A_220, B_221), D_222), B_223) | ~r1_tarski(k1_relat_1(A_220), B_223) | ~r2_hidden(D_222, k9_relat_1(A_220, B_221)) | ~v1_funct_1(A_220) | ~v1_relat_1(A_220))), inference(resolution, [status(thm)], [c_245, c_2])).
% 6.04/2.20  tff(c_44, plain, (![F_64]: (k1_funct_1('#skF_9', F_64)!='#skF_10' | ~r2_hidden(F_64, '#skF_8') | ~r2_hidden(F_64, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.04/2.20  tff(c_2958, plain, (![A_507, B_508, D_509]: (k1_funct_1('#skF_9', '#skF_5'(A_507, B_508, k9_relat_1(A_507, B_508), D_509))!='#skF_10' | ~r2_hidden('#skF_5'(A_507, B_508, k9_relat_1(A_507, B_508), D_509), '#skF_8') | ~r1_tarski(k1_relat_1(A_507), '#skF_6') | ~r2_hidden(D_509, k9_relat_1(A_507, B_508)) | ~v1_funct_1(A_507) | ~v1_relat_1(A_507))), inference(resolution, [status(thm)], [c_612, c_44])).
% 6.04/2.20  tff(c_2984, plain, (![A_510, D_511]: (k1_funct_1('#skF_9', '#skF_5'(A_510, '#skF_8', k9_relat_1(A_510, '#skF_8'), D_511))!='#skF_10' | ~r1_tarski(k1_relat_1(A_510), '#skF_6') | ~r2_hidden(D_511, k9_relat_1(A_510, '#skF_8')) | ~v1_funct_1(A_510) | ~v1_relat_1(A_510))), inference(resolution, [status(thm)], [c_16, c_2958])).
% 6.04/2.20  tff(c_2988, plain, (![D_46]: (D_46!='#skF_10' | ~r1_tarski(k1_relat_1('#skF_9'), '#skF_6') | ~r2_hidden(D_46, k9_relat_1('#skF_9', '#skF_8')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(D_46, k9_relat_1('#skF_9', '#skF_8')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_2984])).
% 6.04/2.20  tff(c_2991, plain, (~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_52, c_57, c_52, c_328, c_2988])).
% 6.04/2.20  tff(c_129, plain, (![A_93, B_94, C_95, D_96]: (k7_relset_1(A_93, B_94, C_95, D_96)=k9_relat_1(C_95, D_96) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.04/2.20  tff(c_132, plain, (![D_96]: (k7_relset_1('#skF_6', '#skF_7', '#skF_9', D_96)=k9_relat_1('#skF_9', D_96))), inference(resolution, [status(thm)], [c_48, c_129])).
% 6.04/2.20  tff(c_46, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.04/2.20  tff(c_134, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_46])).
% 6.04/2.20  tff(c_2993, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2991, c_134])).
% 6.04/2.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.04/2.20  
% 6.04/2.20  Inference rules
% 6.04/2.20  ----------------------
% 6.04/2.20  #Ref     : 3
% 6.04/2.20  #Sup     : 659
% 6.04/2.20  #Fact    : 0
% 6.04/2.20  #Define  : 0
% 6.04/2.20  #Split   : 7
% 6.04/2.20  #Chain   : 0
% 6.04/2.20  #Close   : 0
% 6.04/2.20  
% 6.04/2.20  Ordering : KBO
% 6.04/2.20  
% 6.04/2.20  Simplification rules
% 6.04/2.20  ----------------------
% 6.04/2.20  #Subsume      : 207
% 6.04/2.20  #Demod        : 202
% 6.04/2.20  #Tautology    : 24
% 6.04/2.20  #SimpNegUnit  : 1
% 6.04/2.20  #BackRed      : 3
% 6.04/2.20  
% 6.04/2.20  #Partial instantiations: 0
% 6.04/2.20  #Strategies tried      : 1
% 6.04/2.20  
% 6.04/2.20  Timing (in seconds)
% 6.04/2.20  ----------------------
% 6.04/2.20  Preprocessing        : 0.33
% 6.04/2.20  Parsing              : 0.17
% 6.04/2.20  CNF conversion       : 0.03
% 6.04/2.20  Main loop            : 1.11
% 6.04/2.20  Inferencing          : 0.37
% 6.04/2.20  Reduction            : 0.27
% 6.04/2.20  Demodulation         : 0.18
% 6.04/2.20  BG Simplification    : 0.04
% 6.04/2.20  Subsumption          : 0.38
% 6.04/2.20  Abstraction          : 0.05
% 6.04/2.20  MUC search           : 0.00
% 6.04/2.20  Cooper               : 0.00
% 6.04/2.20  Total                : 1.47
% 6.04/2.20  Index Insertion      : 0.00
% 6.04/2.20  Index Deletion       : 0.00
% 6.04/2.20  Index Matching       : 0.00
% 6.04/2.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
