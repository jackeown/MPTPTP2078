%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:07 EST 2020

% Result     : Theorem 10.82s
% Output     : CNFRefutation 11.05s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 124 expanded)
%              Number of leaves         :   49 (  65 expanded)
%              Depth                    :   10
%              Number of atoms          :  140 ( 232 expanded)
%              Number of equality atoms :   35 (  70 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_1 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_133,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_122,axiom,(
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

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_85,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_44,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_90,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_84,plain,(
    k1_funct_1('#skF_11','#skF_10') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_88,plain,(
    m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_8',k1_tarski('#skF_9')))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_250,plain,(
    ! [C_120,B_121,A_122] :
      ( v5_relat_1(C_120,B_121)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_122,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_259,plain,(
    v5_relat_1('#skF_11',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_88,c_250])).

tff(c_86,plain,(
    r2_hidden('#skF_10','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_203,plain,(
    ! [C_110,A_111,B_112] :
      ( v1_relat_1(C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_212,plain,(
    v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_88,c_203])).

tff(c_92,plain,(
    v1_funct_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_90,plain,(
    v1_funct_2('#skF_11','#skF_8',k1_tarski('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_434,plain,(
    ! [A_168,B_169,C_170] :
      ( k1_relset_1(A_168,B_169,C_170) = k1_relat_1(C_170)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(A_168,B_169))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_443,plain,(
    k1_relset_1('#skF_8',k1_tarski('#skF_9'),'#skF_11') = k1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_88,c_434])).

tff(c_1122,plain,(
    ! [B_244,A_245,C_246] :
      ( k1_xboole_0 = B_244
      | k1_relset_1(A_245,B_244,C_246) = A_245
      | ~ v1_funct_2(C_246,A_245,B_244)
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(A_245,B_244))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1133,plain,
    ( k1_tarski('#skF_9') = k1_xboole_0
    | k1_relset_1('#skF_8',k1_tarski('#skF_9'),'#skF_11') = '#skF_8'
    | ~ v1_funct_2('#skF_11','#skF_8',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_88,c_1122])).

tff(c_1138,plain,
    ( k1_tarski('#skF_9') = k1_xboole_0
    | k1_relat_1('#skF_11') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_443,c_1133])).

tff(c_1139,plain,(
    k1_relat_1('#skF_11') = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1138])).

tff(c_42,plain,(
    ! [B_26,A_25] :
      ( r1_tarski(k2_relat_1(B_26),A_25)
      | ~ v5_relat_1(B_26,A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_608,plain,(
    ! [A_183,D_184] :
      ( r2_hidden(k1_funct_1(A_183,D_184),k2_relat_1(A_183))
      | ~ r2_hidden(D_184,k1_relat_1(A_183))
      | ~ v1_funct_1(A_183)
      | ~ v1_relat_1(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_36,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(A_20,k1_zfmisc_1(B_21))
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_385,plain,(
    ! [A_147,C_148,B_149] :
      ( m1_subset_1(A_147,C_148)
      | ~ m1_subset_1(B_149,k1_zfmisc_1(C_148))
      | ~ r2_hidden(A_147,B_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_390,plain,(
    ! [A_147,B_21,A_20] :
      ( m1_subset_1(A_147,B_21)
      | ~ r2_hidden(A_147,A_20)
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(resolution,[status(thm)],[c_36,c_385])).

tff(c_19212,plain,(
    ! [A_77122,D_77123,B_77124] :
      ( m1_subset_1(k1_funct_1(A_77122,D_77123),B_77124)
      | ~ r1_tarski(k2_relat_1(A_77122),B_77124)
      | ~ r2_hidden(D_77123,k1_relat_1(A_77122))
      | ~ v1_funct_1(A_77122)
      | ~ v1_relat_1(A_77122) ) ),
    inference(resolution,[status(thm)],[c_608,c_390])).

tff(c_19222,plain,(
    ! [B_77305,D_77306,A_77307] :
      ( m1_subset_1(k1_funct_1(B_77305,D_77306),A_77307)
      | ~ r2_hidden(D_77306,k1_relat_1(B_77305))
      | ~ v1_funct_1(B_77305)
      | ~ v5_relat_1(B_77305,A_77307)
      | ~ v1_relat_1(B_77305) ) ),
    inference(resolution,[status(thm)],[c_42,c_19212])).

tff(c_19251,plain,(
    ! [D_77306,A_77307] :
      ( m1_subset_1(k1_funct_1('#skF_11',D_77306),A_77307)
      | ~ r2_hidden(D_77306,'#skF_8')
      | ~ v1_funct_1('#skF_11')
      | ~ v5_relat_1('#skF_11',A_77307)
      | ~ v1_relat_1('#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1139,c_19222])).

tff(c_19277,plain,(
    ! [D_77488,A_77489] :
      ( m1_subset_1(k1_funct_1('#skF_11',D_77488),A_77489)
      | ~ r2_hidden(D_77488,'#skF_8')
      | ~ v5_relat_1('#skF_11',A_77489) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_92,c_19251])).

tff(c_26,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_108,plain,(
    ! [D_85,A_86] : r2_hidden(D_85,k2_tarski(A_86,D_85)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_116,plain,(
    ! [A_87,D_88] : ~ v1_xboole_0(k2_tarski(A_87,D_88)) ),
    inference(resolution,[status(thm)],[c_108,c_2])).

tff(c_118,plain,(
    ! [A_12] : ~ v1_xboole_0(k1_tarski(A_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_116])).

tff(c_32,plain,(
    ! [A_18,B_19] :
      ( r2_hidden(A_18,B_19)
      | v1_xboole_0(B_19)
      | ~ m1_subset_1(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_313,plain,(
    ! [D_137,B_138,A_139] :
      ( D_137 = B_138
      | D_137 = A_139
      | ~ r2_hidden(D_137,k2_tarski(A_139,B_138)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_346,plain,(
    ! [D_142,A_143] :
      ( D_142 = A_143
      | D_142 = A_143
      | ~ r2_hidden(D_142,k1_tarski(A_143)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_313])).

tff(c_350,plain,(
    ! [A_18,A_143] :
      ( A_18 = A_143
      | v1_xboole_0(k1_tarski(A_143))
      | ~ m1_subset_1(A_18,k1_tarski(A_143)) ) ),
    inference(resolution,[status(thm)],[c_32,c_346])).

tff(c_360,plain,(
    ! [A_18,A_143] :
      ( A_18 = A_143
      | ~ m1_subset_1(A_18,k1_tarski(A_143)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_350])).

tff(c_19377,plain,(
    ! [D_77670,A_77671] :
      ( k1_funct_1('#skF_11',D_77670) = A_77671
      | ~ r2_hidden(D_77670,'#skF_8')
      | ~ v5_relat_1('#skF_11',k1_tarski(A_77671)) ) ),
    inference(resolution,[status(thm)],[c_19277,c_360])).

tff(c_19451,plain,(
    ! [A_77852] :
      ( k1_funct_1('#skF_11','#skF_10') = A_77852
      | ~ v5_relat_1('#skF_11',k1_tarski(A_77852)) ) ),
    inference(resolution,[status(thm)],[c_86,c_19377])).

tff(c_19462,plain,(
    k1_funct_1('#skF_11','#skF_10') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_259,c_19451])).

tff(c_19466,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_19462])).

tff(c_19467,plain,(
    k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1138])).

tff(c_114,plain,(
    ! [A_12] : r2_hidden(A_12,k1_tarski(A_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_108])).

tff(c_134,plain,(
    ! [B_93,A_94] :
      ( ~ r1_tarski(B_93,A_94)
      | ~ r2_hidden(A_94,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_148,plain,(
    ! [A_12] : ~ r1_tarski(k1_tarski(A_12),A_12) ),
    inference(resolution,[status(thm)],[c_114,c_134])).

tff(c_19497,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_19467,c_148])).

tff(c_19511,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_19497])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:05:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.82/4.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.82/4.03  
% 10.82/4.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.82/4.03  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_1 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 10.82/4.03  
% 10.82/4.03  %Foreground sorts:
% 10.82/4.03  
% 10.82/4.03  
% 10.82/4.03  %Background operators:
% 10.82/4.03  
% 10.82/4.03  
% 10.82/4.03  %Foreground operators:
% 10.82/4.03  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 10.82/4.03  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.82/4.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.82/4.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.82/4.03  tff('#skF_11', type, '#skF_11': $i).
% 10.82/4.03  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.82/4.03  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.82/4.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.82/4.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.82/4.03  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.82/4.03  tff('#skF_10', type, '#skF_10': $i).
% 10.82/4.03  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.82/4.03  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.82/4.03  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.82/4.03  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.82/4.03  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.82/4.03  tff('#skF_9', type, '#skF_9': $i).
% 10.82/4.03  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 10.82/4.03  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.82/4.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.82/4.03  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 10.82/4.03  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 10.82/4.03  tff('#skF_8', type, '#skF_8': $i).
% 10.82/4.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.82/4.03  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.82/4.03  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.82/4.03  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 10.82/4.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.82/4.03  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.82/4.03  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.82/4.03  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 10.82/4.03  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.82/4.03  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 10.82/4.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.82/4.03  
% 11.05/4.05  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 11.05/4.05  tff(f_133, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 11.05/4.05  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 11.05/4.05  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 11.05/4.05  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.05/4.05  tff(f_122, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 11.05/4.05  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 11.05/4.05  tff(f_85, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 11.05/4.05  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 11.05/4.05  tff(f_64, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 11.05/4.05  tff(f_44, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 11.05/4.05  tff(f_42, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 11.05/4.05  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 11.05/4.05  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 11.05/4.05  tff(f_90, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 11.05/4.05  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.05/4.05  tff(c_84, plain, (k1_funct_1('#skF_11', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_133])).
% 11.05/4.05  tff(c_88, plain, (m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_8', k1_tarski('#skF_9'))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 11.05/4.05  tff(c_250, plain, (![C_120, B_121, A_122]: (v5_relat_1(C_120, B_121) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_122, B_121))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.05/4.05  tff(c_259, plain, (v5_relat_1('#skF_11', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_88, c_250])).
% 11.05/4.05  tff(c_86, plain, (r2_hidden('#skF_10', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_133])).
% 11.05/4.05  tff(c_203, plain, (![C_110, A_111, B_112]: (v1_relat_1(C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 11.05/4.05  tff(c_212, plain, (v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_88, c_203])).
% 11.05/4.05  tff(c_92, plain, (v1_funct_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_133])).
% 11.05/4.05  tff(c_90, plain, (v1_funct_2('#skF_11', '#skF_8', k1_tarski('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 11.05/4.05  tff(c_434, plain, (![A_168, B_169, C_170]: (k1_relset_1(A_168, B_169, C_170)=k1_relat_1(C_170) | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(A_168, B_169))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.05/4.05  tff(c_443, plain, (k1_relset_1('#skF_8', k1_tarski('#skF_9'), '#skF_11')=k1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_88, c_434])).
% 11.05/4.05  tff(c_1122, plain, (![B_244, A_245, C_246]: (k1_xboole_0=B_244 | k1_relset_1(A_245, B_244, C_246)=A_245 | ~v1_funct_2(C_246, A_245, B_244) | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1(A_245, B_244))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 11.05/4.05  tff(c_1133, plain, (k1_tarski('#skF_9')=k1_xboole_0 | k1_relset_1('#skF_8', k1_tarski('#skF_9'), '#skF_11')='#skF_8' | ~v1_funct_2('#skF_11', '#skF_8', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_88, c_1122])).
% 11.05/4.05  tff(c_1138, plain, (k1_tarski('#skF_9')=k1_xboole_0 | k1_relat_1('#skF_11')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_443, c_1133])).
% 11.05/4.05  tff(c_1139, plain, (k1_relat_1('#skF_11')='#skF_8'), inference(splitLeft, [status(thm)], [c_1138])).
% 11.05/4.05  tff(c_42, plain, (![B_26, A_25]: (r1_tarski(k2_relat_1(B_26), A_25) | ~v5_relat_1(B_26, A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_70])).
% 11.05/4.05  tff(c_608, plain, (![A_183, D_184]: (r2_hidden(k1_funct_1(A_183, D_184), k2_relat_1(A_183)) | ~r2_hidden(D_184, k1_relat_1(A_183)) | ~v1_funct_1(A_183) | ~v1_relat_1(A_183))), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.05/4.05  tff(c_36, plain, (![A_20, B_21]: (m1_subset_1(A_20, k1_zfmisc_1(B_21)) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_58])).
% 11.05/4.05  tff(c_385, plain, (![A_147, C_148, B_149]: (m1_subset_1(A_147, C_148) | ~m1_subset_1(B_149, k1_zfmisc_1(C_148)) | ~r2_hidden(A_147, B_149))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.05/4.05  tff(c_390, plain, (![A_147, B_21, A_20]: (m1_subset_1(A_147, B_21) | ~r2_hidden(A_147, A_20) | ~r1_tarski(A_20, B_21))), inference(resolution, [status(thm)], [c_36, c_385])).
% 11.05/4.05  tff(c_19212, plain, (![A_77122, D_77123, B_77124]: (m1_subset_1(k1_funct_1(A_77122, D_77123), B_77124) | ~r1_tarski(k2_relat_1(A_77122), B_77124) | ~r2_hidden(D_77123, k1_relat_1(A_77122)) | ~v1_funct_1(A_77122) | ~v1_relat_1(A_77122))), inference(resolution, [status(thm)], [c_608, c_390])).
% 11.05/4.05  tff(c_19222, plain, (![B_77305, D_77306, A_77307]: (m1_subset_1(k1_funct_1(B_77305, D_77306), A_77307) | ~r2_hidden(D_77306, k1_relat_1(B_77305)) | ~v1_funct_1(B_77305) | ~v5_relat_1(B_77305, A_77307) | ~v1_relat_1(B_77305))), inference(resolution, [status(thm)], [c_42, c_19212])).
% 11.05/4.05  tff(c_19251, plain, (![D_77306, A_77307]: (m1_subset_1(k1_funct_1('#skF_11', D_77306), A_77307) | ~r2_hidden(D_77306, '#skF_8') | ~v1_funct_1('#skF_11') | ~v5_relat_1('#skF_11', A_77307) | ~v1_relat_1('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_1139, c_19222])).
% 11.05/4.05  tff(c_19277, plain, (![D_77488, A_77489]: (m1_subset_1(k1_funct_1('#skF_11', D_77488), A_77489) | ~r2_hidden(D_77488, '#skF_8') | ~v5_relat_1('#skF_11', A_77489))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_92, c_19251])).
% 11.05/4.05  tff(c_26, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.05/4.05  tff(c_108, plain, (![D_85, A_86]: (r2_hidden(D_85, k2_tarski(A_86, D_85)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.05/4.05  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.05/4.05  tff(c_116, plain, (![A_87, D_88]: (~v1_xboole_0(k2_tarski(A_87, D_88)))), inference(resolution, [status(thm)], [c_108, c_2])).
% 11.05/4.05  tff(c_118, plain, (![A_12]: (~v1_xboole_0(k1_tarski(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_116])).
% 11.05/4.05  tff(c_32, plain, (![A_18, B_19]: (r2_hidden(A_18, B_19) | v1_xboole_0(B_19) | ~m1_subset_1(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_54])).
% 11.05/4.05  tff(c_313, plain, (![D_137, B_138, A_139]: (D_137=B_138 | D_137=A_139 | ~r2_hidden(D_137, k2_tarski(A_139, B_138)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.05/4.05  tff(c_346, plain, (![D_142, A_143]: (D_142=A_143 | D_142=A_143 | ~r2_hidden(D_142, k1_tarski(A_143)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_313])).
% 11.05/4.05  tff(c_350, plain, (![A_18, A_143]: (A_18=A_143 | v1_xboole_0(k1_tarski(A_143)) | ~m1_subset_1(A_18, k1_tarski(A_143)))), inference(resolution, [status(thm)], [c_32, c_346])).
% 11.05/4.05  tff(c_360, plain, (![A_18, A_143]: (A_18=A_143 | ~m1_subset_1(A_18, k1_tarski(A_143)))), inference(negUnitSimplification, [status(thm)], [c_118, c_350])).
% 11.05/4.05  tff(c_19377, plain, (![D_77670, A_77671]: (k1_funct_1('#skF_11', D_77670)=A_77671 | ~r2_hidden(D_77670, '#skF_8') | ~v5_relat_1('#skF_11', k1_tarski(A_77671)))), inference(resolution, [status(thm)], [c_19277, c_360])).
% 11.05/4.05  tff(c_19451, plain, (![A_77852]: (k1_funct_1('#skF_11', '#skF_10')=A_77852 | ~v5_relat_1('#skF_11', k1_tarski(A_77852)))), inference(resolution, [status(thm)], [c_86, c_19377])).
% 11.05/4.05  tff(c_19462, plain, (k1_funct_1('#skF_11', '#skF_10')='#skF_9'), inference(resolution, [status(thm)], [c_259, c_19451])).
% 11.05/4.05  tff(c_19466, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_19462])).
% 11.05/4.05  tff(c_19467, plain, (k1_tarski('#skF_9')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1138])).
% 11.05/4.05  tff(c_114, plain, (![A_12]: (r2_hidden(A_12, k1_tarski(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_108])).
% 11.05/4.05  tff(c_134, plain, (![B_93, A_94]: (~r1_tarski(B_93, A_94) | ~r2_hidden(A_94, B_93))), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.05/4.05  tff(c_148, plain, (![A_12]: (~r1_tarski(k1_tarski(A_12), A_12))), inference(resolution, [status(thm)], [c_114, c_134])).
% 11.05/4.05  tff(c_19497, plain, (~r1_tarski(k1_xboole_0, '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_19467, c_148])).
% 11.05/4.05  tff(c_19511, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_19497])).
% 11.05/4.05  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.05/4.05  
% 11.05/4.05  Inference rules
% 11.05/4.05  ----------------------
% 11.05/4.05  #Ref     : 0
% 11.05/4.05  #Sup     : 2364
% 11.05/4.05  #Fact    : 22
% 11.05/4.05  #Define  : 0
% 11.05/4.05  #Split   : 36
% 11.05/4.05  #Chain   : 0
% 11.05/4.05  #Close   : 0
% 11.05/4.05  
% 11.05/4.05  Ordering : KBO
% 11.05/4.05  
% 11.05/4.05  Simplification rules
% 11.05/4.05  ----------------------
% 11.05/4.05  #Subsume      : 556
% 11.05/4.05  #Demod        : 892
% 11.05/4.05  #Tautology    : 499
% 11.05/4.05  #SimpNegUnit  : 114
% 11.05/4.05  #BackRed      : 62
% 11.05/4.05  
% 11.05/4.05  #Partial instantiations: 36377
% 11.05/4.05  #Strategies tried      : 1
% 11.05/4.05  
% 11.05/4.05  Timing (in seconds)
% 11.05/4.05  ----------------------
% 11.05/4.05  Preprocessing        : 0.36
% 11.05/4.05  Parsing              : 0.18
% 11.05/4.05  CNF conversion       : 0.03
% 11.05/4.05  Main loop            : 2.91
% 11.05/4.05  Inferencing          : 1.26
% 11.05/4.05  Reduction            : 0.88
% 11.05/4.05  Demodulation         : 0.61
% 11.05/4.05  BG Simplification    : 0.08
% 11.05/4.05  Subsumption          : 0.51
% 11.05/4.05  Abstraction          : 0.12
% 11.05/4.05  MUC search           : 0.00
% 11.05/4.05  Cooper               : 0.00
% 11.05/4.05  Total                : 3.31
% 11.05/4.05  Index Insertion      : 0.00
% 11.05/4.05  Index Deletion       : 0.00
% 11.05/4.05  Index Matching       : 0.00
% 11.05/4.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
