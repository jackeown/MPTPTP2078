%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:27 EST 2020

% Result     : Theorem 3.69s
% Output     : CNFRefutation 3.69s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 159 expanded)
%              Number of leaves         :   40 (  73 expanded)
%              Depth                    :   12
%              Number of atoms          :  131 ( 376 expanded)
%              Number of equality atoms :   30 (  77 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_120,negated_conjecture,(
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

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_49,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_66,axiom,(
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

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_101,axiom,(
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

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_62,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_136,plain,(
    ! [A_100,B_101,C_102,D_103] :
      ( k7_relset_1(A_100,B_101,C_102,D_103) = k9_relat_1(C_102,D_103)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_147,plain,(
    ! [D_104] : k7_relset_1('#skF_6','#skF_7','#skF_9',D_104) = k9_relat_1('#skF_9',D_104) ),
    inference(resolution,[status(thm)],[c_62,c_136])).

tff(c_40,plain,(
    ! [A_58,B_59,C_60,D_61] :
      ( m1_subset_1(k7_relset_1(A_58,B_59,C_60,D_61),k1_zfmisc_1(B_59))
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_153,plain,(
    ! [D_104] :
      ( m1_subset_1(k9_relat_1('#skF_9',D_104),k1_zfmisc_1('#skF_7'))
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_40])).

tff(c_169,plain,(
    ! [D_105] : m1_subset_1(k9_relat_1('#skF_9',D_105),k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_153])).

tff(c_8,plain,(
    ! [C_8,B_7,A_6] :
      ( ~ v1_xboole_0(C_8)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(C_8))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_175,plain,(
    ! [A_6,D_105] :
      ( ~ v1_xboole_0('#skF_7')
      | ~ r2_hidden(A_6,k9_relat_1('#skF_9',D_105)) ) ),
    inference(resolution,[status(thm)],[c_169,c_8])).

tff(c_178,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_175])).

tff(c_12,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_94,plain,(
    ! [B_86,A_87] :
      ( v1_relat_1(B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_87))
      | ~ v1_relat_1(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_97,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_62,c_94])).

tff(c_100,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_97])).

tff(c_66,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_16,plain,(
    ! [A_14,B_37,D_52] :
      ( k1_funct_1(A_14,'#skF_5'(A_14,B_37,k9_relat_1(A_14,B_37),D_52)) = D_52
      | ~ r2_hidden(D_52,k9_relat_1(A_14,B_37))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_18,plain,(
    ! [A_14,B_37,D_52] :
      ( r2_hidden('#skF_5'(A_14,B_37,k9_relat_1(A_14,B_37),D_52),B_37)
      | ~ r2_hidden(D_52,k9_relat_1(A_14,B_37))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_64,plain,(
    v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_114,plain,(
    ! [A_93,B_94,C_95] :
      ( k1_relset_1(A_93,B_94,C_95) = k1_relat_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_118,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_62,c_114])).

tff(c_235,plain,(
    ! [B_128,A_129,C_130] :
      ( k1_xboole_0 = B_128
      | k1_relset_1(A_129,B_128,C_130) = A_129
      | ~ v1_funct_2(C_130,A_129,B_128)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_129,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_242,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_235])).

tff(c_246,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_118,c_242])).

tff(c_247,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_246])).

tff(c_375,plain,(
    ! [A_165,B_166,D_167] :
      ( r2_hidden('#skF_5'(A_165,B_166,k9_relat_1(A_165,B_166),D_167),k1_relat_1(A_165))
      | ~ r2_hidden(D_167,k9_relat_1(A_165,B_166))
      | ~ v1_funct_1(A_165)
      | ~ v1_relat_1(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_384,plain,(
    ! [B_166,D_167] :
      ( r2_hidden('#skF_5'('#skF_9',B_166,k9_relat_1('#skF_9',B_166),D_167),'#skF_6')
      | ~ r2_hidden(D_167,k9_relat_1('#skF_9',B_166))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_375])).

tff(c_553,plain,(
    ! [B_183,D_184] :
      ( r2_hidden('#skF_5'('#skF_9',B_183,k9_relat_1('#skF_9',B_183),D_184),'#skF_6')
      | ~ r2_hidden(D_184,k9_relat_1('#skF_9',B_183)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_66,c_384])).

tff(c_58,plain,(
    ! [F_76] :
      ( k1_funct_1('#skF_9',F_76) != '#skF_10'
      | ~ r2_hidden(F_76,'#skF_8')
      | ~ r2_hidden(F_76,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_944,plain,(
    ! [B_212,D_213] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9',B_212,k9_relat_1('#skF_9',B_212),D_213)) != '#skF_10'
      | ~ r2_hidden('#skF_5'('#skF_9',B_212,k9_relat_1('#skF_9',B_212),D_213),'#skF_8')
      | ~ r2_hidden(D_213,k9_relat_1('#skF_9',B_212)) ) ),
    inference(resolution,[status(thm)],[c_553,c_58])).

tff(c_951,plain,(
    ! [D_52] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_8',k9_relat_1('#skF_9','#skF_8'),D_52)) != '#skF_10'
      | ~ r2_hidden(D_52,k9_relat_1('#skF_9','#skF_8'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_18,c_944])).

tff(c_1172,plain,(
    ! [D_223] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_8',k9_relat_1('#skF_9','#skF_8'),D_223)) != '#skF_10'
      | ~ r2_hidden(D_223,k9_relat_1('#skF_9','#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_66,c_951])).

tff(c_1176,plain,(
    ! [D_52] :
      ( D_52 != '#skF_10'
      | ~ r2_hidden(D_52,k9_relat_1('#skF_9','#skF_8'))
      | ~ r2_hidden(D_52,k9_relat_1('#skF_9','#skF_8'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1172])).

tff(c_1180,plain,(
    ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_66,c_1176])).

tff(c_143,plain,(
    ! [D_103] : k7_relset_1('#skF_6','#skF_7','#skF_9',D_103) = k9_relat_1('#skF_9',D_103) ),
    inference(resolution,[status(thm)],[c_62,c_136])).

tff(c_60,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_6','#skF_7','#skF_9','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_146,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_60])).

tff(c_1182,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1180,c_146])).

tff(c_1183,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_246])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_75,plain,(
    ! [B_83,A_84] :
      ( ~ r1_tarski(B_83,A_84)
      | ~ r2_hidden(A_84,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_80,plain,(
    ! [A_85] :
      ( ~ r1_tarski(A_85,'#skF_1'(A_85))
      | v1_xboole_0(A_85) ) ),
    inference(resolution,[status(thm)],[c_4,c_75])).

tff(c_85,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_80])).

tff(c_1191,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1183,c_85])).

tff(c_1194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_1191])).

tff(c_1195,plain,(
    ! [A_6,D_105] : ~ r2_hidden(A_6,k9_relat_1('#skF_9',D_105)) ),
    inference(splitRight,[status(thm)],[c_175])).

tff(c_1198,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1195,c_146])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:12:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.69/1.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.63  
% 3.69/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.63  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3
% 3.69/1.63  
% 3.69/1.63  %Foreground sorts:
% 3.69/1.63  
% 3.69/1.63  
% 3.69/1.63  %Background operators:
% 3.69/1.63  
% 3.69/1.63  
% 3.69/1.63  %Foreground operators:
% 3.69/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.69/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.69/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.69/1.63  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.69/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.69/1.63  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.69/1.63  tff('#skF_7', type, '#skF_7': $i).
% 3.69/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.69/1.63  tff('#skF_10', type, '#skF_10': $i).
% 3.69/1.63  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.69/1.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.69/1.63  tff('#skF_6', type, '#skF_6': $i).
% 3.69/1.63  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.69/1.63  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.69/1.63  tff('#skF_9', type, '#skF_9': $i).
% 3.69/1.63  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.69/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.69/1.63  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.69/1.63  tff('#skF_8', type, '#skF_8': $i).
% 3.69/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.69/1.63  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 3.69/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.69/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.69/1.63  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.69/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.69/1.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.69/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.69/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.69/1.63  
% 3.69/1.65  tff(f_120, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_funct_2)).
% 3.69/1.65  tff(f_83, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.69/1.65  tff(f_75, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 3.69/1.65  tff(f_40, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.69/1.65  tff(f_49, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.69/1.65  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.69/1.65  tff(f_66, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 3.69/1.65  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.69/1.65  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.69/1.65  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.69/1.65  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.69/1.65  tff(f_71, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.69/1.65  tff(c_62, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.69/1.65  tff(c_136, plain, (![A_100, B_101, C_102, D_103]: (k7_relset_1(A_100, B_101, C_102, D_103)=k9_relat_1(C_102, D_103) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.69/1.65  tff(c_147, plain, (![D_104]: (k7_relset_1('#skF_6', '#skF_7', '#skF_9', D_104)=k9_relat_1('#skF_9', D_104))), inference(resolution, [status(thm)], [c_62, c_136])).
% 3.69/1.65  tff(c_40, plain, (![A_58, B_59, C_60, D_61]: (m1_subset_1(k7_relset_1(A_58, B_59, C_60, D_61), k1_zfmisc_1(B_59)) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.69/1.65  tff(c_153, plain, (![D_104]: (m1_subset_1(k9_relat_1('#skF_9', D_104), k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))))), inference(superposition, [status(thm), theory('equality')], [c_147, c_40])).
% 3.69/1.65  tff(c_169, plain, (![D_105]: (m1_subset_1(k9_relat_1('#skF_9', D_105), k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_153])).
% 3.69/1.65  tff(c_8, plain, (![C_8, B_7, A_6]: (~v1_xboole_0(C_8) | ~m1_subset_1(B_7, k1_zfmisc_1(C_8)) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.69/1.65  tff(c_175, plain, (![A_6, D_105]: (~v1_xboole_0('#skF_7') | ~r2_hidden(A_6, k9_relat_1('#skF_9', D_105)))), inference(resolution, [status(thm)], [c_169, c_8])).
% 3.69/1.65  tff(c_178, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_175])).
% 3.69/1.65  tff(c_12, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.69/1.65  tff(c_94, plain, (![B_86, A_87]: (v1_relat_1(B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(A_87)) | ~v1_relat_1(A_87))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.69/1.65  tff(c_97, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_62, c_94])).
% 3.69/1.65  tff(c_100, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_97])).
% 3.69/1.65  tff(c_66, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.69/1.65  tff(c_16, plain, (![A_14, B_37, D_52]: (k1_funct_1(A_14, '#skF_5'(A_14, B_37, k9_relat_1(A_14, B_37), D_52))=D_52 | ~r2_hidden(D_52, k9_relat_1(A_14, B_37)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.69/1.65  tff(c_18, plain, (![A_14, B_37, D_52]: (r2_hidden('#skF_5'(A_14, B_37, k9_relat_1(A_14, B_37), D_52), B_37) | ~r2_hidden(D_52, k9_relat_1(A_14, B_37)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.69/1.65  tff(c_64, plain, (v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.69/1.65  tff(c_114, plain, (![A_93, B_94, C_95]: (k1_relset_1(A_93, B_94, C_95)=k1_relat_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.69/1.65  tff(c_118, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_62, c_114])).
% 3.69/1.65  tff(c_235, plain, (![B_128, A_129, C_130]: (k1_xboole_0=B_128 | k1_relset_1(A_129, B_128, C_130)=A_129 | ~v1_funct_2(C_130, A_129, B_128) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_129, B_128))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.69/1.65  tff(c_242, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_62, c_235])).
% 3.69/1.65  tff(c_246, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_118, c_242])).
% 3.69/1.65  tff(c_247, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_246])).
% 3.69/1.65  tff(c_375, plain, (![A_165, B_166, D_167]: (r2_hidden('#skF_5'(A_165, B_166, k9_relat_1(A_165, B_166), D_167), k1_relat_1(A_165)) | ~r2_hidden(D_167, k9_relat_1(A_165, B_166)) | ~v1_funct_1(A_165) | ~v1_relat_1(A_165))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.69/1.65  tff(c_384, plain, (![B_166, D_167]: (r2_hidden('#skF_5'('#skF_9', B_166, k9_relat_1('#skF_9', B_166), D_167), '#skF_6') | ~r2_hidden(D_167, k9_relat_1('#skF_9', B_166)) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_247, c_375])).
% 3.69/1.65  tff(c_553, plain, (![B_183, D_184]: (r2_hidden('#skF_5'('#skF_9', B_183, k9_relat_1('#skF_9', B_183), D_184), '#skF_6') | ~r2_hidden(D_184, k9_relat_1('#skF_9', B_183)))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_66, c_384])).
% 3.69/1.65  tff(c_58, plain, (![F_76]: (k1_funct_1('#skF_9', F_76)!='#skF_10' | ~r2_hidden(F_76, '#skF_8') | ~r2_hidden(F_76, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.69/1.65  tff(c_944, plain, (![B_212, D_213]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', B_212, k9_relat_1('#skF_9', B_212), D_213))!='#skF_10' | ~r2_hidden('#skF_5'('#skF_9', B_212, k9_relat_1('#skF_9', B_212), D_213), '#skF_8') | ~r2_hidden(D_213, k9_relat_1('#skF_9', B_212)))), inference(resolution, [status(thm)], [c_553, c_58])).
% 3.69/1.65  tff(c_951, plain, (![D_52]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_8', k9_relat_1('#skF_9', '#skF_8'), D_52))!='#skF_10' | ~r2_hidden(D_52, k9_relat_1('#skF_9', '#skF_8')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_18, c_944])).
% 3.69/1.65  tff(c_1172, plain, (![D_223]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_8', k9_relat_1('#skF_9', '#skF_8'), D_223))!='#skF_10' | ~r2_hidden(D_223, k9_relat_1('#skF_9', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_66, c_951])).
% 3.69/1.65  tff(c_1176, plain, (![D_52]: (D_52!='#skF_10' | ~r2_hidden(D_52, k9_relat_1('#skF_9', '#skF_8')) | ~r2_hidden(D_52, k9_relat_1('#skF_9', '#skF_8')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1172])).
% 3.69/1.65  tff(c_1180, plain, (~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_66, c_1176])).
% 3.69/1.65  tff(c_143, plain, (![D_103]: (k7_relset_1('#skF_6', '#skF_7', '#skF_9', D_103)=k9_relat_1('#skF_9', D_103))), inference(resolution, [status(thm)], [c_62, c_136])).
% 3.69/1.65  tff(c_60, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.69/1.65  tff(c_146, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_60])).
% 3.69/1.65  tff(c_1182, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1180, c_146])).
% 3.69/1.65  tff(c_1183, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_246])).
% 3.69/1.65  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.69/1.65  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.69/1.65  tff(c_75, plain, (![B_83, A_84]: (~r1_tarski(B_83, A_84) | ~r2_hidden(A_84, B_83))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.69/1.65  tff(c_80, plain, (![A_85]: (~r1_tarski(A_85, '#skF_1'(A_85)) | v1_xboole_0(A_85))), inference(resolution, [status(thm)], [c_4, c_75])).
% 3.69/1.65  tff(c_85, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_80])).
% 3.69/1.65  tff(c_1191, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1183, c_85])).
% 3.69/1.65  tff(c_1194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_178, c_1191])).
% 3.69/1.65  tff(c_1195, plain, (![A_6, D_105]: (~r2_hidden(A_6, k9_relat_1('#skF_9', D_105)))), inference(splitRight, [status(thm)], [c_175])).
% 3.69/1.65  tff(c_1198, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1195, c_146])).
% 3.69/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.65  
% 3.69/1.65  Inference rules
% 3.69/1.65  ----------------------
% 3.69/1.65  #Ref     : 0
% 3.69/1.65  #Sup     : 236
% 3.69/1.65  #Fact    : 0
% 3.69/1.65  #Define  : 0
% 3.69/1.65  #Split   : 5
% 3.69/1.65  #Chain   : 0
% 3.69/1.65  #Close   : 0
% 3.69/1.65  
% 3.69/1.65  Ordering : KBO
% 3.69/1.65  
% 3.69/1.65  Simplification rules
% 3.69/1.65  ----------------------
% 3.69/1.65  #Subsume      : 65
% 3.69/1.65  #Demod        : 137
% 3.69/1.65  #Tautology    : 27
% 3.69/1.65  #SimpNegUnit  : 6
% 3.69/1.65  #BackRed      : 14
% 3.69/1.65  
% 3.69/1.65  #Partial instantiations: 0
% 3.69/1.65  #Strategies tried      : 1
% 3.69/1.65  
% 3.69/1.65  Timing (in seconds)
% 3.69/1.65  ----------------------
% 3.69/1.65  Preprocessing        : 0.36
% 3.69/1.65  Parsing              : 0.17
% 3.69/1.65  CNF conversion       : 0.03
% 3.69/1.65  Main loop            : 0.51
% 3.69/1.65  Inferencing          : 0.19
% 3.69/1.65  Reduction            : 0.14
% 3.69/1.65  Demodulation         : 0.10
% 3.69/1.65  BG Simplification    : 0.03
% 3.69/1.65  Subsumption          : 0.11
% 3.69/1.65  Abstraction          : 0.04
% 3.69/1.65  MUC search           : 0.00
% 3.69/1.65  Cooper               : 0.00
% 3.69/1.65  Total                : 0.91
% 3.69/1.65  Index Insertion      : 0.00
% 3.69/1.65  Index Deletion       : 0.00
% 3.69/1.65  Index Matching       : 0.00
% 3.69/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
