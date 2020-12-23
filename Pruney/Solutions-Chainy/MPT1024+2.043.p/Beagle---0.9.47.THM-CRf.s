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
% DateTime   : Thu Dec  3 10:16:27 EST 2020

% Result     : Theorem 5.66s
% Output     : CNFRefutation 5.90s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 854 expanded)
%              Number of leaves         :   40 ( 309 expanded)
%              Depth                    :   13
%              Number of atoms          :  253 (2703 expanded)
%              Number of equality atoms :   70 ( 919 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

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

tff(f_54,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_127,negated_conjecture,(
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

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_82,axiom,(
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

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_108,axiom,(
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

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(c_18,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_72,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_139,plain,(
    ! [B_90,A_91] :
      ( v1_relat_1(B_90)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(A_91))
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_150,plain,
    ( v1_relat_1('#skF_10')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_72,c_139])).

tff(c_155,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_150])).

tff(c_76,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_30,plain,(
    ! [A_18,B_41,D_56] :
      ( k1_funct_1(A_18,'#skF_6'(A_18,B_41,k9_relat_1(A_18,B_41),D_56)) = D_56
      | ~ r2_hidden(D_56,k9_relat_1(A_18,B_41))
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_32,plain,(
    ! [A_18,B_41,D_56] :
      ( r2_hidden('#skF_6'(A_18,B_41,k9_relat_1(A_18,B_41),D_56),B_41)
      | ~ r2_hidden(D_56,k9_relat_1(A_18,B_41))
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_74,plain,(
    v1_funct_2('#skF_10','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_167,plain,(
    ! [A_92,B_93,C_94] :
      ( k1_relset_1(A_92,B_93,C_94) = k1_relat_1(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_181,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_72,c_167])).

tff(c_1169,plain,(
    ! [B_257,A_258,C_259] :
      ( k1_xboole_0 = B_257
      | k1_relset_1(A_258,B_257,C_259) = A_258
      | ~ v1_funct_2(C_259,A_258,B_257)
      | ~ m1_subset_1(C_259,k1_zfmisc_1(k2_zfmisc_1(A_258,B_257))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1180,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_10') = '#skF_7'
    | ~ v1_funct_2('#skF_10','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_72,c_1169])).

tff(c_1185,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relat_1('#skF_10') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_181,c_1180])).

tff(c_1186,plain,(
    k1_relat_1('#skF_10') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_1185])).

tff(c_1932,plain,(
    ! [A_342,B_343,D_344] :
      ( r2_hidden('#skF_6'(A_342,B_343,k9_relat_1(A_342,B_343),D_344),k1_relat_1(A_342))
      | ~ r2_hidden(D_344,k9_relat_1(A_342,B_343))
      | ~ v1_funct_1(A_342)
      | ~ v1_relat_1(A_342) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1945,plain,(
    ! [B_343,D_344] :
      ( r2_hidden('#skF_6'('#skF_10',B_343,k9_relat_1('#skF_10',B_343),D_344),'#skF_7')
      | ~ r2_hidden(D_344,k9_relat_1('#skF_10',B_343))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1186,c_1932])).

tff(c_1952,plain,(
    ! [B_345,D_346] :
      ( r2_hidden('#skF_6'('#skF_10',B_345,k9_relat_1('#skF_10',B_345),D_346),'#skF_7')
      | ~ r2_hidden(D_346,k9_relat_1('#skF_10',B_345)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_76,c_1945])).

tff(c_68,plain,(
    ! [F_74] :
      ( k1_funct_1('#skF_10',F_74) != '#skF_11'
      | ~ r2_hidden(F_74,'#skF_9')
      | ~ r2_hidden(F_74,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1984,plain,(
    ! [B_352,D_353] :
      ( k1_funct_1('#skF_10','#skF_6'('#skF_10',B_352,k9_relat_1('#skF_10',B_352),D_353)) != '#skF_11'
      | ~ r2_hidden('#skF_6'('#skF_10',B_352,k9_relat_1('#skF_10',B_352),D_353),'#skF_9')
      | ~ r2_hidden(D_353,k9_relat_1('#skF_10',B_352)) ) ),
    inference(resolution,[status(thm)],[c_1952,c_68])).

tff(c_1988,plain,(
    ! [D_56] :
      ( k1_funct_1('#skF_10','#skF_6'('#skF_10','#skF_9',k9_relat_1('#skF_10','#skF_9'),D_56)) != '#skF_11'
      | ~ r2_hidden(D_56,k9_relat_1('#skF_10','#skF_9'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_32,c_1984])).

tff(c_1998,plain,(
    ! [D_354] :
      ( k1_funct_1('#skF_10','#skF_6'('#skF_10','#skF_9',k9_relat_1('#skF_10','#skF_9'),D_354)) != '#skF_11'
      | ~ r2_hidden(D_354,k9_relat_1('#skF_10','#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_76,c_1988])).

tff(c_2002,plain,(
    ! [D_56] :
      ( D_56 != '#skF_11'
      | ~ r2_hidden(D_56,k9_relat_1('#skF_10','#skF_9'))
      | ~ r2_hidden(D_56,k9_relat_1('#skF_10','#skF_9'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1998])).

tff(c_2005,plain,(
    ~ r2_hidden('#skF_11',k9_relat_1('#skF_10','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_76,c_2002])).

tff(c_342,plain,(
    ! [A_133,B_134,C_135,D_136] :
      ( k7_relset_1(A_133,B_134,C_135,D_136) = k9_relat_1(C_135,D_136)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_353,plain,(
    ! [D_136] : k7_relset_1('#skF_7','#skF_8','#skF_10',D_136) = k9_relat_1('#skF_10',D_136) ),
    inference(resolution,[status(thm)],[c_72,c_342])).

tff(c_70,plain,(
    r2_hidden('#skF_11',k7_relset_1('#skF_7','#skF_8','#skF_10','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_356,plain,(
    r2_hidden('#skF_11',k9_relat_1('#skF_10','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_70])).

tff(c_2007,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2005,c_356])).

tff(c_2008,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1185])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2020,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2008,c_6])).

tff(c_58,plain,(
    ! [C_69,A_67] :
      ( k1_xboole_0 = C_69
      | ~ v1_funct_2(C_69,A_67,k1_xboole_0)
      | k1_xboole_0 = A_67
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2238,plain,(
    ! [C_379,A_380] :
      ( C_379 = '#skF_8'
      | ~ v1_funct_2(C_379,A_380,'#skF_8')
      | A_380 = '#skF_8'
      | ~ m1_subset_1(C_379,k1_zfmisc_1(k2_zfmisc_1(A_380,'#skF_8'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2008,c_2008,c_2008,c_2008,c_58])).

tff(c_2249,plain,
    ( '#skF_10' = '#skF_8'
    | ~ v1_funct_2('#skF_10','#skF_7','#skF_8')
    | '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_72,c_2238])).

tff(c_2254,plain,
    ( '#skF_10' = '#skF_8'
    | '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2249])).

tff(c_2255,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_2254])).

tff(c_12,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ v1_xboole_0(B_6)
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [B_6,A_5] :
      ( r2_hidden(B_6,A_5)
      | ~ m1_subset_1(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_88,plain,(
    ! [F_80] :
      ( k1_funct_1('#skF_10',F_80) != '#skF_11'
      | ~ r2_hidden(F_80,'#skF_9')
      | ~ r2_hidden(F_80,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_93,plain,
    ( k1_funct_1('#skF_10','#skF_1'('#skF_7')) != '#skF_11'
    | ~ r2_hidden('#skF_1'('#skF_7'),'#skF_9')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_4,c_88])).

tff(c_156,plain,(
    ~ r2_hidden('#skF_1'('#skF_7'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_160,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_7'),'#skF_9')
    | v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_10,c_156])).

tff(c_161,plain,(
    ~ m1_subset_1('#skF_1'('#skF_7'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_165,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_7'))
    | ~ v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_12,c_161])).

tff(c_166,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_165])).

tff(c_116,plain,(
    ! [B_87,A_88] :
      ( r2_hidden(B_87,A_88)
      | ~ m1_subset_1(B_87,A_88)
      | v1_xboole_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_128,plain,(
    ! [B_87] :
      ( k1_funct_1('#skF_10',B_87) != '#skF_11'
      | ~ r2_hidden(B_87,'#skF_9')
      | ~ m1_subset_1(B_87,'#skF_7')
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_116,c_68])).

tff(c_190,plain,(
    ! [B_97] :
      ( k1_funct_1('#skF_10',B_97) != '#skF_11'
      | ~ r2_hidden(B_97,'#skF_9')
      | ~ m1_subset_1(B_97,'#skF_7') ) ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_198,plain,
    ( k1_funct_1('#skF_10','#skF_1'('#skF_9')) != '#skF_11'
    | ~ m1_subset_1('#skF_1'('#skF_9'),'#skF_7')
    | v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_4,c_190])).

tff(c_204,plain,
    ( k1_funct_1('#skF_10','#skF_1'('#skF_9')) != '#skF_11'
    | ~ m1_subset_1('#skF_1'('#skF_9'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_198])).

tff(c_205,plain,(
    ~ m1_subset_1('#skF_1'('#skF_9'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_204])).

tff(c_209,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_9'))
    | ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_12,c_205])).

tff(c_217,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_209])).

tff(c_2266,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2255,c_217])).

tff(c_2278,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2020,c_2266])).

tff(c_2279,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_2254])).

tff(c_366,plain,(
    ! [A_138,B_139,C_140] :
      ( r2_hidden(k4_tarski('#skF_2'(A_138,B_139,C_140),A_138),C_140)
      | ~ r2_hidden(A_138,k9_relat_1(C_140,B_139))
      | ~ v1_relat_1(C_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_440,plain,(
    ! [C_141,A_142,B_143] :
      ( ~ v1_xboole_0(C_141)
      | ~ r2_hidden(A_142,k9_relat_1(C_141,B_143))
      | ~ v1_relat_1(C_141) ) ),
    inference(resolution,[status(thm)],[c_366,c_2])).

tff(c_443,plain,
    ( ~ v1_xboole_0('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_356,c_440])).

tff(c_462,plain,(
    ~ v1_xboole_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_443])).

tff(c_2289,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2279,c_462])).

tff(c_2306,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2020,c_2289])).

tff(c_2308,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_2869,plain,(
    ! [B_493,A_494,C_495] :
      ( k1_xboole_0 = B_493
      | k1_relset_1(A_494,B_493,C_495) = A_494
      | ~ v1_funct_2(C_495,A_494,B_493)
      | ~ m1_subset_1(C_495,k1_zfmisc_1(k2_zfmisc_1(A_494,B_493))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2880,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_10') = '#skF_7'
    | ~ v1_funct_2('#skF_10','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_72,c_2869])).

tff(c_2885,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relat_1('#skF_10') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_181,c_2880])).

tff(c_2886,plain,(
    k1_relat_1('#skF_10') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_2885])).

tff(c_2390,plain,(
    ! [A_399,B_400,C_401] :
      ( r2_hidden('#skF_2'(A_399,B_400,C_401),k1_relat_1(C_401))
      | ~ r2_hidden(A_399,k9_relat_1(C_401,B_400))
      | ~ v1_relat_1(C_401) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2399,plain,(
    ! [C_402,A_403,B_404] :
      ( ~ v1_xboole_0(k1_relat_1(C_402))
      | ~ r2_hidden(A_403,k9_relat_1(C_402,B_404))
      | ~ v1_relat_1(C_402) ) ),
    inference(resolution,[status(thm)],[c_2390,c_2])).

tff(c_2414,plain,(
    ! [C_402,B_404] :
      ( ~ v1_xboole_0(k1_relat_1(C_402))
      | ~ v1_relat_1(C_402)
      | v1_xboole_0(k9_relat_1(C_402,B_404)) ) ),
    inference(resolution,[status(thm)],[c_4,c_2399])).

tff(c_2467,plain,(
    ! [A_420,B_421,C_422,D_423] :
      ( k7_relset_1(A_420,B_421,C_422,D_423) = k9_relat_1(C_422,D_423)
      | ~ m1_subset_1(C_422,k1_zfmisc_1(k2_zfmisc_1(A_420,B_421))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2478,plain,(
    ! [D_423] : k7_relset_1('#skF_7','#skF_8','#skF_10',D_423) = k9_relat_1('#skF_10',D_423) ),
    inference(resolution,[status(thm)],[c_72,c_2467])).

tff(c_87,plain,(
    ~ v1_xboole_0(k7_relset_1('#skF_7','#skF_8','#skF_10','#skF_9')) ),
    inference(resolution,[status(thm)],[c_70,c_2])).

tff(c_2519,plain,(
    ~ v1_xboole_0(k9_relat_1('#skF_10','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2478,c_87])).

tff(c_2532,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_10'))
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_2414,c_2519])).

tff(c_2538,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_2532])).

tff(c_2887,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2886,c_2538])).

tff(c_2891,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2308,c_2887])).

tff(c_2892,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_2885])).

tff(c_2906,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2892,c_6])).

tff(c_3041,plain,(
    ! [C_513,A_514] :
      ( C_513 = '#skF_8'
      | ~ v1_funct_2(C_513,A_514,'#skF_8')
      | A_514 = '#skF_8'
      | ~ m1_subset_1(C_513,k1_zfmisc_1(k2_zfmisc_1(A_514,'#skF_8'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2892,c_2892,c_2892,c_2892,c_58])).

tff(c_3052,plain,
    ( '#skF_10' = '#skF_8'
    | ~ v1_funct_2('#skF_10','#skF_7','#skF_8')
    | '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_72,c_3041])).

tff(c_3057,plain,
    ( '#skF_10' = '#skF_8'
    | '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3052])).

tff(c_3058,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_3057])).

tff(c_2893,plain,(
    k1_relat_1('#skF_10') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_2885])).

tff(c_3140,plain,(
    k1_relat_1('#skF_10') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3058,c_2893])).

tff(c_3159,plain,(
    v1_funct_2('#skF_10','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3058,c_74])).

tff(c_3153,plain,(
    k1_relset_1('#skF_8','#skF_8','#skF_10') = k1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3058,c_181])).

tff(c_3158,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3058,c_72])).

tff(c_64,plain,(
    ! [B_68,C_69] :
      ( k1_relset_1(k1_xboole_0,B_68,C_69) = k1_xboole_0
      | ~ v1_funct_2(C_69,k1_xboole_0,B_68)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_3384,plain,(
    ! [B_532,C_533] :
      ( k1_relset_1('#skF_8',B_532,C_533) = '#skF_8'
      | ~ v1_funct_2(C_533,'#skF_8',B_532)
      | ~ m1_subset_1(C_533,k1_zfmisc_1(k2_zfmisc_1('#skF_8',B_532))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2892,c_2892,c_2892,c_2892,c_64])).

tff(c_3387,plain,
    ( k1_relset_1('#skF_8','#skF_8','#skF_10') = '#skF_8'
    | ~ v1_funct_2('#skF_10','#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_3158,c_3384])).

tff(c_3398,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3159,c_3153,c_3387])).

tff(c_3400,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3140,c_3398])).

tff(c_3401,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_3057])).

tff(c_2520,plain,(
    r2_hidden('#skF_11',k9_relat_1('#skF_10','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2478,c_70])).

tff(c_2479,plain,(
    ! [A_424,B_425,C_426] :
      ( r2_hidden(k4_tarski('#skF_2'(A_424,B_425,C_426),A_424),C_426)
      | ~ r2_hidden(A_424,k9_relat_1(C_426,B_425))
      | ~ v1_relat_1(C_426) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2575,plain,(
    ! [C_428,A_429,B_430] :
      ( ~ v1_xboole_0(C_428)
      | ~ r2_hidden(A_429,k9_relat_1(C_428,B_430))
      | ~ v1_relat_1(C_428) ) ),
    inference(resolution,[status(thm)],[c_2479,c_2])).

tff(c_2578,plain,
    ( ~ v1_xboole_0('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_2520,c_2575])).

tff(c_2597,plain,(
    ~ v1_xboole_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_2578])).

tff(c_3408,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3401,c_2597])).

tff(c_3427,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2906,c_3408])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:41:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.66/2.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.90/2.12  
% 5.90/2.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.90/2.13  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_3
% 5.90/2.13  
% 5.90/2.13  %Foreground sorts:
% 5.90/2.13  
% 5.90/2.13  
% 5.90/2.13  %Background operators:
% 5.90/2.13  
% 5.90/2.13  
% 5.90/2.13  %Foreground operators:
% 5.90/2.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.90/2.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.90/2.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.90/2.13  tff('#skF_11', type, '#skF_11': $i).
% 5.90/2.13  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.90/2.13  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.90/2.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.90/2.13  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.90/2.13  tff('#skF_7', type, '#skF_7': $i).
% 5.90/2.13  tff('#skF_10', type, '#skF_10': $i).
% 5.90/2.13  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 5.90/2.13  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.90/2.13  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.90/2.13  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.90/2.13  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.90/2.13  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 5.90/2.13  tff('#skF_9', type, '#skF_9': $i).
% 5.90/2.13  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.90/2.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.90/2.13  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.90/2.13  tff('#skF_8', type, '#skF_8': $i).
% 5.90/2.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.90/2.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.90/2.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.90/2.13  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.90/2.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.90/2.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.90/2.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.90/2.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.90/2.13  
% 5.90/2.15  tff(f_54, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.90/2.15  tff(f_127, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_funct_2)).
% 5.90/2.15  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.90/2.15  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 5.90/2.15  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.90/2.15  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.90/2.15  tff(f_90, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 5.90/2.15  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.90/2.15  tff(f_45, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 5.90/2.15  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.90/2.15  tff(f_65, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 5.90/2.15  tff(c_18, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.90/2.15  tff(c_72, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.90/2.15  tff(c_139, plain, (![B_90, A_91]: (v1_relat_1(B_90) | ~m1_subset_1(B_90, k1_zfmisc_1(A_91)) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.90/2.15  tff(c_150, plain, (v1_relat_1('#skF_10') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_72, c_139])).
% 5.90/2.15  tff(c_155, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_150])).
% 5.90/2.15  tff(c_76, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.90/2.15  tff(c_30, plain, (![A_18, B_41, D_56]: (k1_funct_1(A_18, '#skF_6'(A_18, B_41, k9_relat_1(A_18, B_41), D_56))=D_56 | ~r2_hidden(D_56, k9_relat_1(A_18, B_41)) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.90/2.15  tff(c_32, plain, (![A_18, B_41, D_56]: (r2_hidden('#skF_6'(A_18, B_41, k9_relat_1(A_18, B_41), D_56), B_41) | ~r2_hidden(D_56, k9_relat_1(A_18, B_41)) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.90/2.15  tff(c_74, plain, (v1_funct_2('#skF_10', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.90/2.15  tff(c_167, plain, (![A_92, B_93, C_94]: (k1_relset_1(A_92, B_93, C_94)=k1_relat_1(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.90/2.15  tff(c_181, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_72, c_167])).
% 5.90/2.15  tff(c_1169, plain, (![B_257, A_258, C_259]: (k1_xboole_0=B_257 | k1_relset_1(A_258, B_257, C_259)=A_258 | ~v1_funct_2(C_259, A_258, B_257) | ~m1_subset_1(C_259, k1_zfmisc_1(k2_zfmisc_1(A_258, B_257))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.90/2.15  tff(c_1180, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_10')='#skF_7' | ~v1_funct_2('#skF_10', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_72, c_1169])).
% 5.90/2.15  tff(c_1185, plain, (k1_xboole_0='#skF_8' | k1_relat_1('#skF_10')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_181, c_1180])).
% 5.90/2.15  tff(c_1186, plain, (k1_relat_1('#skF_10')='#skF_7'), inference(splitLeft, [status(thm)], [c_1185])).
% 5.90/2.15  tff(c_1932, plain, (![A_342, B_343, D_344]: (r2_hidden('#skF_6'(A_342, B_343, k9_relat_1(A_342, B_343), D_344), k1_relat_1(A_342)) | ~r2_hidden(D_344, k9_relat_1(A_342, B_343)) | ~v1_funct_1(A_342) | ~v1_relat_1(A_342))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.90/2.15  tff(c_1945, plain, (![B_343, D_344]: (r2_hidden('#skF_6'('#skF_10', B_343, k9_relat_1('#skF_10', B_343), D_344), '#skF_7') | ~r2_hidden(D_344, k9_relat_1('#skF_10', B_343)) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_1186, c_1932])).
% 5.90/2.15  tff(c_1952, plain, (![B_345, D_346]: (r2_hidden('#skF_6'('#skF_10', B_345, k9_relat_1('#skF_10', B_345), D_346), '#skF_7') | ~r2_hidden(D_346, k9_relat_1('#skF_10', B_345)))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_76, c_1945])).
% 5.90/2.15  tff(c_68, plain, (![F_74]: (k1_funct_1('#skF_10', F_74)!='#skF_11' | ~r2_hidden(F_74, '#skF_9') | ~r2_hidden(F_74, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.90/2.15  tff(c_1984, plain, (![B_352, D_353]: (k1_funct_1('#skF_10', '#skF_6'('#skF_10', B_352, k9_relat_1('#skF_10', B_352), D_353))!='#skF_11' | ~r2_hidden('#skF_6'('#skF_10', B_352, k9_relat_1('#skF_10', B_352), D_353), '#skF_9') | ~r2_hidden(D_353, k9_relat_1('#skF_10', B_352)))), inference(resolution, [status(thm)], [c_1952, c_68])).
% 5.90/2.15  tff(c_1988, plain, (![D_56]: (k1_funct_1('#skF_10', '#skF_6'('#skF_10', '#skF_9', k9_relat_1('#skF_10', '#skF_9'), D_56))!='#skF_11' | ~r2_hidden(D_56, k9_relat_1('#skF_10', '#skF_9')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_32, c_1984])).
% 5.90/2.15  tff(c_1998, plain, (![D_354]: (k1_funct_1('#skF_10', '#skF_6'('#skF_10', '#skF_9', k9_relat_1('#skF_10', '#skF_9'), D_354))!='#skF_11' | ~r2_hidden(D_354, k9_relat_1('#skF_10', '#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_76, c_1988])).
% 5.90/2.15  tff(c_2002, plain, (![D_56]: (D_56!='#skF_11' | ~r2_hidden(D_56, k9_relat_1('#skF_10', '#skF_9')) | ~r2_hidden(D_56, k9_relat_1('#skF_10', '#skF_9')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1998])).
% 5.90/2.15  tff(c_2005, plain, (~r2_hidden('#skF_11', k9_relat_1('#skF_10', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_76, c_2002])).
% 5.90/2.15  tff(c_342, plain, (![A_133, B_134, C_135, D_136]: (k7_relset_1(A_133, B_134, C_135, D_136)=k9_relat_1(C_135, D_136) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.90/2.15  tff(c_353, plain, (![D_136]: (k7_relset_1('#skF_7', '#skF_8', '#skF_10', D_136)=k9_relat_1('#skF_10', D_136))), inference(resolution, [status(thm)], [c_72, c_342])).
% 5.90/2.15  tff(c_70, plain, (r2_hidden('#skF_11', k7_relset_1('#skF_7', '#skF_8', '#skF_10', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.90/2.15  tff(c_356, plain, (r2_hidden('#skF_11', k9_relat_1('#skF_10', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_353, c_70])).
% 5.90/2.15  tff(c_2007, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2005, c_356])).
% 5.90/2.15  tff(c_2008, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_1185])).
% 5.90/2.15  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.90/2.15  tff(c_2020, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2008, c_6])).
% 5.90/2.15  tff(c_58, plain, (![C_69, A_67]: (k1_xboole_0=C_69 | ~v1_funct_2(C_69, A_67, k1_xboole_0) | k1_xboole_0=A_67 | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.90/2.15  tff(c_2238, plain, (![C_379, A_380]: (C_379='#skF_8' | ~v1_funct_2(C_379, A_380, '#skF_8') | A_380='#skF_8' | ~m1_subset_1(C_379, k1_zfmisc_1(k2_zfmisc_1(A_380, '#skF_8'))))), inference(demodulation, [status(thm), theory('equality')], [c_2008, c_2008, c_2008, c_2008, c_58])).
% 5.90/2.15  tff(c_2249, plain, ('#skF_10'='#skF_8' | ~v1_funct_2('#skF_10', '#skF_7', '#skF_8') | '#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_72, c_2238])).
% 5.90/2.15  tff(c_2254, plain, ('#skF_10'='#skF_8' | '#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2249])).
% 5.90/2.15  tff(c_2255, plain, ('#skF_7'='#skF_8'), inference(splitLeft, [status(thm)], [c_2254])).
% 5.90/2.15  tff(c_12, plain, (![B_6, A_5]: (m1_subset_1(B_6, A_5) | ~v1_xboole_0(B_6) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.90/2.15  tff(c_10, plain, (![B_6, A_5]: (r2_hidden(B_6, A_5) | ~m1_subset_1(B_6, A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.90/2.15  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.90/2.15  tff(c_88, plain, (![F_80]: (k1_funct_1('#skF_10', F_80)!='#skF_11' | ~r2_hidden(F_80, '#skF_9') | ~r2_hidden(F_80, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.90/2.15  tff(c_93, plain, (k1_funct_1('#skF_10', '#skF_1'('#skF_7'))!='#skF_11' | ~r2_hidden('#skF_1'('#skF_7'), '#skF_9') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_4, c_88])).
% 5.90/2.15  tff(c_156, plain, (~r2_hidden('#skF_1'('#skF_7'), '#skF_9')), inference(splitLeft, [status(thm)], [c_93])).
% 5.90/2.15  tff(c_160, plain, (~m1_subset_1('#skF_1'('#skF_7'), '#skF_9') | v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_10, c_156])).
% 5.90/2.15  tff(c_161, plain, (~m1_subset_1('#skF_1'('#skF_7'), '#skF_9')), inference(splitLeft, [status(thm)], [c_160])).
% 5.90/2.15  tff(c_165, plain, (~v1_xboole_0('#skF_1'('#skF_7')) | ~v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_12, c_161])).
% 5.90/2.15  tff(c_166, plain, (~v1_xboole_0('#skF_9')), inference(splitLeft, [status(thm)], [c_165])).
% 5.90/2.15  tff(c_116, plain, (![B_87, A_88]: (r2_hidden(B_87, A_88) | ~m1_subset_1(B_87, A_88) | v1_xboole_0(A_88))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.90/2.15  tff(c_128, plain, (![B_87]: (k1_funct_1('#skF_10', B_87)!='#skF_11' | ~r2_hidden(B_87, '#skF_9') | ~m1_subset_1(B_87, '#skF_7') | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_116, c_68])).
% 5.90/2.15  tff(c_190, plain, (![B_97]: (k1_funct_1('#skF_10', B_97)!='#skF_11' | ~r2_hidden(B_97, '#skF_9') | ~m1_subset_1(B_97, '#skF_7'))), inference(splitLeft, [status(thm)], [c_128])).
% 5.90/2.15  tff(c_198, plain, (k1_funct_1('#skF_10', '#skF_1'('#skF_9'))!='#skF_11' | ~m1_subset_1('#skF_1'('#skF_9'), '#skF_7') | v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_4, c_190])).
% 5.90/2.15  tff(c_204, plain, (k1_funct_1('#skF_10', '#skF_1'('#skF_9'))!='#skF_11' | ~m1_subset_1('#skF_1'('#skF_9'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_166, c_198])).
% 5.90/2.15  tff(c_205, plain, (~m1_subset_1('#skF_1'('#skF_9'), '#skF_7')), inference(splitLeft, [status(thm)], [c_204])).
% 5.90/2.15  tff(c_209, plain, (~v1_xboole_0('#skF_1'('#skF_9')) | ~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_12, c_205])).
% 5.90/2.15  tff(c_217, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_209])).
% 5.90/2.15  tff(c_2266, plain, (~v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2255, c_217])).
% 5.90/2.15  tff(c_2278, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2020, c_2266])).
% 5.90/2.15  tff(c_2279, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_2254])).
% 5.90/2.15  tff(c_366, plain, (![A_138, B_139, C_140]: (r2_hidden(k4_tarski('#skF_2'(A_138, B_139, C_140), A_138), C_140) | ~r2_hidden(A_138, k9_relat_1(C_140, B_139)) | ~v1_relat_1(C_140))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.90/2.15  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.90/2.15  tff(c_440, plain, (![C_141, A_142, B_143]: (~v1_xboole_0(C_141) | ~r2_hidden(A_142, k9_relat_1(C_141, B_143)) | ~v1_relat_1(C_141))), inference(resolution, [status(thm)], [c_366, c_2])).
% 5.90/2.15  tff(c_443, plain, (~v1_xboole_0('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_356, c_440])).
% 5.90/2.15  tff(c_462, plain, (~v1_xboole_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_443])).
% 5.90/2.15  tff(c_2289, plain, (~v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2279, c_462])).
% 5.90/2.15  tff(c_2306, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2020, c_2289])).
% 5.90/2.15  tff(c_2308, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_209])).
% 5.90/2.15  tff(c_2869, plain, (![B_493, A_494, C_495]: (k1_xboole_0=B_493 | k1_relset_1(A_494, B_493, C_495)=A_494 | ~v1_funct_2(C_495, A_494, B_493) | ~m1_subset_1(C_495, k1_zfmisc_1(k2_zfmisc_1(A_494, B_493))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.90/2.15  tff(c_2880, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_10')='#skF_7' | ~v1_funct_2('#skF_10', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_72, c_2869])).
% 5.90/2.15  tff(c_2885, plain, (k1_xboole_0='#skF_8' | k1_relat_1('#skF_10')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_181, c_2880])).
% 5.90/2.15  tff(c_2886, plain, (k1_relat_1('#skF_10')='#skF_7'), inference(splitLeft, [status(thm)], [c_2885])).
% 5.90/2.15  tff(c_2390, plain, (![A_399, B_400, C_401]: (r2_hidden('#skF_2'(A_399, B_400, C_401), k1_relat_1(C_401)) | ~r2_hidden(A_399, k9_relat_1(C_401, B_400)) | ~v1_relat_1(C_401))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.90/2.15  tff(c_2399, plain, (![C_402, A_403, B_404]: (~v1_xboole_0(k1_relat_1(C_402)) | ~r2_hidden(A_403, k9_relat_1(C_402, B_404)) | ~v1_relat_1(C_402))), inference(resolution, [status(thm)], [c_2390, c_2])).
% 5.90/2.15  tff(c_2414, plain, (![C_402, B_404]: (~v1_xboole_0(k1_relat_1(C_402)) | ~v1_relat_1(C_402) | v1_xboole_0(k9_relat_1(C_402, B_404)))), inference(resolution, [status(thm)], [c_4, c_2399])).
% 5.90/2.15  tff(c_2467, plain, (![A_420, B_421, C_422, D_423]: (k7_relset_1(A_420, B_421, C_422, D_423)=k9_relat_1(C_422, D_423) | ~m1_subset_1(C_422, k1_zfmisc_1(k2_zfmisc_1(A_420, B_421))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.90/2.15  tff(c_2478, plain, (![D_423]: (k7_relset_1('#skF_7', '#skF_8', '#skF_10', D_423)=k9_relat_1('#skF_10', D_423))), inference(resolution, [status(thm)], [c_72, c_2467])).
% 5.90/2.15  tff(c_87, plain, (~v1_xboole_0(k7_relset_1('#skF_7', '#skF_8', '#skF_10', '#skF_9'))), inference(resolution, [status(thm)], [c_70, c_2])).
% 5.90/2.15  tff(c_2519, plain, (~v1_xboole_0(k9_relat_1('#skF_10', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_2478, c_87])).
% 5.90/2.15  tff(c_2532, plain, (~v1_xboole_0(k1_relat_1('#skF_10')) | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_2414, c_2519])).
% 5.90/2.15  tff(c_2538, plain, (~v1_xboole_0(k1_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_2532])).
% 5.90/2.15  tff(c_2887, plain, (~v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2886, c_2538])).
% 5.90/2.15  tff(c_2891, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2308, c_2887])).
% 5.90/2.15  tff(c_2892, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_2885])).
% 5.90/2.15  tff(c_2906, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2892, c_6])).
% 5.90/2.15  tff(c_3041, plain, (![C_513, A_514]: (C_513='#skF_8' | ~v1_funct_2(C_513, A_514, '#skF_8') | A_514='#skF_8' | ~m1_subset_1(C_513, k1_zfmisc_1(k2_zfmisc_1(A_514, '#skF_8'))))), inference(demodulation, [status(thm), theory('equality')], [c_2892, c_2892, c_2892, c_2892, c_58])).
% 5.90/2.15  tff(c_3052, plain, ('#skF_10'='#skF_8' | ~v1_funct_2('#skF_10', '#skF_7', '#skF_8') | '#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_72, c_3041])).
% 5.90/2.15  tff(c_3057, plain, ('#skF_10'='#skF_8' | '#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_3052])).
% 5.90/2.15  tff(c_3058, plain, ('#skF_7'='#skF_8'), inference(splitLeft, [status(thm)], [c_3057])).
% 5.90/2.15  tff(c_2893, plain, (k1_relat_1('#skF_10')!='#skF_7'), inference(splitRight, [status(thm)], [c_2885])).
% 5.90/2.15  tff(c_3140, plain, (k1_relat_1('#skF_10')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_3058, c_2893])).
% 5.90/2.15  tff(c_3159, plain, (v1_funct_2('#skF_10', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_3058, c_74])).
% 5.90/2.15  tff(c_3153, plain, (k1_relset_1('#skF_8', '#skF_8', '#skF_10')=k1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_3058, c_181])).
% 5.90/2.15  tff(c_3158, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_3058, c_72])).
% 5.90/2.15  tff(c_64, plain, (![B_68, C_69]: (k1_relset_1(k1_xboole_0, B_68, C_69)=k1_xboole_0 | ~v1_funct_2(C_69, k1_xboole_0, B_68) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_68))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.90/2.15  tff(c_3384, plain, (![B_532, C_533]: (k1_relset_1('#skF_8', B_532, C_533)='#skF_8' | ~v1_funct_2(C_533, '#skF_8', B_532) | ~m1_subset_1(C_533, k1_zfmisc_1(k2_zfmisc_1('#skF_8', B_532))))), inference(demodulation, [status(thm), theory('equality')], [c_2892, c_2892, c_2892, c_2892, c_64])).
% 5.90/2.15  tff(c_3387, plain, (k1_relset_1('#skF_8', '#skF_8', '#skF_10')='#skF_8' | ~v1_funct_2('#skF_10', '#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_3158, c_3384])).
% 5.90/2.15  tff(c_3398, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_3159, c_3153, c_3387])).
% 5.90/2.15  tff(c_3400, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3140, c_3398])).
% 5.90/2.15  tff(c_3401, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_3057])).
% 5.90/2.15  tff(c_2520, plain, (r2_hidden('#skF_11', k9_relat_1('#skF_10', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_2478, c_70])).
% 5.90/2.15  tff(c_2479, plain, (![A_424, B_425, C_426]: (r2_hidden(k4_tarski('#skF_2'(A_424, B_425, C_426), A_424), C_426) | ~r2_hidden(A_424, k9_relat_1(C_426, B_425)) | ~v1_relat_1(C_426))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.90/2.15  tff(c_2575, plain, (![C_428, A_429, B_430]: (~v1_xboole_0(C_428) | ~r2_hidden(A_429, k9_relat_1(C_428, B_430)) | ~v1_relat_1(C_428))), inference(resolution, [status(thm)], [c_2479, c_2])).
% 5.90/2.15  tff(c_2578, plain, (~v1_xboole_0('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_2520, c_2575])).
% 5.90/2.15  tff(c_2597, plain, (~v1_xboole_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_2578])).
% 5.90/2.15  tff(c_3408, plain, (~v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_3401, c_2597])).
% 5.90/2.15  tff(c_3427, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2906, c_3408])).
% 5.90/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.90/2.15  
% 5.90/2.15  Inference rules
% 5.90/2.15  ----------------------
% 5.90/2.15  #Ref     : 0
% 5.90/2.15  #Sup     : 657
% 5.90/2.15  #Fact    : 0
% 5.90/2.15  #Define  : 0
% 5.90/2.15  #Split   : 23
% 5.90/2.15  #Chain   : 0
% 5.90/2.15  #Close   : 0
% 5.90/2.15  
% 5.90/2.15  Ordering : KBO
% 5.90/2.15  
% 5.90/2.15  Simplification rules
% 5.90/2.15  ----------------------
% 5.90/2.15  #Subsume      : 141
% 5.90/2.15  #Demod        : 374
% 5.90/2.15  #Tautology    : 45
% 5.90/2.15  #SimpNegUnit  : 40
% 5.90/2.15  #BackRed      : 170
% 5.90/2.15  
% 5.90/2.15  #Partial instantiations: 0
% 5.90/2.15  #Strategies tried      : 1
% 5.90/2.15  
% 5.90/2.15  Timing (in seconds)
% 5.90/2.15  ----------------------
% 5.90/2.15  Preprocessing        : 0.35
% 5.90/2.16  Parsing              : 0.17
% 5.90/2.16  CNF conversion       : 0.03
% 5.90/2.16  Main loop            : 1.03
% 5.90/2.16  Inferencing          : 0.36
% 5.90/2.16  Reduction            : 0.27
% 5.90/2.16  Demodulation         : 0.18
% 5.90/2.16  BG Simplification    : 0.05
% 5.90/2.16  Subsumption          : 0.26
% 5.90/2.16  Abstraction          : 0.05
% 5.90/2.16  MUC search           : 0.00
% 5.90/2.16  Cooper               : 0.00
% 5.90/2.16  Total                : 1.43
% 5.90/2.16  Index Insertion      : 0.00
% 5.90/2.16  Index Deletion       : 0.00
% 5.90/2.16  Index Matching       : 0.00
% 5.90/2.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
